import R4333Lean.ProfileDRowSupportBounds61
import R4333Lean.K15PairEndpointBound

/-!
# Blockwise colour-zero support and shadows forced in profile D

Every degree-floored profile-D row uses colour zero at least eleven times on
the `K15 + K15 + K16` tail.  Colour zero occurs in the internal palette of
all three critical blocks.  Row admissibility therefore makes its support
inside each block an independent set in the local colour-zero graph, of
order at most five.

It follows that every block is hit, every pair of blocks contains at least
six zero entries, and a saturated block has the unique completion shadow
provided by the critical-template shadow laws.  These are semantic
consequences of the native degree floor; no SAT result is used.
-/

namespace R4333
namespace ProfileDBlockZeroSupport

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDRowSupportBounds61

set_option maxRecDepth 1000000

/-! ## Restricted rows and the exact block partition -/

def k15Block (which : Fin 2) : Fin 3 :=
  ⟨which.val, by omega⟩

@[simp] theorem blockSize_k15Block (which : Fin 2) :
    blockSize (k15Block which) = 15 := by
  fin_cases which <;> rfl

def k15Row (row : TailVertex → Fin 4) (which : Fin 2) :
    Fin 15 → Fin 4 :=
  fun i ↦ row (blockVertex (k15Block which) i.val)

def k16Row (row : TailVertex → Fin 4) : Fin 16 → Fin 4 :=
  fun i ↦ row (blockVertex 2 i.val)

theorem rowColorSupport_card_comp_equiv
    {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (e : A ≃ B) (row : B → C) (q : C) :
    (rowColorSupport (row ∘ e) q).card =
      (rowColorSupport row q).card := by
  have hset :
      (rowColorSupport (row ∘ e) q).image e =
        rowColorSupport row q := by
    ext y
    simp only [Finset.mem_image, mem_rowColorSupport]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simpa using hy
  rw [← hset, Finset.card_image_of_injective _ e.injective]

theorem rowColorSupport_card_sum
    {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (row : A ⊕ B → C) (q : C) :
    (rowColorSupport row q).card =
      (rowColorSupport (fun a ↦ row (.inl a)) q).card +
        (rowColorSupport (fun b ↦ row (.inr b)) q).card := by
  let left :=
    (rowColorSupport (fun a ↦ row (.inl a)) q).image
      (fun a : A ↦ (Sum.inl a : A ⊕ B))
  let right :=
    (rowColorSupport (fun b ↦ row (.inr b)) q).image
      (fun b : B ↦ (Sum.inr b : A ⊕ B))
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxleft hxright
    obtain ⟨a, _ha, hax⟩ := Finset.mem_image.mp hxleft
    obtain ⟨b, _hb, hbx⟩ := Finset.mem_image.mp hxright
    exact Sum.inl_ne_inr (hax.trans hbx.symm)
  have hcover : rowColorSupport row q = left ∪ right := by
    ext x
    cases x with
    | inl a => simp [left, right, rowColorSupport]
    | inr b => simp [left, right, rowColorSupport]
  rw [hcover, Finset.card_union_of_disjoint hdisjoint]
  dsimp only [left, right]
  rw [Finset.card_image_of_injective _ (by
      intro a b h
      exact Sum.inl.inj h),
    Finset.card_image_of_injective _ (by
      intro a b h
      exact Sum.inr.inj h)]

theorem zeroSupport_card_eq_block_sum (row : TailVertex → Fin 4) :
    (rowColorSupport row 0).card =
      (rowColorSupport (k15Row row 0) 0).card +
        ((rowColorSupport (k15Row row 1) 0).card +
          (rowColorSupport (k16Row row) 0).card) := by
  let splitRow : (Fin 15 ⊕ Fin 15) ⊕ Fin 16 → Fin 4 :=
    row ∘ ProfileDFourRowKindSymmetry.tailDecompEquiv
  calc
    (rowColorSupport row 0).card =
        (rowColorSupport splitRow 0).card :=
      (rowColorSupport_card_comp_equiv
        ProfileDFourRowKindSymmetry.tailDecompEquiv row 0).symm
    _ = (rowColorSupport
          (fun p : Fin 15 ⊕ Fin 15 ↦ splitRow (.inl p)) 0).card +
        (rowColorSupport (fun p : Fin 16 ↦ splitRow (.inr p)) 0).card := by
      rw [rowColorSupport_card_sum]
    _ = ((rowColorSupport (k15Row row 0) 0).card +
          (rowColorSupport (k15Row row 1) 0).card) +
        (rowColorSupport (k16Row row) 0).card := by
      rw [rowColorSupport_card_sum]
      congr 1
    _ = (rowColorSupport (k15Row row 0) 0).card +
        ((rowColorSupport (k15Row row 1) 0).card +
          (rowColorSupport (k16Row row) 0).card) := by omega

/-! ## Local independent sets -/

theorem k15_zeroSupport_independent {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (which : Fin 2) :
    IsColorIndependentSet
      (k15Template (kind.twisted (k15Block which))) 0
      (rowColorSupport (k15Row (ext.rows a) which) 0) := by
  intro x hx y hy hxy hcolor
  have hxzero : k15Row (ext.rows a) which x = 0 :=
    (mem_rowColorSupport _ _ _).mp hx
  have hyzero : k15Row (ext.rows a) which y = 0 :=
    (mem_rowColorSupport _ _ _).mp hy
  apply ext.rowsAdmissible a
    (blockVertex (k15Block which) x.val)
    (blockVertex (k15Block which) y.val)
  · intro hvertices
    apply hxy
    have hval := congrArg Fin.val hvertices
    rw [blockVertex_val (k15Block which) (by
        simp),
      blockVertex_val (k15Block which) (by
        simp)] at hval
    exact Fin.ext (by omega)
  · refine ⟨hxzero.trans hyzero.symm, ?_⟩
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        ext.tail (k15Block which) (blockSize_k15Block which) x y hxy
    calc
      k15Row (ext.rows a) which y = 0 := hyzero
      _ = canonicalPalette (Fin.succ (k15Block which)) 0 := by
        fin_cases which <;> decide
      _ = canonicalPalette (Fin.succ (k15Block which))
          (k15Template (kind.twisted (k15Block which)) x y) :=
        congrArg (canonicalPalette (Fin.succ (k15Block which))) hcolor.symm
      _ = ext.tail.coloring
          (blockVertex (k15Block which) x.val)
          (blockVertex (k15Block which) y.val) := hedge.symm

theorem k15_zeroSupport_le_five {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (which : Fin 2) :
    (rowColorSupport (k15Row (ext.rows a) which) 0).card ≤ 5 :=
  K15PairEndpointBound.k15Template_independent_card_le_five
    (kind.twisted (k15Block which)) 0 _
      (k15_zeroSupport_independent ext a which)

theorem k15_zeroSupport_unique_completionShadow {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (which : Fin 2)
    (hfive : (rowColorSupport
      (k15Row (ext.rows a) which) 0).card = 5) :
    ∃! shadow : Fin 16,
      rowColorSupport (k15Row (ext.rows a) which) 0 =
        k15CompletionShadowNeighborhood
          (kind.twisted (k15Block which)) 0 shadow :=
  K15PairEndpointBound.k15Template_maxIndependentSet_unique_completionShadow
    (kind.twisted (k15Block which)) 0 _ hfive
      (k15_zeroSupport_independent ext a which)

theorem k16_zeroSupport_independent {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) :
    IsColorIndependentSet (k16Template (kind.twisted 2)) 0
      (rowColorSupport (k16Row (ext.rows a)) 0) := by
  intro x hx y hy hxy hcolor
  have hxzero : k16Row (ext.rows a) x = 0 :=
    (mem_rowColorSupport _ _ _).mp hx
  have hyzero : k16Row (ext.rows a) y = 0 :=
    (mem_rowColorSupport _ _ _).mp hy
  apply ext.rowsAdmissible a (blockVertex 2 x.val) (blockVertex 2 y.val)
  · intro hvertices
    apply hxy
    have hval := congrArg Fin.val hvertices
    rw [blockVertex_val 2 (by
        simp [ProfileDTripleJoinReduction.blockSize]),
      blockVertex_val 2 (by
        simp [ProfileDTripleJoinReduction.blockSize])] at hval
    exact Fin.ext (by omega)
  · refine ⟨hxzero.trans hyzero.symm, ?_⟩
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        ext.tail 2 (by rfl) x y hxy
    calc
      k16Row (ext.rows a) y = 0 := hyzero
      _ = canonicalPalette 3 0 := by decide
      _ = canonicalPalette 3 (k16Template (kind.twisted 2) x y) :=
        congrArg (canonicalPalette 3) hcolor.symm
      _ = ext.tail.coloring (blockVertex 2 x.val)
          (blockVertex 2 y.val) := hedge.symm

theorem k16_zeroSupport_le_five {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) :
    (rowColorSupport (k16Row (ext.rows a)) 0).card ≤ 5 := by
  have hgood : NoMonochromaticTriangle
      (k16Template (kind.twisted 2)) := by
    cases htwisted : kind.twisted 2 <;>
      simp [k16Template, k16Untwisted_good, k16Twisted_good]
  exact threeColor_independent_card_le_five_at_16
    (k16Template (kind.twisted 2)) hgood 0 _
      (k16_zeroSupport_independent ext a)

theorem k16_zeroSupport_unique_shadow {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex)
    (hfive : (rowColorSupport (k16Row (ext.rows a)) 0).card = 5) :
    ∃! shadow : Fin 16,
      rowColorSupport (k16Row (ext.rows a)) 0 =
        colorNeighborhood (k16Template (kind.twisted 2)) 0 shadow :=
  k16Template_maxIndependentSet_unique_shadow
    (kind.twisted 2) 0 _ hfive (k16_zeroSupport_independent ext a)

/-! ## Global consequences of the native zero-degree floor -/

theorem blockPair_zeroSupport_ge_six {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    6 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 0) 0).card +
        (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 1) 0).card ∧
      6 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 0) 0).card +
        (rowColorSupport
          (k16Row (ext.toFourExtension.rows a)) 0).card ∧
      6 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 1) 0).card +
        (rowColorSupport
          (k16Row (ext.toFourExtension.rows a)) 0).card := by
  have hsum := zeroSupport_card_eq_block_sum
    (ext.toFourExtension.rows a)
  have hlower := ext.zeroSupportLower a
  have h0 := k15_zeroSupport_le_five ext.toFourExtension a 0
  have h1 := k15_zeroSupport_le_five ext.toFourExtension a 1
  have h2 := k16_zeroSupport_le_five ext.toFourExtension a
  omega

theorem every_block_has_zero {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    (∃ i : Fin 15,
      ext.toFourExtension.rows a (blockVertex 0 i.val) = 0) ∧
      (∃ i : Fin 15,
        ext.toFourExtension.rows a (blockVertex 1 i.val) = 0) ∧
      (∃ i : Fin 16,
        ext.toFourExtension.rows a (blockVertex 2 i.val) = 0) := by
  have hpairs := blockPair_zeroSupport_ge_six ext a
  have h0 := k15_zeroSupport_le_five ext.toFourExtension a 0
  have h1 := k15_zeroSupport_le_five ext.toFourExtension a 1
  have h2 := k16_zeroSupport_le_five ext.toFourExtension a
  have hpos0 : 0 < (rowColorSupport
      (k15Row (ext.toFourExtension.rows a) 0) 0).card := by omega
  have hpos1 : 0 < (rowColorSupport
      (k15Row (ext.toFourExtension.rows a) 1) 0).card := by omega
  have hpos2 : 0 < (rowColorSupport
      (k16Row (ext.toFourExtension.rows a)) 0).card := by omega
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hpos0
  obtain ⟨i1, hi1⟩ := Finset.card_pos.mp hpos1
  obtain ⟨i2, hi2⟩ := Finset.card_pos.mp hpos2
  exact ⟨⟨i0, by
      simpa [k15Row, k15Block] using
        (mem_rowColorSupport _ _ i0).mp hi0⟩,
    ⟨⟨i1, by
      simpa [k15Row, k15Block] using
        (mem_rowColorSupport _ _ i1).mp hi1⟩,
      ⟨i2, by
        simpa [k16Row] using
          (mem_rowColorSupport _ _ i2).mp hi2⟩⟩⟩

/-- Every row either has a saturated critical-block zero support, hence a
unique shadow, or has zero support at least four in two distinct blocks. -/
theorem saturated_shadow_or_two_large_blocks {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    (∃ which : Fin 2, ∃ shadow : Fin 16,
      rowColorSupport
          (k15Row (ext.toFourExtension.rows a) which) 0 =
        k15CompletionShadowNeighborhood
          (kind.twisted (k15Block which)) 0 shadow) ∨
    (∃ shadow : Fin 16,
      rowColorSupport (k16Row (ext.toFourExtension.rows a)) 0 =
        colorNeighborhood (k16Template (kind.twisted 2)) 0 shadow) ∨
    ((4 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 0) 0).card ∧
        4 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 1) 0).card) ∨
      (4 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 0) 0).card ∧
        4 ≤ (rowColorSupport
          (k16Row (ext.toFourExtension.rows a)) 0).card) ∨
      (4 ≤ (rowColorSupport
          (k15Row (ext.toFourExtension.rows a) 1) 0).card ∧
        4 ≤ (rowColorSupport
          (k16Row (ext.toFourExtension.rows a)) 0).card)) := by
  let s0 := (rowColorSupport
    (k15Row (ext.toFourExtension.rows a) 0) 0).card
  let s1 := (rowColorSupport
    (k15Row (ext.toFourExtension.rows a) 1) 0).card
  let s2 := (rowColorSupport
    (k16Row (ext.toFourExtension.rows a)) 0).card
  have hsum := zeroSupport_card_eq_block_sum
    (ext.toFourExtension.rows a)
  have hlower := ext.zeroSupportLower a
  have h0 : s0 ≤ 5 := k15_zeroSupport_le_five ext.toFourExtension a 0
  have h1 : s1 ≤ 5 := k15_zeroSupport_le_five ext.toFourExtension a 1
  have h2 : s2 ≤ 5 := k16_zeroSupport_le_five ext.toFourExtension a
  by_cases hs0 : s0 = 5
  · left
    obtain ⟨shadow, hshadow, _⟩ :=
      k15_zeroSupport_unique_completionShadow ext.toFourExtension a 0 hs0
    exact ⟨0, shadow, hshadow⟩
  · by_cases hs1 : s1 = 5
    · left
      obtain ⟨shadow, hshadow, _⟩ :=
        k15_zeroSupport_unique_completionShadow ext.toFourExtension a 1 hs1
      exact ⟨1, shadow, hshadow⟩
    · by_cases hs2 : s2 = 5
      · right; left
        obtain ⟨shadow, hshadow, _⟩ :=
          k16_zeroSupport_unique_shadow ext.toFourExtension a hs2
        exact ⟨shadow, hshadow⟩
      · right; right
        have hsum' : 11 ≤ s0 + (s1 + s2) := by
          rw [← hsum]
          exact hlower
        omega

#print axioms R4333.ProfileDBlockZeroSupport.zeroSupport_card_eq_block_sum
#print axioms R4333.ProfileDBlockZeroSupport.k15_zeroSupport_independent
#print axioms R4333.ProfileDBlockZeroSupport.k15_zeroSupport_unique_completionShadow
#print axioms R4333.ProfileDBlockZeroSupport.k16_zeroSupport_unique_shadow
#print axioms R4333.ProfileDBlockZeroSupport.blockPair_zeroSupport_ge_six
#print axioms R4333.ProfileDBlockZeroSupport.every_block_has_zero
#print axioms R4333.ProfileDBlockZeroSupport.saturated_shadow_or_two_large_blocks

end ProfileDBlockZeroSupport
end R4333
