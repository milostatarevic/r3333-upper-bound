import R4333Lean.ProfileDFourRowStrategicRestriction
import R4333Lean.ProfileDBlockZeroSupportShadows
import R4333Lean.ProfileDToBFreeCompletionTransfer

/-!
# Dual own-colour incidence in a full profile-D extension

View the fourteen free-to-tail rows by columns.  A tail vertex in block `b`
has own omitted-root colour `b+1`.  In either other critical block its
neighbours of that colour form an independent set in the corresponding
critical template, hence there are at most five.  Its total degree in that
colour is at least eleven in the non-root `K60`, while its own block
contributes zero.  Consequently every one of the 46 tail vertices has an
own-colour neighbour in the free `K14`.

Double counting gives at least 46 such incidences across the fourteen free
rows, so one free row has at least four.  The final theorem retains that row
as row zero of a degree-floored four-row restriction.  No SAT conclusion or
certificate is asserted.
-/

namespace R4333
namespace ProfileDColumnOwnColorIncidence61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDFourRowDegreeCap
open ProfileDRowSupportBounds61

set_option maxRecDepth 1000000

def blockRootColor (block : Fin 3) : Fin 4 := Fin.succ block

@[simp] theorem blockRootColor_ne_zero (block : Fin 3) :
    blockRootColor block ≠ 0 := by
  fin_cases block <;> decide

theorem blockVertex_ne_of_block_ne (source target : Fin 3)
    (hne : source ≠ target) {i j : Nat}
    (hi : i < blockSize source) (hj : j < blockSize target) :
    blockVertex source i ≠ blockVertex target j := by
  intro hvertices
  have hval := congrArg Fin.val hvertices
  rw [blockVertex_val source hi, blockVertex_val target hj] at hval
  fin_cases source <;> fin_cases target <;>
    simp_all [ProfileDTripleJoinReduction.blockStart,
      ProfileDTripleJoinReduction.blockSize] <;> omega

theorem blockVertex_fixed_injective (block : Fin 3) :
    Function.Injective
      (fun i : Fin (blockSize block) => blockVertex block i.val) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  rw [blockVertex_val block i.isLt, blockVertex_val block j.isLt] at hval
  omega

@[simp] theorem tailRootColor_blockVertex (block : Fin 3)
    (i : Fin (blockSize block)) :
    tailRootColor (blockVertex block i.val) = blockRootColor block := by
  fin_cases block <;>
    simp [tailRootColor, blockRootColor,
      ProfileDTripleJoinReduction.blockVertex_val,
      ProfileDTripleJoinReduction.blockStart,
      ProfileDTripleJoinReduction.blockSize] <;> omega

theorem exists_template_label (target source : Fin 3)
    (hne : source ≠ target) :
    ∃ q : ThreeColor,
      canonicalPalette (blockRootColor target) q = blockRootColor source := by
  fin_cases target <;> fin_cases source <;>
    simp_all [blockRootColor, canonicalPalette] <;> decide

/-! ## The self-deleted tail row and its block decomposition -/

def ownNeighborRow {kind : Kind} (ext : Extension kind)
    (block : Fin 3) (i : Fin (blockSize block)) : TailVertex → Fin 4 :=
  fun y =>
    if y = blockVertex block i.val then 0
    else ext.tail.coloring (blockVertex block i.val) y

theorem ownNeighborRow_support_eq_colorNeighborhood {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block)) :
    rowColorSupport (ownNeighborRow ext block i) (blockRootColor block) =
      colorNeighborhood ext.tail.coloring (blockRootColor block)
        (blockVertex block i.val) := by
  ext y
  simp only [mem_rowColorSupport, mem_colorNeighborhood]
  constructor
  · intro hy
    have hyne : y ≠ blockVertex block i.val := by
      intro heq
      subst y
      have hyzero : (0 : Fin 4) = blockRootColor block := by
        simpa [ownNeighborRow] using hy
      exact (blockRootColor_ne_zero block) hyzero.symm
    exact ⟨hyne, by simpa [ownNeighborRow, hyne] using hy⟩
  · rintro ⟨hyne, hycolor⟩
    simpa [ownNeighborRow, hyne] using hycolor

theorem support_card_eq_block_sum (row : TailVertex → Fin 4) (q : Fin 4) :
    (rowColorSupport row q).card =
      (rowColorSupport (ProfileDBlockZeroSupport.k15Row row 0) q).card +
        ((rowColorSupport (ProfileDBlockZeroSupport.k15Row row 1) q).card +
          (rowColorSupport (ProfileDBlockZeroSupport.k16Row row) q).card) := by
  let splitRow : (Fin 15 ⊕ Fin 15) ⊕ Fin 16 → Fin 4 :=
    row ∘ ProfileDFourRowKindSymmetry.tailDecompEquiv
  calc
    (rowColorSupport row q).card =
        (rowColorSupport splitRow q).card :=
      (ProfileDBlockZeroSupport.rowColorSupport_card_comp_equiv
        ProfileDFourRowKindSymmetry.tailDecompEquiv row q).symm
    _ = (rowColorSupport
          (fun p : Fin 15 ⊕ Fin 15 => splitRow (.inl p)) q).card +
        (rowColorSupport (fun p : Fin 16 => splitRow (.inr p)) q).card := by
      rw [ProfileDBlockZeroSupport.rowColorSupport_card_sum]
    _ = ((rowColorSupport
          (ProfileDBlockZeroSupport.k15Row row 0) q).card +
          (rowColorSupport
            (ProfileDBlockZeroSupport.k15Row row 1) q).card) +
        (rowColorSupport
          (ProfileDBlockZeroSupport.k16Row row) q).card := by
      rw [ProfileDBlockZeroSupport.rowColorSupport_card_sum]
      congr 1
    _ = (rowColorSupport
          (ProfileDBlockZeroSupport.k15Row row 0) q).card +
        ((rowColorSupport
          (ProfileDBlockZeroSupport.k15Row row 1) q).card +
          (rowColorSupport
            (ProfileDBlockZeroSupport.k16Row row) q).card) := by omega

/-! ## At most five own-colour neighbours in either other block -/

theorem k15_otherBlock_support_independent {kind : Kind}
    (ext : Extension kind) (source : Fin 3)
    (i : Fin (blockSize source)) (which : Fin 2)
    (hne : source ≠ ProfileDBlockZeroSupport.k15Block which) :
    ∃ q : ThreeColor,
      IsColorIndependentSet
        (k15Template
          (kind.twisted (ProfileDBlockZeroSupport.k15Block which))) q
        (rowColorSupport
          (ProfileDBlockZeroSupport.k15Row
            (ownNeighborRow ext source i) which)
          (blockRootColor source)) := by
  let target := ProfileDBlockZeroSupport.k15Block which
  obtain ⟨q, hpalette⟩ := exists_template_label target source hne
  refine ⟨q, ?_⟩
  intro x hx y hy hxy htemplate
  have hsx : blockVertex source i.val ≠ blockVertex target x.val :=
    blockVertex_ne_of_block_ne source target hne i.isLt (by
      simp [target, ProfileDBlockZeroSupport.blockSize_k15Block])
  have hsy : blockVertex source i.val ≠ blockVertex target y.val :=
    blockVertex_ne_of_block_ne source target hne i.isLt (by
      simp [target, ProfileDBlockZeroSupport.blockSize_k15Block])
  have hxcolor :
      ext.tail.coloring (blockVertex source i.val)
          (blockVertex target x.val) = blockRootColor source := by
    have hx' := (mem_rowColorSupport _ _ x).mp hx
    simpa [ProfileDBlockZeroSupport.k15Row, ownNeighborRow, target,
      hsx.symm] using hx'
  have hycolor :
      ext.tail.coloring (blockVertex source i.val)
          (blockVertex target y.val) = blockRootColor source := by
    have hy' := (mem_rowColorSupport _ _ y).mp hy
    simpa [ProfileDBlockZeroSupport.k15Row, ownNeighborRow, target,
      hsy.symm] using hy'
  have htarget :
      ext.tail.coloring (blockVertex target x.val)
          (blockVertex target y.val) =
        canonicalPalette (blockRootColor target)
          (k15Template (kind.twisted target) x y) := by
    simpa [target, blockRootColor] using
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        ext.tail target (ProfileDBlockZeroSupport.blockSize_k15Block which)
        x y hxy
  apply ext.tail.noMono (blockVertex source i.val)
      (blockVertex target x.val) (blockVertex target y.val)
  · have hxyVertices :
        blockVertex target x.val ≠ blockVertex target y.val := by
      intro hvertices
      apply hxy
      apply Fin.ext
      have hval := congrArg Fin.val hvertices
      rw [blockVertex_val target (by
          simp [target, ProfileDBlockZeroSupport.blockSize_k15Block]),
        blockVertex_val target (by
          simp [target, ProfileDBlockZeroSupport.blockSize_k15Block])] at hval
      omega
    exact ⟨hsx, hsy, hxyVertices⟩
  · constructor
    · exact hxcolor.trans hycolor.symm
    · calc
        ext.tail.coloring (blockVertex source i.val)
            (blockVertex target y.val) = blockRootColor source := hycolor
        _ = canonicalPalette (blockRootColor target) q := hpalette.symm
        _ = canonicalPalette (blockRootColor target)
            (k15Template (kind.twisted target) x y) :=
          congrArg (canonicalPalette (blockRootColor target)) htemplate.symm
        _ = ext.tail.coloring (blockVertex target x.val)
            (blockVertex target y.val) := htarget.symm

theorem k15_otherBlock_support_le_five {kind : Kind}
    (ext : Extension kind) (source : Fin 3)
    (i : Fin (blockSize source)) (which : Fin 2)
    (hne : source ≠ ProfileDBlockZeroSupport.k15Block which) :
    (rowColorSupport
      (ProfileDBlockZeroSupport.k15Row
        (ownNeighborRow ext source i) which)
      (blockRootColor source)).card ≤ 5 := by
  obtain ⟨q, hq⟩ :=
    k15_otherBlock_support_independent ext source i which hne
  exact K15PairEndpointBound.k15Template_independent_card_le_five
    (kind.twisted (ProfileDBlockZeroSupport.k15Block which)) q _ hq

theorem k16_otherBlock_support_independent {kind : Kind}
    (ext : Extension kind) (source : Fin 3)
    (i : Fin (blockSize source)) (hne : source ≠ 2) :
    ∃ q : ThreeColor,
      IsColorIndependentSet (k16Template (kind.twisted 2)) q
        (rowColorSupport
          (ProfileDBlockZeroSupport.k16Row
            (ownNeighborRow ext source i))
          (blockRootColor source)) := by
  obtain ⟨q, hpalette⟩ := exists_template_label 2 source hne
  refine ⟨q, ?_⟩
  intro x hx y hy hxy htemplate
  have hsx : blockVertex source i.val ≠ blockVertex 2 x.val :=
    blockVertex_ne_of_block_ne source 2 hne i.isLt (by
      simp [ProfileDTripleJoinReduction.blockSize])
  have hsy : blockVertex source i.val ≠ blockVertex 2 y.val :=
    blockVertex_ne_of_block_ne source 2 hne i.isLt (by
      simp [ProfileDTripleJoinReduction.blockSize])
  have hxcolor :
      ext.tail.coloring (blockVertex source i.val) (blockVertex 2 x.val) =
        blockRootColor source := by
    have hx' := (mem_rowColorSupport _ _ x).mp hx
    simpa [ProfileDBlockZeroSupport.k16Row, ownNeighborRow, hsx.symm] using hx'
  have hycolor :
      ext.tail.coloring (blockVertex source i.val) (blockVertex 2 y.val) =
        blockRootColor source := by
    have hy' := (mem_rowColorSupport _ _ y).mp hy
    simpa [ProfileDBlockZeroSupport.k16Row, ownNeighborRow, hsy.symm] using hy'
  have htarget :
      ext.tail.coloring (blockVertex 2 x.val) (blockVertex 2 y.val) =
        canonicalPalette (blockRootColor 2)
          (k16Template (kind.twisted 2) x y) := by
    simpa [blockRootColor] using
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        ext.tail 2 (by rfl) x y hxy
  apply ext.tail.noMono (blockVertex source i.val)
      (blockVertex 2 x.val) (blockVertex 2 y.val)
  · have hxyVertices : blockVertex 2 x.val ≠ blockVertex 2 y.val := by
      intro hvertices
      apply hxy
      apply Fin.ext
      have hval := congrArg Fin.val hvertices
      rw [blockVertex_val 2 (by
          simp [ProfileDTripleJoinReduction.blockSize]),
        blockVertex_val 2 (by
          simp [ProfileDTripleJoinReduction.blockSize])] at hval
      omega
    exact ⟨hsx, hsy, hxyVertices⟩
  · constructor
    · exact hxcolor.trans hycolor.symm
    · calc
        ext.tail.coloring (blockVertex source i.val)
            (blockVertex 2 y.val) = blockRootColor source := hycolor
        _ = canonicalPalette (blockRootColor 2) q := hpalette.symm
        _ = canonicalPalette (blockRootColor 2)
            (k16Template (kind.twisted 2) x y) :=
          congrArg (canonicalPalette (blockRootColor 2)) htemplate.symm
        _ = ext.tail.coloring (blockVertex 2 x.val)
            (blockVertex 2 y.val) := htarget.symm

theorem k16_otherBlock_support_le_five {kind : Kind}
    (ext : Extension kind) (source : Fin 3)
    (i : Fin (blockSize source)) (hne : source ≠ 2) :
    (rowColorSupport
      (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext source i))
      (blockRootColor source)).card ≤ 5 := by
  obtain ⟨q, hq⟩ := k16_otherBlock_support_independent ext source i hne
  have hgood : NoMonochromaticTriangle (k16Template (kind.twisted 2)) := by
    cases htwisted : kind.twisted 2 <;>
      simp [k16Template, k16Untwisted_good, k16Twisted_good]
  exact threeColor_independent_card_le_five_at_16
    (k16Template (kind.twisted 2)) hgood q _ hq

/-! ## The own block contributes zero -/

theorem ownBlock_support_eq_zero {kind : Kind} (ext : Extension kind)
    (source : Fin 3) (i : Fin (blockSize source)) :
    (rowColorSupport
      (fun j : Fin (blockSize source) =>
        ownNeighborRow ext source i (blockVertex source j.val))
      (blockRootColor source)).card = 0 := by
  rw [Finset.card_eq_zero]
  by_contra hne
  have hnonempty : (rowColorSupport
      (fun j : Fin (blockSize source) =>
        ownNeighborRow ext source i (blockVertex source j.val))
      (blockRootColor source)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨j, hj⟩ := hnonempty
  have hjcolor := (mem_rowColorSupport _ _ j).mp hj
  by_cases hji : j = i
  · subst j
    have hjzero : (0 : Fin 4) = blockRootColor source := by
      simpa [ownNeighborRow] using hjcolor
    exact (blockRootColor_ne_zero source) hjzero.symm
  · have hvertices : blockVertex source j.val ≠ blockVertex source i.val :=
      (blockVertex_fixed_injective source).ne hji
    have hforbidden := tail_rootForbidden (restrictFour ext)
      (blockVertex source i.val) (blockVertex source j.val)
      hvertices.symm (by simp)
    have hforbidden' : ext.tail.coloring (blockVertex source i.val)
        (blockVertex source j.val) ≠ blockRootColor source := by
      simpa [restrictFour] using hforbidden
    apply hforbidden'
    simpa [ownNeighborRow, hvertices] using hjcolor

/-! ## Global degree floor and the forced free incidence -/

theorem fullJoinedColorDegree_ge_eleven {kind : Kind}
    (ext : Extension kind) (q : Fin 4) (v : FullJoinedVertex) :
    11 ≤ colorDegree (fullJoinedColoring ext) q v := by
  have hsum := sum_colorDegree_eq_card_sub_one (fullJoinedColoring ext) v
  have h0 := fullJoinedColorDegree_le_sixteen ext 0 v
  have h1 := fullJoinedColorDegree_le_sixteen ext 1 v
  have h2 := fullJoinedColorDegree_le_sixteen ext 2 v
  have h3 := fullJoinedColorDegree_le_sixteen ext 3 v
  have hcard : Fintype.card FullJoinedVertex = 60 := by decide
  have hsum' :
      colorDegree (fullJoinedColoring ext) 0 v +
        (colorDegree (fullJoinedColoring ext) 1 v +
          (colorDegree (fullJoinedColoring ext) 2 v +
            colorDegree (fullJoinedColoring ext) 3 v)) = 59 := by
    simpa [Fin.sum_univ_succ, hcard] using hsum
  fin_cases q
  · change 11 ≤ colorDegree (fullJoinedColoring ext) 0 v
    omega
  · change 11 ≤ colorDegree (fullJoinedColoring ext) 1 v
    omega
  · change 11 ≤ colorDegree (fullJoinedColoring ext) 2 v
    omega
  · change 11 ≤ colorDegree (fullJoinedColoring ext) 3 v
    omega

theorem colorDegree_joinColoring_inr
    {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (q : C) (x : B) :
    colorDegree (joinColoring inside base rows) q (.inr x) =
      (rowColorSupport (fun a => rows a x) q).card +
        colorDegree base q x := by
  classical
  have hneighborhood :
      colorNeighborhood (joinColoring inside base rows) q (.inr x) =
        (rowColorSupport (fun a => rows a x) q).disjSum
          (colorNeighborhood base q x) := by
    ext y
    cases y with
    | inl a => simp [colorNeighborhood, rowColorSupport, joinColoring]
    | inr y => simp [colorNeighborhood, rowColorSupport, joinColoring]
  rw [colorDegree, hneighborhood, Finset.card_disjSum]
  rfl

def freeOwnColorSupport {kind : Kind} (ext : Extension kind)
    (block : Fin 3) (i : Fin (blockSize block)) : Finset FreeVertex :=
  rowColorSupport
    (fun a => ext.rows a (blockVertex block i.val)) (blockRootColor block)

theorem every_block_tail_vertex_has_free_ownColor_neighbor {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block)) :
    1 ≤ (freeOwnColorSupport ext block i).card := by
  have hdegree := fullJoinedColorDegree_ge_eleven ext (blockRootColor block)
    (.inr (blockVertex block i.val))
  change 11 ≤ colorDegree
    (joinColoring ext.inside ext.tail.coloring ext.rows)
      (blockRootColor block) (.inr (blockVertex block i.val)) at hdegree
  rw [colorDegree_joinColoring_inr] at hdegree
  have htailDegree :
      colorDegree ext.tail.coloring (blockRootColor block)
          (blockVertex block i.val) =
        (rowColorSupport (ownNeighborRow ext block i)
          (blockRootColor block)).card := by
    rw [ownNeighborRow_support_eq_colorNeighborhood]
    rfl
  rw [htailDegree, support_card_eq_block_sum] at hdegree
  change 1 ≤ (rowColorSupport
    (fun a => ext.rows a (blockVertex block i.val))
      (blockRootColor block)).card
  fin_cases block
  · have hown := ownBlock_support_eq_zero ext 0 i
    have hother1 := k15_otherBlock_support_le_five ext 0 i 1 (by decide)
    have hother2 := k16_otherBlock_support_le_five ext 0 i (by decide)
    have hrowEq :
        ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 0 =
          fun j : Fin 15 =>
            ownNeighborRow ext 0 i (blockVertex 0 j.val) := by
      funext j
      rfl
    have hown' : (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 0)
          (blockRootColor 0)).card = 0 := by
      rw [hrowEq]
      exact hown
    change 11 ≤ (freeOwnColorSupport ext 0 i).card +
      ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 0)
          (blockRootColor 0)).card +
       ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 1)
          (blockRootColor 0)).card +
        (rowColorSupport
          (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 0 i))
          (blockRootColor 0)).card)) at hdegree
    change 1 ≤ (freeOwnColorSupport ext 0 i).card
    omega
  · have hother0 := k15_otherBlock_support_le_five ext 1 i 0 (by decide)
    have hown := ownBlock_support_eq_zero ext 1 i
    have hother2 := k16_otherBlock_support_le_five ext 1 i (by decide)
    have hrowEq :
        ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 1 =
          fun j : Fin 15 =>
            ownNeighborRow ext 1 i (blockVertex 1 j.val) := by
      funext j
      rfl
    have hown' : (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 1)
          (blockRootColor 1)).card = 0 := by
      rw [hrowEq]
      exact hown
    change 11 ≤ (freeOwnColorSupport ext 1 i).card +
      ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 0)
          (blockRootColor 1)).card +
       ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 1)
          (blockRootColor 1)).card +
        (rowColorSupport
          (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 1 i))
          (blockRootColor 1)).card)) at hdegree
    change 1 ≤ (freeOwnColorSupport ext 1 i).card
    omega
  · have hother0 := k15_otherBlock_support_le_five ext 2 i 0 (by decide)
    have hother1 := k15_otherBlock_support_le_five ext 2 i 1 (by decide)
    have hown := ownBlock_support_eq_zero ext 2 i
    have hrowEq :
        ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 2 i) =
          fun j : Fin 16 =>
            ownNeighborRow ext 2 i (blockVertex 2 j.val) := by
      rfl
    have hown' : (rowColorSupport
        (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 2 i))
          (blockRootColor 2)).card = 0 := by
      rw [hrowEq]
      exact hown
    change 11 ≤ (freeOwnColorSupport ext 2 i).card +
      ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 2 i) 0)
          (blockRootColor 2)).card +
       ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 2 i) 1)
          (blockRootColor 2)).card +
        (rowColorSupport
          (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 2 i))
          (blockRootColor 2)).card)) at hdegree
    change 1 ≤ (freeOwnColorSupport ext 2 i).card
    omega

/-! ## Exact column-to-row double counting -/

def columnOwnColorIncidences {kind : Kind} (ext : Extension kind)
    (x : TailVertex) : Finset FreeVertex :=
  rowColorSupport (fun a => ext.rows a x) (tailRootColor x)

def rowOwnColorIncidences {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) : Finset TailVertex :=
  (Finset.univ : Finset TailVertex).filter fun x =>
    ext.rows a x = tailRootColor x

theorem every_tail_vertex_has_free_ownColor_neighbor {kind : Kind}
    (ext : Extension kind) (x : TailVertex) :
    1 ≤ (columnOwnColorIncidences ext x).card := by
  generalize hcoord : ProfileDFourRowKindSymmetry.tailDecompEquiv.symm x = coord
  have hx : x = ProfileDFourRowKindSymmetry.tailDecompEquiv coord := by
    have := congrArg ProfileDFourRowKindSymmetry.tailDecompEquiv hcoord
    simpa using this
  cases coord with
  | inl pair =>
      cases pair with
      | inl i =>
          rw [hx, ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero]
          simpa [columnOwnColorIncidences, freeOwnColorSupport] using
            every_block_tail_vertex_has_free_ownColor_neighbor ext 0 i
      | inr i =>
          rw [hx, ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne]
          simpa [columnOwnColorIncidences, freeOwnColorSupport] using
            every_block_tail_vertex_has_free_ownColor_neighbor ext 1 i
  | inr i =>
      rw [hx, ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo]
      simpa [columnOwnColorIncidences, freeOwnColorSupport] using
        every_block_tail_vertex_has_free_ownColor_neighbor ext 2 i

theorem column_row_double_count {kind : Kind} (ext : Extension kind) :
    (∑ x : TailVertex, (columnOwnColorIncidences ext x).card) =
      ∑ a : FreeVertex, (rowOwnColorIncidences ext a).card := by
  classical
  simp only [columnOwnColorIncidences, rowOwnColorIncidences,
    rowColorSupport, Finset.card_filter]
  rw [Finset.sum_comm]

theorem total_row_ownColor_incidences_ge_fortySix {kind : Kind}
    (ext : Extension kind) :
    46 ≤ ∑ a : FreeVertex, (rowOwnColorIncidences ext a).card := by
  rw [← column_row_double_count]
  calc
    46 = ∑ _x : TailVertex, 1 := by simp [TailVertex]
    _ ≤ ∑ x : TailVertex, (columnOwnColorIncidences ext x).card :=
      Finset.sum_le_sum fun x _ =>
        every_tail_vertex_has_free_ownColor_neighbor ext x

theorem exists_row_with_four_ownColor_incidences {kind : Kind}
    (ext : Extension kind) :
    ∃ a : FreeVertex, 4 ≤ (rowOwnColorIncidences ext a).card := by
  by_contra hnone
  have hupper :
      (∑ a : FreeVertex, (rowOwnColorIncidences ext a).card) ≤
        ∑ _a : FreeVertex, 3 := by
    exact Finset.sum_le_sum fun a _ => by
      have hnot : ¬4 ≤ (rowOwnColorIncidences ext a).card := by
        intro hfour
        exact hnone ⟨a, hfour⟩
      omega
  have hconstant : (∑ _a : FreeVertex, 3) = 42 := by
    simp [FreeVertex]
  have hlower := total_row_ownColor_incidences_ge_fortySix ext
  omega

/-- If a separate argument supplies the conjectured rowwise lower bound
three, the 46-incidence count leaves at least four incidences above that
uniform baseline.  The premise is explicit: the present B-transfer proves
only the two K15 hits below. -/
theorem total_excess_above_three_ge_four {kind : Kind}
    (ext : Extension kind)
    (hthree : ∀ a : FreeVertex,
      3 ≤ (rowOwnColorIncidences ext a).card) :
    4 ≤ ∑ a : FreeVertex,
      ((rowOwnColorIncidences ext a).card - 3) := by
  have hdecomp :
      (∑ a : FreeVertex, (rowOwnColorIncidences ext a).card) =
        ∑ a : FreeVertex,
          (3 + ((rowOwnColorIncidences ext a).card - 3)) := by
    apply Finset.sum_congr rfl
    intro a _ha
    have ha := hthree a
    omega
  rw [Finset.sum_add_distrib] at hdecomp
  have hconstant : (∑ _a : FreeVertex, 3) = 42 := by
    simp [FreeVertex]
  have hlower := total_row_ownColor_incidences_ge_fortySix ext
  omega

/-! ## What the existing B obstruction actually supplies rowwise -/

theorem every_full_row_hits_bothK15_of_B_obstruction
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : Kind} (ext : Extension kind) (a : FreeVertex) :
    (∃ i : Fin 15, ext.rows a (blockVertex 0 i.val) = 1) ∧
      ∃ i : Fin 15, ext.rows a (blockVertex 1 i.val) = 2 := by
  let restricted :=
    ProfileDFourRowStrategicRestriction.restrictFourAt ext a
  obtain ⟨first, hfirst⟩ :=
    ProfileDToBFreeCompletionTransfer.every_free_row_hits_firstK15_of_B_obstruction
      hB restricted 0
  obtain ⟨second, hsecond⟩ :=
    ProfileDToBFreeCompletionTransfer.every_free_row_hits_secondK15_of_B_obstruction
      hB restricted 0
  constructor
  · exact ⟨first, by simpa [restricted] using hfirst⟩
  · exact ⟨second, by simpa [restricted] using hsecond⟩

theorem every_full_row_has_two_ownColor_incidences_of_B_obstruction
    (hB : ProfileBThreeRowBoundary.UniversalThreeRowObstruction)
    {kind : Kind} (ext : Extension kind) (a : FreeVertex) :
    2 ≤ (rowOwnColorIncidences ext a).card := by
  obtain ⟨⟨first, hfirst⟩, ⟨second, hsecond⟩⟩ :=
    every_full_row_hits_bothK15_of_B_obstruction hB ext a
  let x0 : TailVertex := blockVertex 0 first.val
  let x1 : TailVertex := blockVertex 1 second.val
  have hx0 : x0 ∈ rowOwnColorIncidences ext a := by
    simp [x0, rowOwnColorIncidences, tailRootColor_blockVertex,
      blockRootColor, hfirst]
  have hx1 : x1 ∈ rowOwnColorIncidences ext a := by
    simp [x1, rowOwnColorIncidences, tailRootColor_blockVertex,
      blockRootColor, hsecond]
  have hne : x0 ≠ x1 := by
    exact blockVertex_ne_of_block_ne 0 1 (by decide)
      (by simp [ProfileDTripleJoinReduction.blockSize])
      (by simp [ProfileDTripleJoinReduction.blockSize])
  let pair : Finset TailVertex := {x0, x1}
  have hsubset : pair ⊆ rowOwnColorIncidences ext a := by
    intro x hx
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hx0
    · exact hx1
  calc
    2 = pair.card := by simp [pair, hne]
    _ ≤ (rowOwnColorIncidences ext a).card := Finset.card_le_card hsubset

/-! ## Preserve the strategic row in the checked four-row boundary -/

def fourRowOwnColorIncidences {kind : Kind} (ext : FourExtension kind)
    (a : FourVertex) : Finset TailVertex :=
  (Finset.univ : Finset TailVertex).filter fun x =>
    ext.rows a x = tailRootColor x

/-- A native degree-floored profile-D object whose row zero retains at least
four tail-own-colour incidences. -/
structure StrategicDegreeFlooredFourExtension (kind : Kind) : Type where
  toDegreeFlooredFourExtension : DegreeFlooredFourExtension kind
  rowZeroOwnColorIncidencesLower :
    4 ≤ (fourRowOwnColorIncidences
      toDegreeFlooredFourExtension.toFourExtension 0).card

theorem exists_strategicDegreeFlooredFourExtension {kind : Kind}
    (ext : Extension kind) :
    Nonempty (StrategicDegreeFlooredFourExtension kind) := by
  obtain ⟨selected, hselected⟩ :=
    exists_row_with_four_ownColor_incidences ext
  let restricted :=
    ProfileDFourRowStrategicRestriction.restrictDegreeFlooredFourAt ext selected
  refine ⟨{
    toDegreeFlooredFourExtension := restricted
    rowZeroOwnColorIncidencesLower := ?_
  }⟩
  simpa [fourRowOwnColorIncidences, rowOwnColorIncidences, restricted,
    ProfileDFourRowStrategicRestriction.restrictDegreeFlooredFourAt,
    ProfileDFourRowStrategicRestriction.restrictDegreeFlooredFourWith,
    ProfileDFourRowStrategicRestriction.restrictFourWith] using hselected

#print axioms R4333.ProfileDColumnOwnColorIncidence61.every_block_tail_vertex_has_free_ownColor_neighbor
#print axioms R4333.ProfileDColumnOwnColorIncidence61.every_tail_vertex_has_free_ownColor_neighbor
#print axioms R4333.ProfileDColumnOwnColorIncidence61.column_row_double_count
#print axioms R4333.ProfileDColumnOwnColorIncidence61.total_row_ownColor_incidences_ge_fortySix
#print axioms R4333.ProfileDColumnOwnColorIncidence61.exists_row_with_four_ownColor_incidences
#print axioms R4333.ProfileDColumnOwnColorIncidence61.total_excess_above_three_ge_four
#print axioms R4333.ProfileDColumnOwnColorIncidence61.every_full_row_has_two_ownColor_incidences_of_B_obstruction
#print axioms R4333.ProfileDColumnOwnColorIncidence61.exists_strategicDegreeFlooredFourExtension

end ProfileDColumnOwnColorIncidence61
end R4333
