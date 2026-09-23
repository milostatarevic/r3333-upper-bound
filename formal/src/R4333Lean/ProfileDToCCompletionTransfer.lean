import R4333Lean.ProfileCFourRowKindSymmetry
import R4333Lean.ProfileDFourRowKindSymmetry
import R4333Lean.CriticalTemplateMaximumSetIntersection
import R4333Lean.K15Extension

/-!
# Conditional completion transfer from profile D to profile C

Profile D has tail orders `15+15+16`, whereas profile C has
`14+16+16`.  If one vertex of D's first K15 supplies the missing canonical
completion row of its second K15, that vertex can be moved between the two
blocks.  Deleting it from the first block leaves the arbitrary root-forbidden
K14 permitted by profile C, and adjoining it to the second block creates the
required canonical K16.

This is deliberately conditional: row admissibility alone does not force an
external vertex to omit the target block colour.  The final theorem packages
the useful search cut: after profile C is obstructed, only profile-D objects
with no such completion vertex remain.
-/

namespace R4333
namespace ProfileDToCCompletionTransfer

open SingleRootStarCNF
open ColoringJoinRows

namespace C
abbrev Kind := ProfileCRowExtension.Kind
abbrev TailVertex := ProfileCRowExtension.TailVertex
abbrev TailWitness := ProfileCRowExtension.TailWitness
abbrev ProfileC := ProfileCRowExtension.ProfileC
abbrev blockVertex := ProfileCRowExtension.blockVertex
abbrev SplitTail := ProfileCFourRowKindSymmetry.SplitTail
abbrev FourExtension := ProfileCFourRowBoundary.FourExtension
abbrev UniversalFourRowObstruction :=
  ProfileCFourRowBoundary.UniversalFourRowObstruction
end C

namespace D
abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev TailVertex := Fin 46
abbrev Witness := ProfileDTripleJoinReduction.Witness
abbrev blockVertex := ProfileDTripleJoinReduction.blockVertex
abbrev DCoord := (Fin 15 ⊕ Fin 15) ⊕ Fin 16
abbrev FourExtension := ProfileDFourRowBoundary.FourExtension
abbrev UniversalFourRowObstruction :=
  ProfileDFourRowBoundary.UniversalFourRowObstruction
end D

/-- The profile-C kind keeps D's second-K15 bit and its K16 bit. -/
def toCKind (kind : D.Kind) : C.Kind :=
  ProfileCRowExtension.Kind.ofBooleans
    (kind.twisted 1) (kind.twisted 2)

@[simp] theorem toCKind_twisted_one (kind : D.Kind) :
    (toCKind kind).twisted 1 = kind.twisted 1 := by
  simp [toCKind]

@[simp] theorem toCKind_twisted_two (kind : D.Kind) :
    (toCKind kind).twisted 2 = kind.twisted 2 := by
  simp [toCKind]

/-! ## The exact completion condition -/

/-- A vertex of D's first K15 supplies, with the old second K15, the last
row of its fixed K16 completion. -/
def CompletesSecondK15 {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15) : Prop :=
  ∀ x : Fin 15,
    ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) =
      canonicalPalette 2
        (k16Template (kind.twisted 1) (Fin.last 15) x.castSucc)

def HasSecondK15Completion {kind : D.Kind}
    (ext : D.FourExtension kind) : Prop :=
  ∃ moved : Fin 15, CompletesSecondK15 ext moved

/-- The labeled last row in the fixed K16 completion of a K15 template. -/
def canonicalK15LastRow (twisted : Bool) : Fin 15 → ThreeColor :=
  fun x => k16Template twisted (Fin.last 15) x.castSucc

theorem canonicalK15Extension_eq_k16_offDiagonal (twisted : Bool)
    (u v : Fin 16) (huv : u ≠ v) :
    extendByLast (k15Template twisted) (canonicalK15LastRow twisted) 0 u v =
      k16Template twisted u v := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast v =>
          rw [extendByLast_last_old]
          rfl
  | cast u =>
      induction v using Fin.lastCases with
      | last =>
          rw [extendByLast_old_last,
            (k16Template twisted).color_symm]
          rfl
      | cast v =>
          simp [k15Template_edge_eq_k16Template]

theorem canonicalK15Extension_good (twisted : Bool) :
    NoMonochromaticTriangle
      (extendByLast (k15Template twisted)
        (canonicalK15LastRow twisted) 0) := by
  intro x y z hdistinct hmono
  have hgood : NoMonochromaticTriangle (k16Template twisted) := by
    cases twisted <;> simp [k16Template, k16Untwisted_good,
      k16Twisted_good]
  apply hgood x y z hdistinct
  constructor
  · rw [← canonicalK15Extension_eq_k16_offDiagonal twisted x y
        hdistinct.1,
      ← canonicalK15Extension_eq_k16_offDiagonal twisted x z
        hdistinct.2.1]
    exact hmono.1
  · rw [← canonicalK15Extension_eq_k16_offDiagonal twisted x z
        hdistinct.2.1,
      ← canonicalK15Extension_eq_k16_offDiagonal twisted y z
        hdistinct.2.2]
    exact hmono.2

/-- Place the candidate completion vertex last, after D's second K15. -/
def completionEmbedding (moved : Fin 15) : Fin 16 → D.TailVertex :=
  Fin.lastCases (D.blockVertex 0 moved.val)
    (fun x => D.blockVertex 1 x.val)

theorem completionEmbedding_injective (moved : Fin 15) :
    Function.Injective (completionEmbedding moved) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
      induction y using Fin.lastCases with
      | last => rfl
      | cast y =>
          exfalso
          have hval := congrArg Fin.val hxy
          simp only [completionEmbedding, Fin.lastCases_last,
            Fin.lastCases_castSucc] at hval
          rw [ProfileDTripleJoinReduction.blockVertex_val 0 (by
              simp [ProfileDTripleJoinReduction.blockSize]),
            ProfileDTripleJoinReduction.blockVertex_val 1 y.isLt] at hval
          simp [ProfileDTripleJoinReduction.blockStart] at hval
          omega
  | cast x =>
      induction y using Fin.lastCases with
      | last =>
          exfalso
          have hval := congrArg Fin.val hxy
          simp only [completionEmbedding, Fin.lastCases_castSucc,
            Fin.lastCases_last] at hval
          rw [ProfileDTripleJoinReduction.blockVertex_val 1 x.isLt,
            ProfileDTripleJoinReduction.blockVertex_val 0 (by
              simp [ProfileDTripleJoinReduction.blockSize])] at hval
          simp [ProfileDTripleJoinReduction.blockStart] at hval
          omega
      | cast y =>
          have hxy' : x = y := by
            apply Fin.ext
            have hval := congrArg Fin.val hxy
            simp only [completionEmbedding, Fin.lastCases_castSucc] at hval
            rw [ProfileDTripleJoinReduction.blockVertex_val 1 x.isLt,
              ProfileDTripleJoinReduction.blockVertex_val 1 y.isLt] at hval
            simpa [ProfileDTripleJoinReduction.blockStart] using hval
          exact congrArg Fin.castSucc hxy'

/-- Decode a completion candidate's host-colour row into the local palette
of the second K15. -/
noncomputable def localCompletionRow {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (havoid : ∀ x : Fin 15,
      ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) ≠ 2) :
    Fin 15 → ThreeColor := fun x =>
  (ProfileDFourRowKindSymmetry.canonicalPaletteEquiv 2).symm
    ⟨ext.tail.coloring
      (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val), havoid x⟩

theorem localCompletionRow_encode {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (havoid : ∀ x : Fin 15,
      ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) ≠ 2)
    (x : Fin 15) :
    canonicalPalette 2 (localCompletionRow ext moved havoid x) =
      ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) := by
  have h := congrArg Subtype.val
    ((ProfileDFourRowKindSymmetry.canonicalPaletteEquiv 2).apply_symm_apply
      ⟨ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val), havoid x⟩)
  exact h

theorem completionHost_eq_paletteLocal {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (havoid : ∀ x : Fin 15,
      ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) ≠ 2)
    (u v : Fin 16) (huv : u ≠ v) :
    ext.tail.coloring (completionEmbedding moved u)
        (completionEmbedding moved v) =
      canonicalPalette 2
        (extendByLast (k15Template (kind.twisted 1))
          (localCompletionRow ext moved havoid) 0 u v) := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast v =>
          simp only [completionEmbedding, Fin.lastCases_last,
            Fin.lastCases_castSucc, extendByLast_last_old]
          exact
            (localCompletionRow_encode ext moved havoid v).symm
  | cast u =>
      induction v using Fin.lastCases with
      | last =>
          rw [ext.tail.coloring.color_symm]
          simp only [completionEmbedding, Fin.lastCases_castSucc,
            Fin.lastCases_last, extendByLast_old_last]
          exact
            (localCompletionRow_encode ext moved havoid u).symm
      | cast v =>
          have hne : u ≠ v := by
            intro h
            apply huv
            exact congrArg Fin.castSucc h
          simpa [completionEmbedding] using
            ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
              ext.tail 1 (by decide) u v hne

theorem localCompletionExtension_good {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (havoid : ∀ x : Fin 15,
      ext.tail.coloring
        (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) ≠ 2) :
    NoMonochromaticTriangle
      (extendByLast (k15Template (kind.twisted 1))
        (localCompletionRow ext moved havoid) 0) := by
  intro x y z hdistinct hmono
  apply ext.tail.noMono
    (completionEmbedding moved x)
    (completionEmbedding moved y)
    (completionEmbedding moved z)
  · exact ⟨(completionEmbedding_injective moved).ne hdistinct.1,
      (completionEmbedding_injective moved).ne hdistinct.2.1,
      (completionEmbedding_injective moved).ne hdistinct.2.2⟩
  · constructor
    · rw [completionHost_eq_paletteLocal ext moved havoid x y
          hdistinct.1,
        completionHost_eq_paletteLocal ext moved havoid x z
          hdistinct.2.1]
      exact congrArg (canonicalPalette 2) hmono.1
    · rw [completionHost_eq_paletteLocal ext moved havoid x z
          hdistinct.2.1,
        completionHost_eq_paletteLocal ext moved havoid y z
          hdistinct.2.2]
      exact congrArg (canonicalPalette 2) hmono.2

/-- In an actual triangle-free D tail, avoiding the second block's omitted
colour is equivalent to being its unique canonical completion row. -/
theorem completesSecondK15_iff_avoids {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15) :
    CompletesSecondK15 ext moved ↔
      ∀ x : Fin 15,
        ext.tail.coloring
          (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) ≠ 2 := by
  constructor
  · intro hcompletion x
    rw [hcompletion x]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
  · intro havoid
    have hlocal : localCompletionRow ext moved havoid =
        canonicalK15LastRow (kind.twisted 1) := by
      have hbase : NoMonochromaticTriangle
          (k15Template (kind.twisted 1)) := by
        cases ht : kind.twisted 1 <;>
          simp [k15Template, k15Untwisted_good, k15Twisted_good]
      exact
        (attachment_eq_deficientColor15
          (k15Template (kind.twisted 1)) hbase
          (localCompletionRow ext moved havoid) 0
          (localCompletionExtension_good ext moved havoid)).trans
        (attachment_eq_deficientColor15
          (k15Template (kind.twisted 1)) hbase
          (canonicalK15LastRow (kind.twisted 1)) 0
          (canonicalK15Extension_good (kind.twisted 1))).symm
    intro x
    calc
      ext.tail.coloring
          (D.blockVertex 0 moved.val) (D.blockVertex 1 x.val) =
        canonicalPalette 2 (localCompletionRow ext moved havoid x) :=
          (localCompletionRow_encode ext moved havoid x).symm
      _ = canonicalPalette 2
          (canonicalK15LastRow (kind.twisted 1) x) := by rw [hlocal]
      _ = canonicalPalette 2
          (k16Template (kind.twisted 1) (Fin.last 15) x.castSucc) := rfl

/-! ## Exchanging one tail vertex -/

/-- Merge fourteen retained positions and the moved singleton into the old
first K15. -/
noncomputable def blockZeroMerge (moved : Fin 15) :
    (Fin 14 ⊕ Fin 1) ≃ Fin 15 :=
  (finSumFinEquiv : (Fin 14 ⊕ Fin 1) ≃ Fin 15).trans
    (Equiv.swap (Fin.last 14) moved)

@[simp] theorem blockZeroMerge_moved (moved : Fin 15) :
    blockZeroMerge moved (.inr 0) = moved := by
  change (Equiv.swap (Fin.last 14) moved)
      ((finSumFinEquiv : (Fin 14 ⊕ Fin 1) ≃ Fin 15) (.inr 0)) = moved
  rw [show (finSumFinEquiv : (Fin 14 ⊕ Fin 1) ≃ Fin 15) (.inr 0) =
      Fin.last 14 by
    rw [finSumFinEquiv_apply_right]
    rfl]
  exact Equiv.swap_apply_left (Fin.last 14) moved

@[simp] theorem blockZeroMerge_symm_moved (moved : Fin 15) :
    (blockZeroMerge moved).symm moved = .inr 0 := by
  apply (blockZeroMerge moved).injective
  rw [Equiv.apply_symm_apply, blockZeroMerge_moved]

/-- The new first critical K16 is the old second K15 followed by the moved
vertex. -/
noncomputable def firstCriticalCoordMap (moved : Fin 15) :
    Fin 16 → D.DCoord :=
  Fin.lastCases
    (.inl (.inl (blockZeroMerge moved (.inr 0))))
    (fun x => .inl (.inr x))

@[simp] theorem firstCriticalCoordMap_last (moved : Fin 15) :
    firstCriticalCoordMap moved (Fin.last 15) =
      .inl (.inl moved) := by
  unfold firstCriticalCoordMap
  rw [Fin.lastCases_last, blockZeroMerge_moved]

@[simp] theorem firstCriticalCoordMap_castSucc
    (moved : Fin 15) (x : Fin 15) :
    firstCriticalCoordMap moved x.castSucc = .inl (.inr x) := by
  unfold firstCriticalCoordMap
  exact Fin.lastCases_castSucc x

/-- Reblock C coordinates as D coordinates. -/
noncomputable def tailCoordMap (moved : Fin 15) :
    C.SplitTail → D.DCoord
  | .inl x => .inl (.inl (blockZeroMerge moved (.inl x)))
  | .inr (index, position) =>
      ![firstCriticalCoordMap moved position, (.inr position : D.DCoord)] index

@[simp] theorem tailCoordMap_noncritical (moved : Fin 15)
    (position : Fin 14) :
    tailCoordMap moved (.inl position) =
      .inl (.inl (blockZeroMerge moved (.inl position))) := by
  rfl

@[simp] theorem tailCoordMap_first_last (moved : Fin 15) :
    tailCoordMap moved (.inr ((0 : Fin 2), Fin.last 15)) =
      .inl (.inl moved) := by
  change firstCriticalCoordMap moved (Fin.last 15) = _
  exact firstCriticalCoordMap_last moved

@[simp] theorem tailCoordMap_first_castSucc
    (moved : Fin 15) (position : Fin 15) :
    tailCoordMap moved (.inr ((0 : Fin 2), position.castSucc)) =
      .inl (.inr position) := by
  change firstCriticalCoordMap moved position.castSucc = _
  exact firstCriticalCoordMap_castSucc moved position

@[simp] theorem tailCoordMap_second
    (moved : Fin 15) (position : Fin 16) :
    tailCoordMap moved (.inr ((1 : Fin 2), position)) = .inr position := by
  rfl

/-- A left inverse used only to certify injectivity of `tailCoordMap`. -/
noncomputable def tailCoordUnmap (moved : Fin 15) :
    D.DCoord → C.SplitTail
  | .inl (.inl position) =>
      match (blockZeroMerge moved).symm position with
      | .inl x => .inl x
      | .inr _ => .inr (0, Fin.last 15)
  | .inl (.inr position) => .inr (0, position.castSucc)
  | .inr position => .inr (1, position)

theorem tailCoordUnmap_map (moved : Fin 15) (x : C.SplitTail) :
    tailCoordUnmap moved (tailCoordMap moved x) = x := by
  rcases x with x | ⟨index, position⟩
  · simp [tailCoordMap, tailCoordUnmap]
  · fin_cases index
    · induction position using Fin.lastCases with
      | last =>
          change tailCoordUnmap moved
              (tailCoordMap moved (.inr ((0 : Fin 2), Fin.last 15))) =
            .inr ((0 : Fin 2), Fin.last 15)
          rw [tailCoordMap_first_last]
          simp [tailCoordUnmap]
      | cast position =>
          simp [tailCoordUnmap]
    · simp [tailCoordUnmap]

theorem tailCoordMap_injective (moved : Fin 15) :
    Function.Injective (tailCoordMap moved) :=
  (show Function.LeftInverse (tailCoordUnmap moved) (tailCoordMap moved)
    from tailCoordUnmap_map moved).injective

/-- The concrete tail relabelling from profile-C labels into profile-D
labels. -/
noncomputable def newTailToOldTail (moved : Fin 15) :
    C.TailVertex → D.TailVertex :=
  fun x => ProfileDFourRowKindSymmetry.tailDecompEquiv
    (tailCoordMap moved
      (ProfileCFourRowKindSymmetry.splitTailEquiv.symm x))

theorem newTailToOldTail_injective (moved : Fin 15) :
    Function.Injective (newTailToOldTail moved) := by
  intro x y hxy
  apply ProfileCFourRowKindSymmetry.splitTailEquiv.symm.injective
  apply tailCoordMap_injective moved
  apply ProfileDFourRowKindSymmetry.tailDecompEquiv.injective
  exact hxy

theorem newTail_block_zero (moved : Fin 15) (position : Fin 14) :
    newTailToOldTail moved (C.blockVertex 0 position.val) =
      D.blockVertex 0 (blockZeroMerge moved (.inl position)).val := by
  have hC : ProfileCFourRowKindSymmetry.splitTailEquiv.symm
      (C.blockVertex 0 position.val) = .inl position := by
    apply ProfileCFourRowKindSymmetry.splitTailEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (ProfileCFourRowKindSymmetry.splitTailEquiv_noncritical
      position).symm
  rw [newTailToOldTail, hC]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero _

theorem newTail_block_one_last (moved : Fin 15) :
    newTailToOldTail moved (C.blockVertex 1 (Fin.last 15).val) =
      D.blockVertex 0 moved.val := by
  have hC : ProfileCFourRowKindSymmetry.splitTailEquiv.symm
      (C.blockVertex 1 (Fin.last 15).val) =
        .inr ((0 : Fin 2), Fin.last 15) := by
    apply ProfileCFourRowKindSymmetry.splitTailEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (ProfileCFourRowKindSymmetry.splitTailEquiv_critical
      0 (Fin.last 15)).symm
  rw [newTailToOldTail, hC]
  rw [tailCoordMap_first_last]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero moved

theorem newTail_block_one_castSucc (moved : Fin 15) (position : Fin 15) :
    newTailToOldTail moved (C.blockVertex 1 position.castSucc.val) =
      D.blockVertex 1 position.val := by
  have hC : ProfileCFourRowKindSymmetry.splitTailEquiv.symm
      (C.blockVertex 1 position.castSucc.val) =
        .inr ((0 : Fin 2), position.castSucc) := by
    apply ProfileCFourRowKindSymmetry.splitTailEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (ProfileCFourRowKindSymmetry.splitTailEquiv_critical
      0 position.castSucc).symm
  rw [newTailToOldTail, hC]
  rw [tailCoordMap_first_castSucc]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position

theorem newTail_block_two (moved : Fin 15) (position : Fin 16) :
    newTailToOldTail moved (C.blockVertex 2 position.val) =
      D.blockVertex 2 position.val := by
  have hC : ProfileCFourRowKindSymmetry.splitTailEquiv.symm
      (C.blockVertex 2 position.val) = .inr ((1 : Fin 2), position) := by
    apply ProfileCFourRowKindSymmetry.splitTailEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (ProfileCFourRowKindSymmetry.splitTailEquiv_critical
      1 position).symm
  rw [newTailToOldTail, hC]
  rw [tailCoordMap_second]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position

/-! ## The reblocked profile-C tail -/

noncomputable def newTailColoring {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15) :
    EdgeColoring C.TailVertex (Fin 4) :=
  pullbackColoring ext.tail.coloring (newTailToOldTail moved)

/-- The newly enlarged middle block is exactly the required K16. -/
theorem newTail_block_one_internal {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (hcompletion : CompletesSecondK15 ext moved)
    (left right : Fin 16) (hlr : left ≠ right) :
    newTailColoring ext moved
        (C.blockVertex 1 left.val) (C.blockVertex 1 right.val) =
      canonicalPalette 2
        (k16Template (kind.twisted 1) left right) := by
  induction left using Fin.lastCases with
  | last =>
      induction right using Fin.lastCases with
      | last => exact (hlr rfl).elim
      | cast right =>
          change ext.tail.coloring
              (newTailToOldTail moved
                (C.blockVertex 1 (Fin.last 15).val))
              (newTailToOldTail moved
                (C.blockVertex 1 right.castSucc.val)) = _
          rw [newTail_block_one_last, newTail_block_one_castSucc]
          exact hcompletion right
  | cast left =>
      induction right using Fin.lastCases with
      | last =>
          change ext.tail.coloring
              (newTailToOldTail moved
                (C.blockVertex 1 left.castSucc.val))
              (newTailToOldTail moved
                (C.blockVertex 1 (Fin.last 15).val)) = _
          rw [newTail_block_one_castSucc, newTail_block_one_last]
          calc
            ext.tail.coloring
                (D.blockVertex 1 left.val) (D.blockVertex 0 moved.val) =
              ext.tail.coloring
                (D.blockVertex 0 moved.val) (D.blockVertex 1 left.val) :=
              ext.tail.coloring.color_symm _ _
            _ = canonicalPalette 2
                (k16Template (kind.twisted 1)
                  (Fin.last 15) left.castSucc) := hcompletion left
            _ = canonicalPalette 2
                (k16Template (kind.twisted 1)
                  left.castSucc (Fin.last 15)) := by
              rw [(k16Template (kind.twisted 1)).color_symm]
      | cast right =>
          have hne : left ≠ right := by
            intro h
            apply hlr
            exact congrArg Fin.castSucc h
          change ext.tail.coloring
              (newTailToOldTail moved
                (C.blockVertex 1 left.castSucc.val))
              (newTailToOldTail moved
                (C.blockVertex 1 right.castSucc.val)) = _
          rw [newTail_block_one_castSucc, newTail_block_one_castSucc,
            ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
              ext.tail 1 (by decide) left right hne]
          rw [k15Template_edge_eq_k16Template]
          rfl

theorem newTail_block_two_internal {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (left right : Fin 16) (hlr : left ≠ right) :
    newTailColoring ext moved
        (C.blockVertex 2 left.val) (C.blockVertex 2 right.val) =
      canonicalPalette 3
        (k16Template (kind.twisted 2) left right) := by
  change ext.tail.coloring
      (newTailToOldTail moved (C.blockVertex 2 left.val))
      (newTailToOldTail moved (C.blockVertex 2 right.val)) = _
  rw [newTail_block_two, newTail_block_two,
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
      ext.tail 2 (by decide) left right hlr]
  rfl

theorem newTail_rootForbidden {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (hcompletion : CompletesSecondK15 ext moved) :
    ∀ (block : Fin 3) (left right : Nat),
      left < ProfileCRowExtension.blockSize block →
      right < ProfileCRowExtension.blockSize block → left < right →
      newTailColoring ext moved
          (C.blockVertex block left) (C.blockVertex block right) ≠
        Fin.succ block := by
  intro block left right hleft hright hlr
  fin_cases block
  · simp [ProfileCRowExtension.blockSize] at hleft hright ⊢
    let leftFin : Fin 14 := ⟨left, hleft⟩
    let rightFin : Fin 14 := ⟨right, hright⟩
    let sourceLeft : Fin 15 := blockZeroMerge moved (.inl leftFin)
    let sourceRight : Fin 15 := blockZeroMerge moved (.inl rightFin)
    have hne : sourceLeft ≠ sourceRight :=
      (blockZeroMerge moved).injective.ne (by
        intro h
        exact Fin.ne_of_lt (by simpa [leftFin, rightFin] using hlr)
          (Sum.inl.inj h))
    rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl]
    change ext.tail.coloring
        (newTailToOldTail moved (C.blockVertex 0 leftFin.val))
        (newTailToOldTail moved (C.blockVertex 0 rightFin.val)) ≠ 1
    rw [newTail_block_zero, newTail_block_zero,
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        ext.tail 0 (by decide) sourceLeft sourceRight hne]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 1 _
  · simp [ProfileCRowExtension.blockSize] at hleft hright ⊢
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
      simpa [leftFin, rightFin] using hlr)
    rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
      newTail_block_one_internal ext moved hcompletion leftFin rightFin hne]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
  · simp [ProfileCRowExtension.blockSize] at hleft hright ⊢
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
      simpa [leftFin, rightFin] using hlr)
    rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
      newTail_block_two_internal ext moved leftFin rightFin hne]
    exact SingleRootStarWitness61.canonicalPalette_ne_block 3 _

theorem newTail_templateCanonical {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (hcompletion : CompletesSecondK15 ext moved) :
    ∀ (block : Fin 3), isCriticalBlock C.ProfileC (Fin.succ block) →
      ∀ (left right : Nat),
        left < ProfileCRowExtension.blockSize block →
        right < ProfileCRowExtension.blockSize block → left < right →
        newTailColoring ext moved
            (C.blockVertex block left) (C.blockVertex block right) =
          canonicalPalette (Fin.succ block)
            (templateColor (ProfileCRowExtension.blockSize block)
              ((toCKind kind).twisted block) left right) := by
  intro block hcritical left right hleft hright hlr
  fin_cases block
  · simp [isCriticalBlock, SingleRootStarCNF.blockSize,
      SingleRootStarCNF.profileSizes] at hcritical
  · simp [ProfileCRowExtension.blockSize] at hleft hright ⊢
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
      simpa [leftFin, rightFin] using hlr)
    rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
      newTail_block_one_internal ext moved hcompletion leftFin rightFin hne]
    simp [templateColor, fin16,
      Nat.mod_eq_of_lt leftFin.isLt, Nat.mod_eq_of_lt rightFin.isLt]
  · simp [ProfileCRowExtension.blockSize] at hleft hright ⊢
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := Fin.ne_of_lt (by
      simpa [leftFin, rightFin] using hlr)
    rw [show left = leftFin.val by rfl, show right = rightFin.val by rfl,
      newTail_block_two_internal ext moved leftFin rightFin hne]
    simp [templateColor, fin16,
      Nat.mod_eq_of_lt leftFin.isLt, Nat.mod_eq_of_lt rightFin.isLt]

noncomputable def newTailWitness {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (hcompletion : CompletesSecondK15 ext moved) :
    C.TailWitness (toCKind kind) where
  coloring := newTailColoring ext moved
  noMono := noMono_pullback ext.tail.coloring (newTailToOldTail moved)
    (newTailToOldTail_injective moved) ext.tail.noMono
  rootForbidden := newTail_rootForbidden ext moved hcompletion
  templateCanonical := newTail_templateCanonical ext moved hcompletion

/-! ## Transporting the complete four-row boundary -/

def oldJoined {kind : D.Kind} (ext : D.FourExtension kind) :
    EdgeColoring (Sum (Fin 4) D.TailVertex) (Fin 4) :=
  joinColoring ext.inside ext.tail.coloring ext.rows

theorem oldJoined_noMono {kind : D.Kind} (ext : D.FourExtension kind) :
    NoMonochromaticTriangle (oldJoined ext) :=
  (noMono_joinColoring_iff _ _ _).2
    ⟨ext.insideNoMono, ext.tail.noMono,
      ext.rowsAdmissible, ext.rowsPairCompatible⟩

noncomputable def newRows {kind : D.Kind} (ext : D.FourExtension kind)
    (moved : Fin 15) : Fin 4 → C.TailVertex → Fin 4 :=
  fun a x => ext.rows a (newTailToOldTail moved x)

noncomputable def newSplitToOld (moved : Fin 15) :
    Sum (Fin 4) C.TailVertex → Sum (Fin 4) D.TailVertex
  | .inl a => .inl a
  | .inr x => .inr (newTailToOldTail moved x)

theorem newSplitToOld_injective (moved : Fin 15) :
    Function.Injective (newSplitToOld moved) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Sum.inl.inj hxy)
      | inr y => simp [newSplitToOld] at hxy
  | inr x =>
      cases y with
      | inl y => simp [newSplitToOld] at hxy
      | inr y =>
          exact congrArg Sum.inr
            (newTailToOldTail_injective moved (Sum.inr.inj hxy))

theorem newJoin_eq_pullback {kind : D.Kind} (ext : D.FourExtension kind)
    (moved : Fin 15) :
    joinColoring ext.inside (newTailColoring ext moved)
        (newRows ext moved) =
      pullbackColoring (oldJoined ext) (newSplitToOld moved) := by
  apply EdgeColoring.ext
  funext u v
  cases u with
  | inl u =>
      cases v <;> rfl
  | inr u =>
      cases v with
      | inl v => rfl
      | inr v => rfl

theorem newJoin_noMono {kind : D.Kind} (ext : D.FourExtension kind)
    (moved : Fin 15) :
    NoMonochromaticTriangle
      (joinColoring ext.inside (newTailColoring ext moved)
        (newRows ext moved)) := by
  rw [newJoin_eq_pullback]
  exact noMono_pullback (oldJoined ext) (newSplitToOld moved)
    (newSplitToOld_injective moved) (oldJoined_noMono ext)

noncomputable def transferWith {kind : D.Kind}
    (ext : D.FourExtension kind) (moved : Fin 15)
    (hcompletion : CompletesSecondK15 ext moved) :
    C.FourExtension (toCKind kind) := by
  have hdecomp := (noMono_joinColoring_iff
    ext.inside (newTailColoring ext moved) (newRows ext moved)).1
      (newJoin_noMono ext moved)
  exact {
    tail := newTailWitness ext moved hcompletion
    inside := ext.inside
    rows := newRows ext moved
    insideNoMono := hdecomp.1
    insideRootForbidden := ext.insideRootForbidden
    rowsAdmissible := hdecomp.2.2.1
    rowsPairCompatible := hdecomp.2.2.2
  }

noncomputable def transfer {kind : D.Kind}
    (ext : D.FourExtension kind) (hcompletion : HasSecondK15Completion ext) :
    C.FourExtension (toCKind kind) :=
  transferWith ext (Classical.choose hcompletion)
    (Classical.choose_spec hcompletion)

theorem nonempty_C_of_D_with_completion (kind : D.Kind) :
    Nonempty {ext : D.FourExtension kind // HasSecondK15Completion ext} →
      Nonempty (C.FourExtension (toCKind kind)) := by
  rintro ⟨⟨ext, hcompletion⟩⟩
  exact ⟨transfer ext hcompletion⟩

/-- Once all profile-C objects are obstructed, the profile-D search may
soundly impose that neither K15 contains a vertex completing the other
(the equal-K15 symmetry handles the opposite orientation). -/
theorem universalD_of_C_and_completionFreeD
    (hC : C.UniversalFourRowObstruction)
    (hDfree : ∀ kind : D.Kind,
      ¬Nonempty {ext : D.FourExtension kind //
        ¬HasSecondK15Completion ext}) :
    D.UniversalFourRowObstruction := by
  intro kind
  rintro ⟨ext⟩
  by_cases hcompletion : HasSecondK15Completion ext
  · exact hC (toCKind kind) ⟨transfer ext hcompletion⟩
  · exact hDfree kind ⟨⟨ext, hcompletion⟩⟩

/-! ## Why the completion hypothesis is not automatic -/

/-- The source K15 uses the host palette omitting colour one. -/
def sourceK15Host (twisted : Bool) : EdgeColoring (Fin 15) (Fin 4) where
  color x y := canonicalPalette 1 (k15Template twisted x y)
  color_symm x y := by rw [(k15Template twisted).color_symm]

/-- The target K15 uses the host palette omitting colour two. -/
def targetK15Host (twisted : Bool) : EdgeColoring (Fin 15) (Fin 4) where
  color x y := canonicalPalette 2 (k15Template twisted x y)
  color_symm x y := by rw [(k15Template twisted).color_symm]

/-- Copy the target K15 row off the diagonal, but put the target's omitted
colour on the diagonal.  Thus every source row fails to complete the target
K15 at least once. -/
def blockedCompletionCross (twisted : Bool) (source target : Fin 15) :
    Fin 4 :=
  if source = target then 2
  else targetK15Host twisted source target

theorem sourceK15Host_noMono (twisted : Bool) :
    NoMonochromaticTriangle (sourceK15Host twisted) := by
  intro x y z hdistinct hmono
  have hgood : NoMonochromaticTriangle (k15Template twisted) := by
    cases twisted <;> simp [k15Template, k15Untwisted_good,
      k15Twisted_good]
  apply hgood x y z hdistinct
  exact ⟨SingleRootStarWitness61.canonicalPalette_injective 1 hmono.1,
    SingleRootStarWitness61.canonicalPalette_injective 1 hmono.2⟩

theorem targetK15Host_noMono (twisted : Bool) :
    NoMonochromaticTriangle (targetK15Host twisted) := by
  intro x y z hdistinct hmono
  have hgood : NoMonochromaticTriangle (k15Template twisted) := by
    cases twisted <;> simp [k15Template, k15Untwisted_good,
      k15Twisted_good]
  apply hgood x y z hdistinct
  exact ⟨SingleRootStarWitness61.canonicalPalette_injective 2 hmono.1,
    SingleRootStarWitness61.canonicalPalette_injective 2 hmono.2⟩

theorem blockedCompletionCross_rowAdmissible (twisted : Bool)
    (source : Fin 15) :
    RowAdmissible (targetK15Host twisted)
      (blockedCompletionCross twisted source) := by
  intro x y hxy hbad
  by_cases hx : source = x
  · subst x
    have hy : source ≠ y := by
      intro h
      apply hxy
      exact h
    have htargetNe : targetK15Host twisted source y ≠ 2 := by
      exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
    apply htargetNe
    simpa [blockedCompletionCross, hy] using hbad.1.symm
  by_cases hy : source = y
  · subst y
    have htargetNe : targetK15Host twisted source x ≠ 2 := by
      exact SingleRootStarWitness61.canonicalPalette_ne_block 2 _
    apply htargetNe
    simpa [blockedCompletionCross, hx,
      (targetK15Host twisted).color_symm] using hbad.1
  have hsx : source ≠ x := hx
  have hsy : source ≠ y := hy
  have hdistinct : PairwiseDistinct source x y := ⟨hsx, hsy, hxy⟩
  have hgood := targetK15Host_noMono twisted
  apply hgood source x y hdistinct
  simpa [HomogeneousTriangle, blockedCompletionCross, hx, hy] using hbad

theorem blockedCompletionCross_pairCompatible (twisted : Bool) :
    RowPairCompatible (sourceK15Host twisted)
      (blockedCompletionCross twisted) := by
  intro left right hlr x hbad
  by_cases hxl : x = left
  · subst x
    have hright : right ≠ left := Ne.symm hlr
    have htargetNe : targetK15Host twisted right left ≠ 2 :=
      SingleRootStarWitness61.canonicalPalette_ne_block 2 _
    apply htargetNe
    simpa [blockedCompletionCross, hright] using hbad.2.symm
  by_cases hxr : x = right
  · subst x
    have htargetNe : targetK15Host twisted left right ≠ 2 :=
      SingleRootStarWitness61.canonicalPalette_ne_block 2 _
    apply htargetNe
    simpa [blockedCompletionCross, hlr] using hbad.2
  have hdistinct : PairwiseDistinct left right x :=
    ⟨hlr, fun h => hxl h.symm, fun h => hxr h.symm⟩
  have hlx : left ≠ x := Ne.symm hxl
  have hrx : right ≠ x := Ne.symm hxr
  have hgood := targetK15Host_noMono twisted
  have hnotMono := hgood left right x hdistinct
  generalize hedge : k15Template twisted left right = edge
  generalize hleft : k15Template twisted left x = leftColor
  generalize hright : k15Template twisted right x = rightColor
  fin_cases edge <;> fin_cases leftColor <;> fin_cases rightColor <;>
    simp [sourceK15Host, targetK15Host, blockedCompletionCross,
      canonicalPalette, hlx, hrx, hedge, hleft, hright,
      HomogeneousTriangle] at hbad hnotMono

/-- A fully triangle-free join of two canonical K15 blocks in which every
source vertex has a target-omitted edge.  This rules out an unconditional
two-block completion/exchange theorem based only on triangle compatibility. -/
def blockedCompletionPairColoring (twisted : Bool) :
    EdgeColoring (Fin 15 ⊕ Fin 15) (Fin 4) :=
  joinColoring (sourceK15Host twisted) (targetK15Host twisted)
    (blockedCompletionCross twisted)

theorem blockedCompletionPairColoring_noMono (twisted : Bool) :
    NoMonochromaticTriangle (blockedCompletionPairColoring twisted) := by
  exact (noMono_joinColoring_iff _ _ _).2
    ⟨sourceK15Host_noMono twisted, targetK15Host_noMono twisted,
      blockedCompletionCross_rowAdmissible twisted,
      blockedCompletionCross_pairCompatible twisted⟩

theorem blockedCompletionCross_uses_targetOmitted
    (twisted : Bool) (source : Fin 15) :
    blockedCompletionCross twisted source source = 2 := by
  simp [blockedCompletionCross]

theorem blockedCompletionCross_no_completion
    (twisted : Bool) (source : Fin 15) :
    ¬(∀ target : Fin 15,
      blockedCompletionCross twisted source target =
        canonicalPalette 2
          (k16Template twisted (Fin.last 15) target.castSucc)) := by
  intro h
  have hbad := h source
  rw [blockedCompletionCross_uses_targetOmitted] at hbad
  exact (SingleRootStarWitness61.canonicalPalette_ne_block 2 _)
    hbad.symm

#print axioms R4333.ProfileDToCCompletionTransfer.transfer
#print axioms R4333.ProfileDToCCompletionTransfer.completesSecondK15_iff_avoids
#print axioms R4333.ProfileDToCCompletionTransfer.nonempty_C_of_D_with_completion
#print axioms R4333.ProfileDToCCompletionTransfer.universalD_of_C_and_completionFreeD
#print axioms R4333.ProfileDToCCompletionTransfer.blockedCompletionPairColoring_noMono
#print axioms R4333.ProfileDToCCompletionTransfer.blockedCompletionCross_no_completion

end ProfileDToCCompletionTransfer
end R4333
