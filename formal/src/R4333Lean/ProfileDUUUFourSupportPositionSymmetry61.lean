import R4333Lean.ProfileDUUUDegreeTenFiniteBoundary61
import R4333Lean.ProfileDFourSupportRestoredRootK15

/-!
# Selected-position quotient for the UUU four-support branch

The certified UUU tail automorphisms used for the five-support quotient act
only on the tail vertices.  They therefore transport a four-support object
without any relabelling of its five retained rows: the first four rows remain
own-colour rows and the fifth remains outside the own-colour support.

Together with the certified swap of the two equal `K15` blocks, every UUU
four-support object reduces to one of the same four selected indices as in
the five-support branch: block zero at position `0`, `1`, or `2`, or block two
at position `15`.  Exact selected tail own-degree ten and every degree-floor
field are preserved by construction.
-/

namespace R4333
namespace ProfileDUUUFourSupportPositionSymmetry61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUDegreeTenFiniteBoundary61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev TailVertex := ProfileDRowExtension.TailVertex

abbrev SemanticFourSupport :=
  ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension

abbrev DegreeFlooredFiveExtension :=
  ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension

/-! ## A block/position-indexed four-support object -/

structure PositionedFourSupport (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)) where
  toDegreeFlooredFiveExtension : DegreeFlooredFiveExtension kind
  firstFourOwn : ∀ a : Fin 4,
    toDegreeFlooredFiveExtension.toFiveExtension.rows a.castSucc
        (blockVertex block position.val) = blockRootColor block
  fifthNotOwn :
    toDegreeFlooredFiveExtension.toFiveExtension.rows (Fin.last 4)
        (blockVertex block position.val) ≠ blockRootColor block
  tailOwnDegreeEqTen :
    colorDegree
        toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) = 10

def PositionedFourSupport.toSemantic {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : PositionedFourSupport kind block position) :
    SemanticFourSupport kind where
  toDegreeFlooredFiveExtension := branch.toDegreeFlooredFiveExtension
  block := block
  position := position
  firstFourOwn := branch.firstFourOwn
  fifthNotOwn := branch.fifthNotOwn
  tailOwnDegreeEqTen := branch.tailOwnDegreeEqTen

def PositionedFourSupport.ofSemantic {kind : Kind}
    (ext : SemanticFourSupport kind) :
    PositionedFourSupport kind ext.block ext.position where
  toDegreeFlooredFiveExtension := ext.toDegreeFlooredFiveExtension
  firstFourOwn := ext.firstFourOwn
  fifthNotOwn := ext.fifthNotOwn
  tailOwnDegreeEqTen := ext.tailOwnDegreeEqTen

/-! ## Tail-position normalization with the five rows fixed -/

noncomputable def normalizeFourSupportBlockZero (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 0 selected) :
    PositionedFourSupport .uuu 0 (k15Representative selected) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockZero branch.toDegreeFlooredFiveExtension selected
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      ((selectedPositionPermZero .uuu selected).symm
        (blockVertex 0 (k15Representative selected).val)) = _
    rw [← selectedPositionPermZero_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      ((selectedPositionPermZero .uuu selected).symm
        (blockVertex 0 (k15Representative selected).val)) ≠ _
    rw [← selectedPositionPermZero_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uuu selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val) = 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermZero_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeEqTen

theorem normalizeFourSupportBlockZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 0 selected) :
    colorDegree
        (normalizeFourSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (k15Representative selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0) (blockVertex 0 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uuu selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermZero_uuu_selected selected,
    Equiv.symm_apply_apply]

noncomputable def normalizeFourSupportBlockTwo (selected : Fin 16)
    (branch : PositionedFourSupport .uuu 2 selected) :
    PositionedFourSupport .uuu 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockTwo branch.toDegreeFlooredFiveExtension selected
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val)) = _
    rw [← selectedPositionPermTwo_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val)) ≠ _
    rw [← selectedPositionPermTwo_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uuu selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermTwo_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeEqTen

theorem normalizeFourSupportBlockTwo_tailOwnDegree
    (selected : Fin 16)
    (branch : PositionedFourSupport .uuu 2 selected) :
    colorDegree
        (normalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uuu selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply]

@[simp] theorem normalizeFourSupportBlockZero_rows
    (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 0 selected)
    (row : Fin 5) (x : TailVertex) :
    (normalizeFourSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        ((selectedPositionPermZero .uuu selected).symm x) := by
  rfl

@[simp] theorem normalizeFourSupportBlockTwo_rows
    (selected : Fin 16)
    (branch : PositionedFourSupport .uuu 2 selected)
    (row : Fin 5) (x : TailVertex) :
    (normalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        ((selectedPositionPermTwo .uuu selected).symm x) := by
  rfl

theorem normalizeFourSupportBlockZero_rowSupport_card
    (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 0 selected)
    (row : Fin 5) (q : Fin 4) :
    (rowColorSupport
      ((normalizeFourSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row) q).card =
      (rowColorSupport
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row)
        q).card := by
  change (rowColorSupport
      ((transportFiveExtensionByTailPerm
        branch.toDegreeFlooredFiveExtension.toFiveExtension
        (selectedPositionPermZero .uuu selected).symm
        (selectedPositionPermZero_symm_templateCanonical
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
          selected)).rows row) q).card = _
  exact transportFiveExtensionByTailPerm_rowSupport_card
    branch.toDegreeFlooredFiveExtension.toFiveExtension
    (selectedPositionPermZero .uuu selected).symm
    (selectedPositionPermZero_symm_templateCanonical
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail selected)
    row q

theorem normalizeFourSupportBlockTwo_rowSupport_card
    (selected : Fin 16)
    (branch : PositionedFourSupport .uuu 2 selected)
    (row : Fin 5) (q : Fin 4) :
    (rowColorSupport
      ((normalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row) q).card =
      (rowColorSupport
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row)
        q).card := by
  change (rowColorSupport
      ((transportFiveExtensionByTailPerm
        branch.toDegreeFlooredFiveExtension.toFiveExtension
        (selectedPositionPermTwo .uuu selected).symm
        (selectedPositionPermTwo_symm_templateCanonical
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
          selected)).rows row) q).card = _
  exact transportFiveExtensionByTailPerm_rowSupport_card
    branch.toDegreeFlooredFiveExtension.toFiveExtension
    (selectedPositionPermTwo .uuu selected).symm
    (selectedPositionPermTwo_symm_templateCanonical
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail selected)
    row q

/-! ## Swapping block one to block zero -/

noncomputable def swapFourSupportBlockOneToZero (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 1 selected) :
    PositionedFourSupport .uuu 0 (blockOneTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    swapDegreeFlooredUUU branch.toDegreeFlooredFiveExtension
  firstFourOwn := by
    intro row
    change ProfileDFourRowKindSymmetry.hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row.castSucc
        (ProfileDFourRowKindSymmetry.tailVertexPerm .uuu
          (blockVertex 0 (blockOneTargetPosition selected).val))) = _
    rw [tailVertexPerm_uuu_blockOneTarget, branch.firstFourOwn]
    exact hostColorPerm_blockOneRoot
  fifthNotOwn := by
    change ProfileDFourRowKindSymmetry.hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows (Fin.last 4)
        (ProfileDFourRowKindSymmetry.tailVertexPerm .uuu
          (blockVertex 0 (blockOneTargetPosition selected).val))) ≠ _
    rw [tailVertexPerm_uuu_blockOneTarget]
    intro hcolor
    apply branch.fifthNotOwn
    apply ProfileDFourRowKindSymmetry.hostColorPerm.injective
    exact hcolor.trans hostColorPerm_blockOneRoot.symm
  tailOwnDegreeEqTen := by
    change colorDegree
      (mapEdgeColors
        (relabelVertices
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uuu))
        ProfileDFourRowKindSymmetry.hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) = 10
    rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
      hostColorPerm_symm_blockZeroRoot,
      tailVertexPerm_uuu_blockOneTarget]
    exact branch.tailOwnDegreeEqTen

theorem swapFourSupportBlockOneToZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 1 selected) :
    colorDegree
        (swapFourSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (blockOneTargetPosition selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1) (blockVertex 1 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uuu))
        ProfileDFourRowKindSymmetry.hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockZeroRoot,
    tailVertexPerm_uuu_blockOneTarget]

@[simp] theorem swapFourSupportBlockOneToZero_rows
    (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 1 selected)
    (row : Fin 5) (x : TailVertex) :
    (swapFourSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      ProfileDFourRowKindSymmetry.hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uuu x)) := by
  rfl

theorem swapFourSupportBlockOneToZero_rowSupport_card
    (selected : Fin 15)
    (branch : PositionedFourSupport .uuu 1 selected)
    (row : Fin 5) (q : Fin 4) :
    (rowColorSupport
      ((swapFourSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row) q).card =
      (rowColorSupport
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row)
        (ProfileDFourRowKindSymmetry.hostColorPerm.symm q)).card := by
  change (rowColorSupport
      ((swapFiveExtension
        branch.toDegreeFlooredFiveExtension.toFiveExtension).rows row)
        q).card = _
  exact swapped_rowColorSupport_card
    branch.toDegreeFlooredFiveExtension.toFiveExtension row q

/-! ## The four exact representative indices -/

abbrev SelectedIndex :=
  ProfileDUUUFiveSupportPositionSymmetry.SelectedIndex

/-- This is definitionally the same four-slot indexing used by the exact
degree-ten five-support boundary. -/
abbrev representativeIndexBySlot (slot : Fin 4) : SelectedIndex :=
  ProfileDUUUDegreeTenFiniteBoundary61.representativeIndexBySlot slot

theorem representativeIndexBySlot_mem (slot : Fin 4) :
    representativeIndexBySlot slot ∈
      ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives := by
  exact ProfileDUUUDegreeTenFiniteBoundary61.representativeIndexBySlot_mem
    slot

theorem representativeIndices_length :
    ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives.length = 4 :=
  ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives_length

theorem representativeIndices_nodup :
    ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives.Nodup :=
  ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives_nodup

theorem representativeIndexBySlot_injective :
    Function.Injective representativeIndexBySlot := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide

/-- Every member of the old four-element representative list has exactly
one slot in the explicit `Fin 4` indexing. -/
theorem existsUnique_representativeSlot_of_mem
    {index : SelectedIndex}
    (hindex : index ∈
      ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives) :
    ∃! slot : Fin 4, representativeIndexBySlot slot = index := by
  obtain ⟨slot, hslot⟩ :=
    ProfileDUUUDegreeTenFiniteBoundary61.exists_representativeSlot_of_mem
      hindex
  refine ⟨slot, hslot, ?_⟩
  intro other hother
  apply representativeIndexBySlot_injective
  exact hother.trans hslot.symm

/-- Semantic coverage by exactly the same four representative indices as
the five-support quotient. -/
theorem exists_positioned_representative
    (ext : SemanticFourSupport .uuu) :
    ∃ index : SelectedIndex,
      index ∈ ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives ∧
        Nonempty (PositionedFourSupport .uuu index.1 index.2) := by
  cases ext with
  | mk degree block position firstFour fifthNot degreeTen =>
      fin_cases block
      · let source : PositionedFourSupport .uuu 0 position :=
          ⟨degree, firstFour, fifthNot, degreeTen⟩
        let normalized := normalizeFourSupportBlockZero position source
        exact ⟨ProfileDUUUFiveSupportPositionSymmetry.k15Index
            (k15Representative position),
          ProfileDUUUFiveSupportPositionSymmetry.k15Index_representative_mem
            position,
          ⟨normalized⟩⟩
      · let source : PositionedFourSupport .uuu 1 position :=
          ⟨degree, firstFour, fifthNot, degreeTen⟩
        let swapped := swapFourSupportBlockOneToZero position source
        let normalized := normalizeFourSupportBlockZero
          (blockOneTargetPosition position) swapped
        exact ⟨ProfileDUUUFiveSupportPositionSymmetry.k15Index
            (k15Representative (blockOneTargetPosition position)),
          ProfileDUUUFiveSupportPositionSymmetry.k15Index_representative_mem
            (blockOneTargetPosition position),
          ⟨normalized⟩⟩
      · let source : PositionedFourSupport .uuu 2 position :=
          ⟨degree, firstFour, fifthNot, degreeTen⟩
        let normalized := normalizeFourSupportBlockTwo position source
        exact ⟨ProfileDUUUFiveSupportPositionSymmetry.k16Index
            (Fin.last 15),
          ProfileDUUUFiveSupportPositionSymmetry.k16Index_last_mem,
          ⟨normalized⟩⟩

/-- Explicitly indexed semantic representative.  The unique-slot theorem
above shows that the output index is one and only one of the four displayed
indices. -/
theorem exists_indexed_representative
    (ext : SemanticFourSupport .uuu) :
    ∃ slot : Fin 4, Nonempty
      (PositionedFourSupport .uuu
        (representativeIndexBySlot slot).1
        (representativeIndexBySlot slot).2) := by
  obtain ⟨index, hindex, branch⟩ := exists_positioned_representative ext
  obtain ⟨slot, hslot⟩ :=
    ProfileDUUUDegreeTenFiniteBoundary61.exists_representativeSlot_of_mem
      hindex
  subst index
  exact ⟨slot, branch⟩

/-- Coverage packaged with the uniqueness of the representative slot. -/
theorem exists_uniquelySlotted_positioned_representative
    (ext : SemanticFourSupport .uuu) :
    ∃ index : SelectedIndex,
      index ∈ ProfileDUUUFiveSupportPositionSymmetry.uuuRepresentatives ∧
        Nonempty (PositionedFourSupport .uuu index.1 index.2) ∧
        ∃! slot : Fin 4, representativeIndexBySlot slot = index := by
  obtain ⟨index, hindex, branch⟩ := exists_positioned_representative ext
  exact ⟨index, hindex, branch,
    existsUnique_representativeSlot_of_mem hindex⟩

/-! ## Direct handoff to the restored-root K15 catalogue -/

/-- The representative quotient and restored-root semantic entrance compose
without any extra hypothesis. -/
theorem exists_indexed_catalogued_representative
    (ext : SemanticFourSupport .uuu) :
    ∃ slot : Fin 4,
      ∃ branch : PositionedFourSupport .uuu
          (representativeIndexBySlot slot).1
          (representativeIndexBySlot slot).2,
        ∃ enumerations :
            ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
              branch.toSemantic,
          ∃ twisted : Bool, Nonempty
            (WeakColorEquiv
              (ProfileDFourSupportRestoredRootK15.restoredRootDecodedK15
                enumerations)
              (k15Template twisted)) := by
  obtain ⟨slot, ⟨branch⟩⟩ := exists_indexed_representative ext
  obtain ⟨enumerations, twisted, equivalence⟩ :=
    ProfileDFourSupportRestoredRootK15.exists_catalogued_restoredRootK15
      branch.toSemantic
  exact ⟨slot, branch, enumerations, twisted, equivalence⟩

#print axioms normalizeFourSupportBlockZero
#print axioms normalizeFourSupportBlockTwo
#print axioms swapFourSupportBlockOneToZero
#print axioms exists_positioned_representative
#print axioms exists_indexed_representative
#print axioms exists_uniquelySlotted_positioned_representative
#print axioms exists_indexed_catalogued_representative

end ProfileDUUUFourSupportPositionSymmetry61
end R4333
