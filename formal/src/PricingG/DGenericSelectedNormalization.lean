import R4333Lean.ProfileDUUUFourSupportPositionSymmetry61

namespace PricingG.DGenericSelectedNormalization
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDRowExtension ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61 ProfileDSelectedPositionTransport

/-- The selected Q16 endpoint is normalized to15 for every tail kind, by a
whole-tail vertex permutation preserving all physical palette labels. -/
theorem selected_to_last {kind : ProfileDTripleJoinReduction.Kind} (selected : Fin 16) :
    selectedPositionPermTwo kind selected (blockVertex 2 selected.val) =
      blockVertex 2 (Fin.last 15).val := by
  rw [selectedPositionPermTwo_blockTwo,
    k16TemplateToLastEquiv_apply, k16TemplateToLastMap_deleted]

noncomputable def normalizeDegree {kind : ProfileDTripleJoinReduction.Kind}
    (ext : ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension kind) (selected : Fin 16) :
    ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension kind :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermTwo kind selected).symm
    (selectedPositionPermTwo_symm_templateCanonical ext.toFiveExtension.tail selected)

noncomputable def normalizeFiveSupport {kind : ProfileDTripleJoinReduction.Kind} (selected : Fin 16)
    (branch : PositionedFiveSupport kind 2 selected) :
    PositionedFiveSupport kind 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension :=
    normalizeDegree branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermTwo kind selected).symm
        (blockVertex 2 (Fin.last 15).val)) = _
    rw [← selected_to_last selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo kind selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val)
    rw [colorDegree_relabelVertices,
      ← selected_to_last selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo kind selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selected_to_last selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper


noncomputable def normalizeFourSupport {kind : ProfileDTripleJoinReduction.Kind} (selected : Fin 16)
    (branch : PositionedFourSupport kind 2 selected) :
    PositionedFourSupport kind 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension :=
    normalizeDegree branch.toDegreeFlooredFiveExtension selected
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      ((selectedPositionPermTwo kind selected).symm
        (blockVertex 2 (Fin.last 15).val)) = _
    rw [← selected_to_last selected,
      Equiv.symm_apply_apply]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      ((selectedPositionPermTwo kind selected).symm
        (blockVertex 2 (Fin.last 15).val)) ≠ _
    rw [← selected_to_last selected,
      Equiv.symm_apply_apply]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo kind selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = 10
    rw [colorDegree_relabelVertices,
      ← selected_to_last selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeEqTen


#print axioms normalizeFiveSupport
#print axioms normalizeFourSupport
end PricingG.DGenericSelectedNormalization
