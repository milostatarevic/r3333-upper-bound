import PricingG.UUTFivePosition
namespace R4333.UUTD9DegreeTransport
open ProfileDTripleJoinReduction ProfileDRowExtension ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61 ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry
set_option maxHeartbeats 0
theorem normalizeSupportBlockZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFiveSupport .uut 0 selected) :
    colorDegree
        (UUTFivePosition.normalizeSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (UUTFivePosition.k15Representative selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0) (blockVertex 0 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uut selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (UUTFivePosition.k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← UUTFivePosition.selectedPositionPermZero_uut_selected selected,
    Equiv.symm_apply_apply]

theorem normalizeSupportBlockOne_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFiveSupport .uut 1 selected) :
    colorDegree
        (UUTFivePosition.normalizeSupportBlockOne selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1)
        (blockVertex 1 (UUTFivePosition.k15Representative selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1) (blockVertex 1 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermOne .uut selected).symm)
      (blockRootColor 1)
      (blockVertex 1 (UUTFivePosition.k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← UUTFivePosition.selectedPositionPermOne_uut_selected selected,
    Equiv.symm_apply_apply]

theorem normalizeSupportBlockTwo_tailOwnDegree
    (selected : Fin 16)
    (branch : PositionedFiveSupport .uut 2 selected) :
    colorDegree
        (UUTFivePosition.normalizeSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uut selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = _
  rw [colorDegree_relabelVertices]
  rw [← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
    Equiv.symm_apply_apply]


#print axioms normalizeSupportBlockTwo_tailOwnDegree
end R4333.UUTD9DegreeTransport
