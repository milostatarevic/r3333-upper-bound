import R4333Lean.ProfileDDegreeTenMatrixLeafTenDataUUU0P2
import R4333Lean.ProfileDUUUDegreeTenSupportOrbits61

/-!
# Support classification for UUU / block zero / position two / degree ten

For an arbitrary exact matrix branch at selected position two, the two
foreign own-colour neighbourhoods are independent five-sets in the canonical
untwisted K15 and K16 templates.  The checked support-family enumerations
therefore give an actual `Fin 11` and `Fin 16` index.

This is the position-dependent semantic entrance to the otherwise reusable
support and catalogue quotient.  It contains no finite-refutation claim.
-/

namespace R4333
namespace ProfileDUUUDegreeTenSupportClassificationUUU0P2

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDUUUDegreeTenSupportOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0P2.selectedPosition

theorem orderedFiveSupport_card {n : Nat} (support : OrderedFiveSupport n) :
    support.positions.card = 5 := by
  calc
    support.positions.card =
        (Finset.univ : Finset
          ProfileDHighOwnFiveRowSplit61.FiveVertex).card := by
      exact Finset.card_image_of_injective _ support.embedding.injective
    _ = 5 := by simp

theorem firstSupport_templateIndependent
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    IsColorIndependentSet (k15Template false) 1
      coordinates.first.positions := by
  intro left hleft right hright hlr hcolor
  let tail := exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hleftOwn := (exact.firstSupportExact left).mp hleft
  have hrightOwn := (exact.firstSupportExact right).mp hright
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 1 (by decide) left right hlr
  have hedgeOwn :
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1 left.val)
          (ProfileDTripleJoinReduction.blockVertex 1 right.val) = 1 := by
    rw [hedge]
    change SingleRootStarCNF.canonicalPalette 2
      (k15Template false left right) = 1
    rw [hcolor]
    decide
  apply tail.noMono
    (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val)
    (ProfileDTripleJoinReduction.blockVertex 1 left.val)
    (ProfileDTripleJoinReduction.blockVertex 1 right.val)
  · exact ⟨
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 1
        (by decide) SelectedPosition.isLt left.isLt,
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 1
        (by decide) SelectedPosition.isLt right.isLt,
      (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 1).ne hlr⟩
  · exact ⟨hleftOwn.trans hrightOwn.symm,
      hrightOwn.trans hedgeOwn.symm⟩

theorem secondSupport_templateIndependent
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    IsColorIndependentSet (k16Template false) 1
      coordinates.second.positions := by
  intro left hleft right hright hlr hcolor
  let tail := exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hleftOwn := (exact.secondSupportExact left).mp hleft
  have hrightOwn := (exact.secondSupportExact right).mp hright
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
      tail 2 (by decide) left right hlr
  have hedgeOwn :
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 2 left.val)
          (ProfileDTripleJoinReduction.blockVertex 2 right.val) = 1 := by
    rw [hedge]
    change SingleRootStarCNF.canonicalPalette 3
      (k16Template false left right) = 1
    rw [hcolor]
    decide
  apply tail.noMono
    (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val)
    (ProfileDTripleJoinReduction.blockVertex 2 left.val)
    (ProfileDTripleJoinReduction.blockVertex 2 right.val)
  · exact ⟨
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 2
        (by decide) SelectedPosition.isLt left.isLt,
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 2
        (by decide) SelectedPosition.isLt right.isLt,
      (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 2).ne hlr⟩
  · exact ⟨hleftOwn.trans hrightOwn.symm,
      hrightOwn.trans hedgeOwn.symm⟩

theorem exists_firstSupportIndex
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ i : Fin 11, coordinates.first.positions = u15Support i := by
  have hmem : coordinates.first.positions ∈
      CriticalK15PartitionClassification.independentFiveSets false 1 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 1 coordinates.first.positions).2
      ⟨orderedFiveSupport_card coordinates.first,
        firstSupport_templateIndependent exact⟩
  rw [u15SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_secondSupportIndex
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ i : Fin 16, coordinates.second.positions = u16Support i := by
  have hmem : coordinates.second.positions ∈ u16IndependentFiveSets := by
    unfold u16IndependentFiveSets
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, orderedFiveSupport_card coordinates.second⟩
    · exact (colorViolationCount_eq_zero_iff _ _ _).2
        (secondSupport_templateIndependent exact)
  rw [u16SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_supportIndices
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ firstIndex : Fin 11, ∃ secondIndex : Fin 16,
      coordinates.first.positions = u15Support firstIndex ∧
      coordinates.second.positions = u16Support secondIndex := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex exact
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex exact
  exact ⟨firstIndex, secondIndex, hfirst, hsecond⟩

#print axioms firstSupport_templateIndependent
#print axioms secondSupport_templateIndependent
#print axioms exists_supportIndices

end ProfileDUUUDegreeTenSupportClassificationUUU0P2
end R4333
