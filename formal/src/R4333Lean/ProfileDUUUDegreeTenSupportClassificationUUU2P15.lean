import R4333Lean.ProfileDDegreeTenMatrixLeafDataUUU2P15
import R4333Lean.ProfileDUUUDegreeTenSupportOrbitsB2P15

/-!
# Support classification for UUU / block two / position fifteen / degree ten

For an arbitrary exact matrix branch at the final position of block two, the
two foreign own-color neighborhoods are independent five-sets of template
color two in the two canonical untwisted K15 blocks.  The checked finite
enumeration gives two `Fin 11` indices; checked strong automorphisms then send
them independently to the nine ordered pairs over representatives `0,1,4`.

This is a semantic entrance and support-orbit theorem.  It makes no matrix
catalogue completeness or finite-refutation claim.
-/

namespace R4333
namespace ProfileDUUUDegreeTenSupportClassificationUUU2P15

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDUUUDegreeTenSupportOrbits61
open ProfileDUUUDegreeTenSupportOrbitsB2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition

theorem orderedFiveSupport_card {n : Nat} (support : OrderedFiveSupport n) :
    support.positions.card = 5 := by
  calc
    support.positions.card =
        (Finset.univ : Finset
          ProfileDHighOwnFiveRowSplit61.FiveVertex).card := by
      exact Finset.card_image_of_injective _ support.embedding.injective
    _ = 5 := by simp

theorem firstSupport_templateIndependent
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    IsColorIndependentSet (k15Template false) 2
      coordinates.first.positions := by
  intro left hleft right hright hlr hcolor
  let tail := exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hleftOwn := (exact.firstSupportExact left).mp hleft
  have hrightOwn := (exact.firstSupportExact right).mp hright
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 0 (by decide) left right hlr
  have hedgeOwn :
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 0 left.val)
          (ProfileDTripleJoinReduction.blockVertex 0 right.val) = 3 := by
    rw [hedge]
    change SingleRootStarCNF.canonicalPalette 1
      (k15Template false left right) = 3
    rw [hcolor]
    decide
  apply tail.noMono
    (ProfileDTripleJoinReduction.blockVertex 2 SelectedPosition.val)
    (ProfileDTripleJoinReduction.blockVertex 0 left.val)
    (ProfileDTripleJoinReduction.blockVertex 0 right.val)
  · exact ⟨
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 2 0
        (by decide) SelectedPosition.isLt left.isLt,
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 2 0
        (by decide) SelectedPosition.isLt right.isLt,
      (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 0).ne hlr⟩
  · exact ⟨hleftOwn.trans hrightOwn.symm,
      hrightOwn.trans hedgeOwn.symm⟩

theorem secondSupport_templateIndependent
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    IsColorIndependentSet (k15Template false) 2
      coordinates.second.positions := by
  intro left hleft right hright hlr hcolor
  let tail := exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hleftOwn := (exact.secondSupportExact left).mp hleft
  have hrightOwn := (exact.secondSupportExact right).mp hright
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 1 (by decide) left right hlr
  have hedgeOwn :
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1 left.val)
          (ProfileDTripleJoinReduction.blockVertex 1 right.val) = 3 := by
    rw [hedge]
    change SingleRootStarCNF.canonicalPalette 2
      (k15Template false left right) = 3
    rw [hcolor]
    decide
  apply tail.noMono
    (ProfileDTripleJoinReduction.blockVertex 2 SelectedPosition.val)
    (ProfileDTripleJoinReduction.blockVertex 1 left.val)
    (ProfileDTripleJoinReduction.blockVertex 1 right.val)
  · exact ⟨
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 2 1
        (by decide) SelectedPosition.isLt left.isLt,
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 2 1
        (by decide) SelectedPosition.isLt right.isLt,
      (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 1).ne hlr⟩
  · exact ⟨hleftOwn.trans hrightOwn.symm,
      hrightOwn.trans hedgeOwn.symm⟩

theorem exists_firstSupportIndex
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∃ i : Fin 11, coordinates.first.positions = q2Support i := by
  have hmem : coordinates.first.positions ∈
      CriticalK15PartitionClassification.independentFiveSets false 2 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 2 coordinates.first.positions).2
      ⟨orderedFiveSupport_card coordinates.first,
        firstSupport_templateIndependent exact⟩
  rw [q2SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_secondSupportIndex
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∃ i : Fin 11, coordinates.second.positions = q2Support i := by
  have hmem : coordinates.second.positions ∈
      CriticalK15PartitionClassification.independentFiveSets false 2 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 2 coordinates.second.positions).2
      ⟨orderedFiveSupport_card coordinates.second,
        secondSupport_templateIndependent exact⟩
  rw [q2SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_supportIndices
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∃ firstIndex secondIndex : Fin 11,
      coordinates.first.positions = q2Support firstIndex ∧
      coordinates.second.positions = q2Support secondIndex := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex exact
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex exact
  exact ⟨firstIndex, secondIndex, hfirst, hsecond⟩

structure NormalizedSupportPair
    (coordinates : MatrixCoordinates 2) where
  firstIndex : Fin 11
  secondIndex : Fin 11
  firstRepresentative : Fin 11
  secondRepresentative : Fin 11
  firstRepresentative_mem :
    firstRepresentative ∈ ({0, 1, 4} : Finset (Fin 11))
  secondRepresentative_mem :
    secondRepresentative ∈ ({0, 1, 4} : Finset (Fin 11))
  firstEquiv : StrongTemplateAutomorphism 15 (k15Template false)
  secondEquiv : StrongTemplateAutomorphism 15 (k15Template false)
  firstExact : coordinates.first.positions = q2Support firstIndex
  secondExact : coordinates.second.positions = q2Support secondIndex
  firstNormalized :
    coordinates.first.positions.image firstEquiv.vertex =
      q2Support firstRepresentative
  secondNormalized :
    coordinates.second.positions.image secondEquiv.vertex =
      q2Support secondRepresentative

theorem exists_normalizedSupportPair
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    Nonempty (NormalizedSupportPair coordinates) := by
  obtain ⟨firstIndex, secondIndex, hfirst, hsecond⟩ :=
    exists_supportIndices exact
  obtain ⟨firstRepresentative, hfirstRepresentative,
      secondRepresentative, hsecondRepresentative,
      firstEquiv, secondEquiv, hfirstImage, hsecondImage⟩ :=
    exists_q2_strong_support_pair_normalization firstIndex secondIndex
  refine ⟨{
    firstIndex := firstIndex
    secondIndex := secondIndex
    firstRepresentative := firstRepresentative
    secondRepresentative := secondRepresentative
    firstRepresentative_mem := hfirstRepresentative
    secondRepresentative_mem := hsecondRepresentative
    firstEquiv := firstEquiv
    secondEquiv := secondEquiv
    firstExact := hfirst
    secondExact := hsecond
    firstNormalized := ?_
    secondNormalized := ?_ }⟩
  · rw [hfirst]
    exact hfirstImage
  · rw [hsecond]
    exact hsecondImage

def dataRepresentativeOfIndex (i : Fin 11) :
    ProfileDDegreeTenMatrixLeafDataUUU2P15.SupportRepresentative :=
  if i = 0 then .s0 else if i = 1 then .s1 else .s4

theorem dataSupport_eq_q2Support_of_representative
    (i : Fin 11) (hi : i ∈ ({0, 1, 4} : Finset (Fin 11))) :
    (ProfileDDegreeTenMatrixLeafDataUUU2P15.support
      (dataRepresentativeOfIndex i)).positions = q2Support i := by
  fin_cases i <;> simp_all [dataRepresentativeOfIndex] <;> decide

theorem normalizedSupportPair_lands_in_data
    {coordinates : MatrixCoordinates 2}
    (normalized : NormalizedSupportPair coordinates) :
    coordinates.first.positions.image normalized.firstEquiv.vertex =
        (ProfileDDegreeTenMatrixLeafDataUUU2P15.support
          (dataRepresentativeOfIndex normalized.firstRepresentative)).positions ∧
      coordinates.second.positions.image normalized.secondEquiv.vertex =
        (ProfileDDegreeTenMatrixLeafDataUUU2P15.support
          (dataRepresentativeOfIndex normalized.secondRepresentative)).positions := by
  constructor
  · rw [normalized.firstNormalized,
      dataSupport_eq_q2Support_of_representative _
        normalized.firstRepresentative_mem]
  · rw [normalized.secondNormalized,
      dataSupport_eq_q2Support_of_representative _
        normalized.secondRepresentative_mem]

#print axioms firstSupport_templateIndependent
#print axioms secondSupport_templateIndependent
#print axioms exists_supportIndices
#print axioms exists_normalizedSupportPair
#print axioms normalizedSupportPair_lands_in_data

end ProfileDUUUDegreeTenSupportClassificationUUU2P15
end R4333
