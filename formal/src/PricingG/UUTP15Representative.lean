import PricingG.UUTD10OrbitTransport
import PricingG.UUTP15Rooted
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualCoverage61

/-!
# Semantic entrance to the 372 ordered P15 matrices

This module composes the rooted semantic normalization with the two-stage
factorized finite quotient.  It produces an explicit coordinate equivalence
from every normalized P15 branch to one of the 372 ordered matrices.
-/

namespace R4333
namespace UUTP15Representative

open ProfileDFourSupportRestoredRootK15
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUFourSupportP0OrbitData61
open UUTP15SupportPair
open UUTP15Base
open ProfileDUUUFourSupportP15SemanticCatalogueData61
open ProfileDUUUFourSupportP15SemanticCatalogueFinite61
open ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61
open ProfileDUUUFourSupportP15SemanticCatalogueResidualCoverage61
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open UUTD10OrbitTransport
open UUTP15Rooted

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev RootCase :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.RootCase
abbrev LabelAction :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.LabelAction
abbrev ReducedLabel :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.ReducedLabel
abbrev SupportRepresentative :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.SupportRepresentative
abbrev OrderedLeaf :=
  ProfileDUUUFourSupportP15SwapData61.OrderedLeaf

/-! ## The nine ordered support pairs -/

def supportPairIndex :
    SupportRepresentative → SupportRepresentative → Fin 9
  | .s0, .s0 => 0
  | .s0, .s1 => 1
  | .s0, .s4 => 2
  | .s1, .s0 => 3
  | .s1, .s1 => 4
  | .s1, .s4 => 5
  | .s4, .s0 => 6
  | .s4, .s1 => 7
  | .s4, .s4 => 8

@[simp] theorem pairFirst_supportPairIndex
    (first second : SupportRepresentative) :
    pairFirst (supportPairIndex first second) = first := by
  cases first <;> cases second <;> decide

@[simp] theorem pairSecond_supportPairIndex
    (first second : SupportRepresentative) :
    pairSecond (supportPairIndex first second) = second := by
  cases first <;> cases second <;> decide

/-! ## Raw labelings to the reduced 5-by-5 residual family -/

def stageCoordinate (firstSupport secondSupport : SupportRepresentative)
    (free : FreeLabelAction) (first second : Fin 10)
    (p : Fin 14) : Fin 14 :=
  matrixCoordinateIndex <| match matrixCoordinate p with
  | .inl (.inl position) =>
      .inl (.inl (freeLabelPermutation free position))
  | .inl (.inr position) =>
      .inl (.inr (q2SupportAction firstSupport first position))
  | .inr position =>
      .inr (q2SupportAction secondSupport second position)

noncomputable def freeLabelEquiv (action : FreeLabelAction) :
    Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (freeLabelPermutation action)
    (freeLabelPermutation_bijective action)

noncomputable def stageCoordinateEquiv
    (firstSupport secondSupport : SupportRepresentative)
    (free : FreeLabelAction) (first second : Fin 10) :
    Equiv.Perm (Fin 14) :=
  fourFiveFiveEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (freeLabelEquiv free)
        (q2SupportActionEquiv firstSupport first))
      (q2SupportActionEquiv secondSupport second)).trans fourFiveFiveEquiv)

@[simp] theorem stageCoordinateEquiv_apply
    (firstSupport secondSupport : SupportRepresentative)
    (free : FreeLabelAction) (first second : Fin 10) (p : Fin 14) :
    stageCoordinateEquiv firstSupport secondSupport free first second p =
      stageCoordinate firstSupport secondSupport free first second p := by
  unfold stageCoordinateEquiv stageCoordinate
  simp only [Equiv.trans_apply]
  rw [matrixCoordinate_eq_equiv_symm]
  generalize fourFiveFiveEquiv.symm p = coordinate
  rcases coordinate with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · rw [matrixCoordinateIndex_eq_equiv]
      simp [freeLabelEquiv, q2SupportActionEquiv]
    · rw [matrixCoordinateIndex_eq_equiv]
      simp [freeLabelEquiv, q2SupportActionEquiv]
  · rw [matrixCoordinateIndex_eq_equiv]
    simp [freeLabelEquiv, q2SupportActionEquiv]

theorem candidateVertex_stageOne
    (firstSupport secondSupport : SupportRepresentative)
    (root : RootCase) (free : FreeLabelAction)
    (first second : LabelAction) (p : Fin 14) :
    UUTP15Rooted.candidateVertex
        firstSupport secondSupport root free first second
        (stageCoordinate firstSupport secondSupport
          (freeNormalizerAction free)
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.firstNormalizerAction
            firstSupport root first)
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.secondNormalizerAction
            secondSupport root second) p) =
      reducedCandidateVertex (supportPairIndex firstSupport secondSupport) root
        (firstReducedChoice firstSupport root first)
        (secondReducedChoice secondSupport root second) p := by
  rw [← matrixCoordinateIndex_coordinate p]
  generalize matrixCoordinate p = coordinate
  rcases coordinate with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · simp [UUTP15Rooted.candidateVertex,
        stageCoordinate, reducedCandidateVertex,
        matrixCoordinate_eq_equiv_symm, matrixCoordinateIndex_eq_equiv,
        freeNormalizer_equation]
    · simp [UUTP15Rooted.candidateVertex,
        stageCoordinate, reducedCandidateVertex,
        matrixCoordinate_eq_equiv_symm, matrixCoordinateIndex_eq_equiv,
        ProfileDUUUFourSupportP15SemanticCatalogueFinite61.firstNormalizer_equation]
  · simp [UUTP15Rooted.candidateVertex,
      stageCoordinate, reducedCandidateVertex,
      matrixCoordinate_eq_equiv_symm, matrixCoordinateIndex_eq_equiv,
      ProfileDUUUFourSupportP15SemanticCatalogueFinite61.secondNormalizer_equation]

theorem candidateColor_stageOne
    (firstSupport secondSupport : SupportRepresentative)
    (root : RootCase) (free : FreeLabelAction)
    (first second : LabelAction) (left right : Fin 14) :
    UUTP15Rooted.candidateColor
        firstSupport secondSupport root free first second
        (stageCoordinate firstSupport secondSupport
          (freeNormalizerAction free)
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.firstNormalizerAction
            firstSupport root first)
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.secondNormalizerAction
            secondSupport root second) left)
        (stageCoordinate firstSupport secondSupport
          (freeNormalizerAction free)
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.firstNormalizerAction
            firstSupport root first)
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.secondNormalizerAction
            secondSupport root second) right) =
      reducedCandidateColor (supportPairIndex firstSupport secondSupport) root
        (firstReducedChoice firstSupport root first)
        (secondReducedChoice secondSupport root second) left right := by
  simp only [UUTP15Rooted.candidateColor,
    reducedCandidateColor]
  rw [candidateVertex_stageOne, candidateVertex_stageOne]

/-! ## Exact ordered representative for every normalized semantic branch -/

def representativePair {normalized : NormalizedSupportPair}
    (_parameters : RootedCandidateParameters normalized) : Fin 9 :=
  supportPairIndex normalized.first normalized.second

def representativeFirstReduced {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : ReducedLabel :=
  firstReducedChoice normalized.first parameters.normalization.root
    parameters.first

def representativeSecondReduced {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : ReducedLabel :=
  secondReducedChoice normalized.second parameters.normalization.root
    parameters.second

def representativeLeaf {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : OrderedLeaf :=
  reducedLeaf (representativePair parameters) parameters.normalization.root
    (representativeFirstReduced parameters)
    (representativeSecondReduced parameters)

noncomputable def representativeResidualCoordinate
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm (Fin 14) :=
  residualCoordinateEquiv (representativePair parameters)
    parameters.normalization.root (representativeFirstReduced parameters)
    (representativeSecondReduced parameters)

noncomputable def representativeStageCoordinate
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm (Fin 14) :=
  stageCoordinateEquiv normalized.first normalized.second
    (freeNormalizerAction parameters.free)
    (ProfileDUUUFourSupportP15SemanticCatalogueData61.firstNormalizerAction
      normalized.first parameters.normalization.root parameters.first)
    (ProfileDUUUFourSupportP15SemanticCatalogueData61.secondNormalizerAction
      normalized.second parameters.normalization.root parameters.second)

noncomputable def representativeCoordinate
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm (Fin 14) :=
  (representativeResidualCoordinate parameters).trans
    (representativeStageCoordinate parameters)

theorem representativeLeaf_first {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    orderedFirst (representativeLeaf parameters) = normalized.first := by
  calc
    orderedFirst (representativeLeaf parameters) =
        pairFirst (representativePair parameters) := by
      exact reducedLeaf_first _ _ _ _
    _ = normalized.first := pairFirst_supportPairIndex _ _

theorem representativeLeaf_second {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    orderedSecond (representativeLeaf parameters) = normalized.second := by
  calc
    orderedSecond (representativeLeaf parameters) =
        pairSecond (representativePair parameters) := by
      exact reducedLeaf_second _ _ _ _
    _ = normalized.second := pairSecond_supportPairIndex _ _

theorem representativeCoordinate_matrix
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized)
    (left right : Fin 14) (hne : left ≠ right) :
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized (representativeCoordinate parameters left))
        (physicalVertex normalized (representativeCoordinate parameters right)) =
      orderedMatrixColor (representativeLeaf parameters) left right := by
  have hcoordinate : representativeCoordinate parameters left ≠
      representativeCoordinate parameters right :=
    (representativeCoordinate parameters).injective.ne hne
  calc
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized (representativeCoordinate parameters left))
        (physicalVertex normalized (representativeCoordinate parameters right)) =
      UUTP15Rooted.candidateColor
        normalized.first normalized.second parameters.normalization.root
        parameters.free parameters.first parameters.second
        (representativeCoordinate parameters left)
        (representativeCoordinate parameters right) := by
          exact parameters.matrix_eq_candidateColor _ _ hcoordinate
    _ = reducedCandidateColor (representativePair parameters)
        parameters.normalization.root
        (representativeFirstReduced parameters)
        (representativeSecondReduced parameters)
        (representativeResidualCoordinate parameters left)
        (representativeResidualCoordinate parameters right) := by
      change UUTP15Rooted.candidateColor
        normalized.first normalized.second parameters.normalization.root
        parameters.free parameters.first parameters.second
        (representativeStageCoordinate parameters
          (representativeResidualCoordinate parameters left))
        (representativeStageCoordinate parameters
          (representativeResidualCoordinate parameters right)) = _
      rw [representativeStageCoordinate, stageCoordinateEquiv_apply,
        stageCoordinateEquiv_apply]
      exact candidateColor_stageOne normalized.first normalized.second
        parameters.normalization.root parameters.free parameters.first
        parameters.second (representativeResidualCoordinate parameters left)
        (representativeResidualCoordinate parameters right)
    _ = orderedMatrixColor (representativeLeaf parameters) left right := by
      rw [representativeResidualCoordinate, residualCoordinateEquiv_apply,
        residualCoordinateEquiv_apply]
      exact reducedLeaf_exact (representativePair parameters)
        parameters.normalization.root (representativeFirstReduced parameters)
        (representativeSecondReduced parameters) left right hne

theorem exists_orderedLeafCoordinate
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    ∃ leaf : OrderedLeaf,
      orderedFirst leaf = normalized.first ∧
      orderedSecond leaf = normalized.second ∧
      ∃ coordinate : Equiv.Perm (Fin 14),
        ∀ left right : Fin 14, left ≠ right →
          ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
              (physicalVertex normalized (coordinate left))
              (physicalVertex normalized (coordinate right)) =
            orderedMatrixColor leaf left right := by
  exact ⟨representativeLeaf parameters, representativeLeaf_first parameters,
    representativeLeaf_second parameters, representativeCoordinate parameters,
    representativeCoordinate_matrix parameters⟩

#print axioms candidateVertex_stageOne
#print axioms candidateColor_stageOne
#print axioms representativeCoordinate_matrix
#print axioms exists_orderedLeafCoordinate

end UUTP15Representative
end R4333
