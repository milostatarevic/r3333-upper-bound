import PricingG.UUTD10OrbitTransport
import PricingG.UUTP15Representative
import PricingG.UUTP15Leaves

/-!
# Physical transport to an exact ordered P15 leaf

The factorized semantic catalogue supplies a permutation of the fourteen
`4|5|5` coordinates.  This module realizes that permutation by an actual
row permutation and strong automorphisms of the two ambient K15 blocks,
then packages the transported semantic branch as an `ExactOrderedLeaf`.
-/

namespace R4333
namespace UUTP15Transport

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDFourSupportRestoredRootK15
open ProfileDFourSupportForeignSupports61
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61
open UUTP15SupportPair
open UUTP15Base
open ProfileDUUUFourSupportP15SemanticCatalogueData61
open ProfileDUUUFourSupportP15SemanticCatalogueFinite61
open ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61
open UUTP15Representative
open UUTP15Rooted
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61
open UUTP15Leaves
open ProfileDUUUFourSupportP0OrbitData61
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open UUTD10OrbitTransport
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDDegreeTenMatrixLeafDataUUU2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Branch := UUTP15SupportPair.Branch
abbrev SupportRepresentative :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.SupportRepresentative
abbrev OrderedLeaf := ProfileDUUUFourSupportP15SwapData61.OrderedLeaf

/-! ## The six local actions in the two-stage quotient -/

def stageFree {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Fin 24 :=
  freeNormalizerAction parameters.free

def stageFirst {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Fin 10 :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.firstNormalizerAction
    normalized.first parameters.normalization.root parameters.first

def stageSecond {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Fin 10 :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.secondNormalizerAction
    normalized.second parameters.normalization.root parameters.second

def residualFree {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Fin 24 :=
  residualFreeAction (representativePair parameters)
    parameters.normalization.root (representativeFirstReduced parameters)
    (representativeSecondReduced parameters)

def residualFirst {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Fin 10 :=
  residualFirstAction (representativePair parameters)
    parameters.normalization.root (representativeFirstReduced parameters)
    (representativeSecondReduced parameters)

def residualSecond {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Fin 10 :=
  residualSecondAction (representativePair parameters)
    parameters.normalization.root (representativeFirstReduced parameters)
    (representativeSecondReduced parameters)

noncomputable def representativeFreeEquiv
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm (Fin 4) :=
  (freeFourActionEquiv (residualFree parameters)).trans
    (freeLabelEquiv (stageFree parameters))

noncomputable def stageTailPerm {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  q2TailStabilizerPerm normalized.first normalized.second
    (stageFirst parameters) (stageSecond parameters)

noncomputable def residualTailPerm {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  q2TailStabilizerPerm normalized.first normalized.second
    (residualFirst parameters) (residualSecond parameters)

noncomputable def representativeTailPerm
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  (residualTailPerm parameters).trans (stageTailPerm parameters)

/-! ## Semantic branch transports -/

noncomputable def liftFourEquiv (perm : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin 5) where
  toFun := Fin.lastCases (Fin.last 4) (fun p => (perm p).castSucc)
  invFun := Fin.lastCases (Fin.last 4) (fun p => (perm.symm p).castSucc)
  left_inv := by
    intro p
    induction p using Fin.lastCases with
    | last => rfl
    | cast p => simp
  right_inv := by
    intro p
    induction p using Fin.lastCases with
    | last => rfl
    | cast p => simp

@[simp] theorem liftFourEquiv_castSucc (perm : Equiv.Perm (Fin 4))
    (p : Fin 4) :
    liftFourEquiv perm p.castSucc = (perm p).castSucc := by
  simp [liftFourEquiv]

@[simp] theorem liftFourEquiv_last (perm : Equiv.Perm (Fin 4)) :
    liftFourEquiv perm (Fin.last 4) = Fin.last 4 := by
  rfl

noncomputable def transportBranchByTailStabilizer
    (first second : SupportRepresentative) (branch : Branch)
    (firstAction secondAction : Fin 10) : Branch where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveByTailPerm
      branch.toDegreeFlooredFiveExtension
      (q2TailStabilizerPerm first second firstAction secondAction)
      (q2TailStabilizer_templateCanonical
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
        first second firstAction secondAction)
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      (q2TailStabilizerPerm first second firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 2
          UUTP15SupportPair.SelectedPosition.val)) = 3
    rw [q2TailStabilizerPerm_blockTwo]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      (q2TailStabilizerPerm first second firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 2
          UUTP15SupportPair.SelectedPosition.val)) ≠ 3
    rw [q2TailStabilizerPerm_blockTwo]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (q2TailStabilizerPerm first second firstAction secondAction))
      3 (ProfileDTripleJoinReduction.blockVertex 2
        UUTP15SupportPair.SelectedPosition.val) = 10
    rw [colorDegree_relabelVertices, q2TailStabilizerPerm_blockTwo]
    exact branch.tailOwnDegreeEqTen

noncomputable def transportBranchByFreeEquiv
    (branch : Branch) (perm : Equiv.Perm (Fin 4)) : Branch where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveExtension (liftFourEquiv perm)
      branch.toDegreeFlooredFiveExtension
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (liftFourEquiv perm row.castSucc)
      (ProfileDTripleJoinReduction.blockVertex 2
        UUTP15SupportPair.SelectedPosition.val) = 3
    rw [liftFourEquiv_castSucc]
    exact branch.firstFourOwn (perm row)
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (liftFourEquiv perm (Fin.last 4))
      (ProfileDTripleJoinReduction.blockVertex 2
        UUTP15SupportPair.SelectedPosition.val) ≠ 3
    rw [liftFourEquiv_last]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := branch.tailOwnDegreeEqTen

/-- One reusable local action: a strong automorphism in each foreign K15,
followed by the indicated permutation of the four retained rows. -/
noncomputable def transportBranchByLocalAction
    (first second : SupportRepresentative) (branch : Branch)
    (free : Fin 24) (firstAction secondAction : Fin 10) : Branch :=
  transportBranchByFreeEquiv
    (transportBranchByTailStabilizer first second branch
      firstAction secondAction)
    (freeFourActionEquiv free)

noncomputable def stageTailBranch {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Branch :=
  transportBranchByTailStabilizer normalized.first normalized.second
    normalized.branch (stageFirst parameters) (stageSecond parameters)

noncomputable def stageTransportedBranch
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Branch :=
  transportBranchByLocalAction normalized.first normalized.second
    normalized.branch (stageFree parameters) (stageFirst parameters)
    (stageSecond parameters)

noncomputable def tailTransportedBranch
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Branch :=
  transportBranchByTailStabilizer normalized.first normalized.second
    (stageTailBranch parameters) (residualFirst parameters)
    (residualSecond parameters)

noncomputable def transportedBranch {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) : Branch :=
  transportBranchByLocalAction normalized.first normalized.second
    (stageTransportedBranch parameters) (residualFree parameters)
    (residualFirst parameters) (residualSecond parameters)

/-! ## Total-vertex covariance -/

noncomputable def fourTotalDecompEquiv :
    ProfileDFourRowCNF.TotalVertex ≃
      Sum (Fin 4) ProfileDRowExtension.TailVertex where
  toFun := ProfileDFourRowCNF.splitVertex
  invFun := ProfileDFourRowCNF.mergeVertex
  left_inv := ProfileDFourRowCNF.mergeVertex_splitVertex
  right_inv := by
    intro vertex
    cases vertex <;> simp [ProfileDFourRowCNF.mergeVertex]

noncomputable def fourTotalFreePerm (perm : Equiv.Perm (Fin 4)) :
    Equiv.Perm ProfileDFourRowCNF.TotalVertex :=
  fourTotalDecompEquiv.trans
    ((Equiv.sumCongr perm (Equiv.refl ProfileDRowExtension.TailVertex)).trans
      fourTotalDecompEquiv.symm)

@[simp] theorem fourTotalFreePerm_free (perm : Equiv.Perm (Fin 4))
    (row : Fin 4) :
    fourTotalFreePerm perm (ProfileDFourRowCNF.freeVertex row) =
      ProfileDFourRowCNF.freeVertex (perm row) := by
  simp [fourTotalFreePerm, fourTotalDecompEquiv,
    ProfileDFourRowCNF.mergeVertex]

@[simp] theorem fourTotalFreePerm_tail (perm : Equiv.Perm (Fin 4))
    (x : ProfileDRowExtension.TailVertex) :
    fourTotalFreePerm perm (ProfileDFourRowCNF.tailVertex x) =
      ProfileDFourRowCNF.tailVertex x := by
  simp [fourTotalFreePerm, fourTotalDecompEquiv,
    ProfileDFourRowCNF.mergeVertex]

noncomputable def fourTotalTailPerm
    (perm : Equiv.Perm ProfileDRowExtension.TailVertex) :
    Equiv.Perm ProfileDFourRowCNF.TotalVertex :=
  fourTotalDecompEquiv.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 4)) perm).trans
      fourTotalDecompEquiv.symm)

@[simp] theorem fourTotalTailPerm_free
    (perm : Equiv.Perm ProfileDRowExtension.TailVertex) (row : Fin 4) :
    fourTotalTailPerm perm (ProfileDFourRowCNF.freeVertex row) =
      ProfileDFourRowCNF.freeVertex row := by
  simp [fourTotalTailPerm, fourTotalDecompEquiv,
    ProfileDFourRowCNF.mergeVertex]

@[simp] theorem fourTotalTailPerm_tail
    (perm : Equiv.Perm ProfileDRowExtension.TailVertex)
    (x : ProfileDRowExtension.TailVertex) :
    fourTotalTailPerm perm (ProfileDFourRowCNF.tailVertex x) =
      ProfileDFourRowCNF.tailVertex (perm x) := by
  simp [fourTotalTailPerm, fourTotalDecompEquiv,
    ProfileDFourRowCNF.mergeVertex]

theorem totalColoring_transportBranchByFreeEquiv
    (branch : Branch) (perm : Equiv.Perm (Fin 4))
    (left right : ProfileDFourRowCNF.TotalVertex) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (transportBranchByFreeEquiv branch perm)) left right =
      ProfileDFourRowCNF.totalColoring (fourExtension branch)
        (fourTotalFreePerm perm left) (fourTotalFreePerm perm right) := by
  rw [← ProfileDFourRowCNF.mergeVertex_splitVertex left,
    ← ProfileDFourRowCNF.mergeVertex_splitVertex right]
  generalize ProfileDFourRowCNF.splitVertex left = leftPart
  generalize ProfileDFourRowCNF.splitVertex right = rightPart
  cases leftPart <;> cases rightPart <;>
    simp [transportBranchByFreeEquiv, fourExtension,
      UUTP15SupportPair.semantic,
      ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
      ProfileDFourSupportInside61.firstFourInsideColoring,
      transportDegreeFlooredFiveExtension, transportFiveExtension,
      fourTotalFreePerm, fourTotalDecompEquiv,
      ProfileDFourRowCNF.totalColoring, pullbackColoring,
      ProfileDFourRowCNF.mergeVertex]

theorem totalColoring_transportBranchByTailStabilizer
    (first second : SupportRepresentative) (branch : Branch)
    (firstAction secondAction : Fin 10)
    (left right : ProfileDFourRowCNF.TotalVertex) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension
          (transportBranchByTailStabilizer first second branch
            firstAction secondAction)) left right =
      ProfileDFourRowCNF.totalColoring (fourExtension branch)
        (fourTotalTailPerm
          (q2TailStabilizerPerm first second firstAction secondAction) left)
        (fourTotalTailPerm
          (q2TailStabilizerPerm first second firstAction secondAction)
          right) := by
  rw [← ProfileDFourRowCNF.mergeVertex_splitVertex left,
    ← ProfileDFourRowCNF.mergeVertex_splitVertex right]
  generalize ProfileDFourRowCNF.splitVertex left = leftPart
  generalize ProfileDFourRowCNF.splitVertex right = rightPart
  cases leftPart <;> cases rightPart <;>
    simp [transportBranchByTailStabilizer, fourExtension,
      UUTP15SupportPair.semantic,
      ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
      ProfileDFourSupportInside61.firstFourInsideColoring,
      transportDegreeFlooredFiveByTailPerm,
      transportFiveExtensionByTailPerm,
      ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
      fourTotalTailPerm, fourTotalDecompEquiv, relabelVertices,
      ProfileDFourRowCNF.totalColoring, pullbackColoring,
      ProfileDFourRowCNF.mergeVertex]

noncomputable def localTotalPerm
    (first second : SupportRepresentative) (free : Fin 24)
    (firstAction secondAction : Fin 10) :
    Equiv.Perm ProfileDFourRowCNF.TotalVertex :=
  (fourTotalFreePerm (freeFourActionEquiv free)).trans
    (fourTotalTailPerm
      (q2TailStabilizerPerm first second firstAction secondAction))

theorem totalColoring_transportBranchByLocalAction
    (first second : SupportRepresentative) (branch : Branch)
    (free : Fin 24) (firstAction secondAction : Fin 10)
    (left right : ProfileDFourRowCNF.TotalVertex) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension
          (transportBranchByLocalAction first second branch free
            firstAction secondAction)) left right =
      ProfileDFourRowCNF.totalColoring (fourExtension branch)
        (localTotalPerm first second free firstAction secondAction left)
        (localTotalPerm first second free firstAction secondAction right) := by
  unfold transportBranchByLocalAction localTotalPerm
  rw [totalColoring_transportBranchByFreeEquiv,
    totalColoring_transportBranchByTailStabilizer]
  rfl

@[simp] theorem localCoordinateEquiv_freeCoordinate
    (first second : SupportRepresentative) (free : Fin 24)
    (firstAction secondAction : Fin 10) (p : Fin 4) :
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
        first second free firstAction secondAction
        (fourFiveFiveEquiv (.inl (.inl p))) =
      fourFiveFiveEquiv (.inl (.inl (freeFourAction free p))) := by
  rw [ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv_apply]
  simp [ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateAction,
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateActionOnCoordinates]

@[simp] theorem localCoordinateEquiv_firstCoordinate
    (first second : SupportRepresentative) (free : Fin 24)
    (firstAction secondAction : Fin 10) (p : Fin 5) :
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
        first second free firstAction secondAction
        (fourFiveFiveEquiv (.inl (.inr p))) =
      fourFiveFiveEquiv
        (.inl (.inr (q2SupportAction first firstAction p))) := by
  rw [ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv_apply]
  simp [ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateAction,
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateActionOnCoordinates]

@[simp] theorem localCoordinateEquiv_secondCoordinate
    (first second : SupportRepresentative) (free : Fin 24)
    (firstAction secondAction : Fin 10) (p : Fin 5) :
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
        first second free firstAction secondAction
        (fourFiveFiveEquiv (.inr p)) =
      fourFiveFiveEquiv
        (.inr (q2SupportAction second secondAction p)) := by
  rw [ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv_apply]
  simp [ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateAction,
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateActionOnCoordinates]

theorem localTotalPerm_physicalVertex
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) (p : Fin 14) :
    localTotalPerm normalized.first normalized.second free
        firstAction secondAction (physicalVertex normalized p) =
      physicalVertex normalized
        (ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
          normalized.first normalized.second free firstAction secondAction p) := by
  rw [← matrixCoordinateIndex_coordinate p]
  generalize matrixCoordinate p = coordinate
  rcases coordinate with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · rw [show matrixCoordinateIndex (.inl (.inl freePosition)) =
          fourFiveFiveEquiv (.inl (.inl freePosition)) by
          exact matrixCoordinateIndex_eq_equiv _]
      simp only [localTotalPerm, Equiv.trans_apply,
        physicalVertex_freeCoordinate, fourTotalFreePerm_free,
        fourTotalTailPerm_free, localCoordinateEquiv_freeCoordinate]
      rfl
    · rw [show matrixCoordinateIndex (.inl (.inr firstPosition)) =
          fourFiveFiveEquiv (.inl (.inr firstPosition)) by
          exact matrixCoordinateIndex_eq_equiv _]
      simp only [localTotalPerm, Equiv.trans_apply,
        physicalVertex_firstCoordinate, fourTotalFreePerm_tail,
        fourTotalTailPerm_tail, q2TailStabilizerPerm_blockZero,
        q2Stabilizer_canonicalEmbedding,
        localCoordinateEquiv_firstCoordinate]
      rfl
  · rw [show matrixCoordinateIndex (.inr secondPosition) =
        fourFiveFiveEquiv (.inr secondPosition) by
        exact matrixCoordinateIndex_eq_equiv _]
    simp only [localTotalPerm, Equiv.trans_apply,
      physicalVertex_secondCoordinate, fourTotalFreePerm_tail,
      fourTotalTailPerm_tail, q2TailStabilizerPerm_blockOne,
      q2Stabilizer_canonicalEmbedding,
      localCoordinateEquiv_secondCoordinate]
    rfl

/-! ## The generic normalized local transport -/

theorem transportBranchByLocalAction_firstSupport
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) :
    firstForeignOwnSupport
        (UUTP15SupportPair.semantic
          (transportBranchByLocalAction normalized.first normalized.second
            normalized.branch free firstAction secondAction)) =
      (support normalized.first).positions := by
  change foreignOwnSupport
      (UUTP15SupportPair.semantic
        (transportBranchByLocalAction normalized.first normalized.second
          normalized.branch free firstAction secondAction)) 0 =
    (support normalized.first).positions
  apply Finset.ext
  intro p
  rw [ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport]
  change normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (q2TailStabilizerPerm normalized.first normalized.second
        firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 2
          UUTP15SupportPair.SelectedPosition.val))
      (q2TailStabilizerPerm normalized.first normalized.second
        firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 0 p.val)) = 3 ↔
    p ∈ (support normalized.first).positions
  rw [q2TailStabilizerPerm_blockTwo, q2TailStabilizerPerm_blockZero]
  let acted : Fin 15 := u15StabilizerEquiv .support7
    (q2VertexActionIndex normalized.first firstAction) p
  calc
    normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex 2
          UUTP15SupportPair.SelectedPosition.val)
        (ProfileDTripleJoinReduction.blockVertex 0 acted.val) = 3 ↔
      acted ∈ firstForeignOwnSupport
        (UUTP15SupportPair.semantic normalized.branch) := by
          exact (ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport
            (UUTP15SupportPair.semantic
              normalized.branch) (0 : Fin 3) acted).symm
    _ ↔ acted ∈ (support normalized.first).positions := by
      constructor
      · intro h
        rw [normalized.firstSupport] at h
        exact h
      · intro h
        rw [normalized.firstSupport]
        exact h
    _ ↔ p ∈ (support normalized.first).positions := by
      dsimp only [acted]
      cases normalized.first <;> fin_cases firstAction <;> fin_cases p <;>
        decide

theorem transportBranchByLocalAction_secondSupport
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) :
    secondForeignOwnSupport
        (UUTP15SupportPair.semantic
          (transportBranchByLocalAction normalized.first normalized.second
            normalized.branch free firstAction secondAction)) =
      (support normalized.second).positions := by
  change foreignOwnSupport
      (UUTP15SupportPair.semantic
        (transportBranchByLocalAction normalized.first normalized.second
          normalized.branch free firstAction secondAction)) 1 =
    (support normalized.second).positions
  apply Finset.ext
  intro p
  rw [ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport]
  change normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (q2TailStabilizerPerm normalized.first normalized.second
        firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 2
          UUTP15SupportPair.SelectedPosition.val))
      (q2TailStabilizerPerm normalized.first normalized.second
        firstAction secondAction
        (ProfileDTripleJoinReduction.blockVertex 1 p.val)) = 3 ↔
    p ∈ (support normalized.second).positions
  rw [q2TailStabilizerPerm_blockTwo, q2TailStabilizerPerm_blockOne]
  let acted : Fin 15 := u15StabilizerEquiv .support7
    (q2VertexActionIndex normalized.second secondAction) p
  calc
    normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex 2
          UUTP15SupportPair.SelectedPosition.val)
        (ProfileDTripleJoinReduction.blockVertex 1 acted.val) = 3 ↔
      acted ∈ secondForeignOwnSupport
        (UUTP15SupportPair.semantic normalized.branch) := by
          exact (ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport
            (UUTP15SupportPair.semantic
              normalized.branch) (1 : Fin 3) acted).symm
    _ ↔ acted ∈ (support normalized.second).positions := by
      constructor
      · intro h
        rw [normalized.secondSupport] at h
        exact h
      · intro h
        rw [normalized.secondSupport]
        exact h
    _ ↔ p ∈ (support normalized.second).positions := by
      dsimp only [acted]
      cases normalized.second <;> fin_cases secondAction <;> fin_cases p <;>
        decide

/-- Transport a normalized P15 branch by one checked local `S₄ × H × H`
action.  Both support representatives stay literally unchanged. -/
noncomputable def transportNormalizedLocal
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) : NormalizedSupportPair where
  first := normalized.first
  second := normalized.second
  branch := transportBranchByLocalAction normalized.first normalized.second
    normalized.branch free firstAction secondAction
  firstSupport :=
    transportBranchByLocalAction_firstSupport normalized free
      firstAction secondAction
  secondSupport :=
    transportBranchByLocalAction_secondSupport normalized free
      firstAction secondAction

@[simp] theorem transportNormalizedLocal_first
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) :
    (transportNormalizedLocal normalized free firstAction secondAction).first =
      normalized.first := rfl

@[simp] theorem transportNormalizedLocal_second
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) :
    (transportNormalizedLocal normalized free firstAction secondAction).second =
      normalized.second := rfl

theorem transportNormalizedLocal_matrix
    (normalized : NormalizedSupportPair) (free : Fin 24)
    (firstAction secondAction : Fin 10) (left right : Fin 14) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension
          (transportNormalizedLocal normalized free firstAction secondAction).branch)
        (physicalVertex
          (transportNormalizedLocal normalized free firstAction secondAction)
          left)
        (physicalVertex
          (transportNormalizedLocal normalized free firstAction secondAction)
          right) =
      ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized
          (ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
            normalized.first normalized.second free firstAction secondAction
            left))
        (physicalVertex normalized
          (ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
            normalized.first normalized.second free firstAction secondAction
            right)) := by
  change ProfileDFourRowCNF.totalColoring
      (fourExtension
        (transportBranchByLocalAction normalized.first normalized.second
          normalized.branch free firstAction secondAction))
      (physicalVertex normalized left) (physicalVertex normalized right) = _
  rw [totalColoring_transportBranchByLocalAction,
    localTotalPerm_physicalVertex, localTotalPerm_physicalVertex]

theorem freeLabelEquiv_eq_freeFourActionEquiv (action : Fin 24) :
    freeLabelEquiv action = freeFourActionEquiv action := by
  apply Equiv.ext
  intro p
  simp only [freeLabelEquiv, freeFourActionEquiv,
    Equiv.ofBijective_apply]
  fin_cases action <;> fin_cases p <;> decide

theorem representativeStageCoordinate_eq_local
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    representativeStageCoordinate parameters =
      ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
        normalized.first normalized.second (stageFree parameters)
        (stageFirst parameters) (stageSecond parameters) := by
  unfold representativeStageCoordinate
    UUTP15Representative.stageCoordinateEquiv
    ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
    stageFree stageFirst stageSecond
  rw [freeLabelEquiv_eq_freeFourActionEquiv]
  rfl

theorem representativeResidualCoordinate_eq_local
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    representativeResidualCoordinate parameters =
      ProfileDUUUFourSupportP15SwapFiniteCoverage61.localCoordinateEquiv
        normalized.first normalized.second (residualFree parameters)
        (residualFirst parameters) (residualSecond parameters) := by
  unfold representativeResidualCoordinate residualCoordinateEquiv
    residualFree residualFirst residualSecond
  simp only [representativePair, pairFirst_supportPairIndex,
    pairSecond_supportPairIndex]

noncomputable def representativeTotalPerm
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    Equiv.Perm ProfileDFourRowCNF.TotalVertex :=
  (localTotalPerm normalized.first normalized.second
      (residualFree parameters) (residualFirst parameters)
      (residualSecond parameters)).trans
    (localTotalPerm normalized.first normalized.second
      (stageFree parameters) (stageFirst parameters)
      (stageSecond parameters))

theorem representativeTotalPerm_physicalVertex
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) (p : Fin 14) :
    representativeTotalPerm parameters (physicalVertex normalized p) =
      physicalVertex normalized (representativeCoordinate parameters p) := by
  change localTotalPerm normalized.first normalized.second
      (stageFree parameters) (stageFirst parameters) (stageSecond parameters)
      (localTotalPerm normalized.first normalized.second
        (residualFree parameters) (residualFirst parameters)
        (residualSecond parameters) (physicalVertex normalized p)) = _
  rw [localTotalPerm_physicalVertex, localTotalPerm_physicalVertex]
  rw [← representativeStageCoordinate_eq_local,
    ← representativeResidualCoordinate_eq_local]
  rfl

theorem totalColoring_transportedBranch
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized)
    (left right : ProfileDFourRowCNF.TotalVertex) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (transportedBranch parameters)) left right =
      ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (representativeTotalPerm parameters left)
        (representativeTotalPerm parameters right) := by
  unfold transportedBranch stageTransportedBranch
  rw [totalColoring_transportBranchByLocalAction,
    totalColoring_transportBranchByLocalAction]
  rfl

theorem transportedBranch_matrixExact
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized)
    (left right : Fin 14) (hne : left ≠ right) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (transportedBranch parameters))
        (physicalVertex normalized left) (physicalVertex normalized right) =
      orderedMatrixColor (representativeLeaf parameters) left right := by
  rw [totalColoring_transportedBranch,
    representativeTotalPerm_physicalVertex,
    representativeTotalPerm_physicalVertex]
  exact representativeCoordinate_matrix parameters left right hne

/-! ## Twice-transported normalized pair and exact leaf -/

noncomputable def stageTransportedNormalized
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    NormalizedSupportPair :=
  transportNormalizedLocal normalized (stageFree parameters)
    (stageFirst parameters) (stageSecond parameters)

noncomputable def transportedNormalized
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    NormalizedSupportPair :=
  transportNormalizedLocal (stageTransportedNormalized parameters)
    (residualFree parameters) (residualFirst parameters)
    (residualSecond parameters)

@[simp] theorem transportedNormalized_first
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    (transportedNormalized parameters).first = normalized.first := rfl

@[simp] theorem transportedNormalized_second
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    (transportedNormalized parameters).second = normalized.second := rfl

theorem transportedNormalized_matrixExact
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized)
    (left right : Fin 14) (hne : left ≠ right) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (transportedNormalized parameters).branch)
        (physicalVertex (transportedNormalized parameters) left)
        (physicalVertex (transportedNormalized parameters) right) =
      orderedMatrixColor (representativeLeaf parameters) left right := by
  change ProfileDFourRowCNF.totalColoring
      (fourExtension (transportedBranch parameters))
      (physicalVertex normalized left) (physicalVertex normalized right) = _
  exact transportedBranch_matrixExact parameters left right hne

theorem leafPhysicalVertex_eq_physicalVertex
    (normalized : NormalizedSupportPair) (leaf : OrderedLeaf)
    (hfirst : normalized.first = orderedFirst leaf)
    (hsecond : normalized.second = orderedSecond leaf) (p : Fin 14) :
    leafPhysicalVertex leaf p = physicalVertex normalized p := by
  rw [← matrixCoordinateIndex_coordinate p]
  generalize matrixCoordinate p = coordinate
  rcases coordinate with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · rw [show matrixCoordinateIndex (.inl (.inl freePosition)) =
          freeLabel freePosition by rfl,
        leafPhysicalVertex_free, physicalVertex_free]
    · rw [show matrixCoordinateIndex (.inl (.inr firstPosition)) =
          firstForeignLabel firstPosition by rfl,
        leafPhysicalVertex_first, physicalVertex_first, hfirst]
  · rw [show matrixCoordinateIndex (.inr secondPosition) =
        secondForeignLabel secondPosition by rfl,
      leafPhysicalVertex_second, physicalVertex_second, hsecond]

noncomputable def exactOrderedLeaf
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) :
    ExactOrderedLeaf (representativeLeaf parameters) where
  normalized := transportedNormalized parameters
  first_eq := by
    change normalized.first = orderedFirst (representativeLeaf parameters)
    exact (representativeLeaf_first parameters).symm
  second_eq := by
    change normalized.second = orderedSecond (representativeLeaf parameters)
    exact (representativeLeaf_second parameters).symm
  matrixExact := by
    intro left right hne
    have hfirst : (transportedNormalized parameters).first =
        orderedFirst (representativeLeaf parameters) := by
      change normalized.first = orderedFirst (representativeLeaf parameters)
      exact (representativeLeaf_first parameters).symm
    have hsecond : (transportedNormalized parameters).second =
        orderedSecond (representativeLeaf parameters) := by
      change normalized.second = orderedSecond (representativeLeaf parameters)
      exact (representativeLeaf_second parameters).symm
    rw [leafPhysicalVertex_eq_physicalVertex
        (transportedNormalized parameters) (representativeLeaf parameters)
        hfirst hsecond left,
      leafPhysicalVertex_eq_physicalVertex
        (transportedNormalized parameters) (representativeLeaf parameters)
        hfirst hsecond right]
    exact transportedNormalized_matrixExact parameters left right hne

/-- Every semantic P15 branch reaches one literal ordered matrix leaf. -/
theorem exists_exactOrderedLeaf (branch : Branch) :
    ∃ leaf : OrderedLeaf, Nonempty (ExactOrderedLeaf leaf) := by
  obtain ⟨normalized⟩ := exists_normalizedSupportPair branch
  obtain ⟨parameters⟩ := exists_rootedCandidateParameters normalized
  exact ⟨representativeLeaf parameters, ⟨exactOrderedLeaf parameters⟩⟩

#print axioms transportNormalizedLocal
#print axioms transportNormalizedLocal_matrix
#print axioms representativeTotalPerm_physicalVertex
#print axioms transportedBranch_matrixExact
#print axioms exactOrderedLeaf
#print axioms exists_exactOrderedLeaf

end UUTP15Transport
end R4333
