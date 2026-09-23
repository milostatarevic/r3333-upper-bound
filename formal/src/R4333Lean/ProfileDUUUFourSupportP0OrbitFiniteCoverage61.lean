import R4333Lean.ProfileDUUUFourSupportP0OrbitData61

/-!
# Kernel-checked finite coverage of the restored-root K15 matrix catalogue

The 24,000 rooted and labelled candidates for each normalized support pair
are reduced by explicit free/U15/U16 actions to one of the 36 exact matrix
leaves.  The witness table is checked below by ordinary kernel reduction.
-/

namespace R4333
namespace ProfileDUUUFourSupportP0OrbitData61

open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUFourSupportP0RepresentativeData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/- Only these 300 entries can occur after the algebraic first-stage
normalization.  Keeping this table separate from the 72,000 raw witnesses is
important: the finite proof below reduces just 110 fixed matrices. -/
def reducedNormalizerWord0 : RootCase → Fin 10 → Nat :=
  ![![78739, 43641, 78741, 77882, 78746, 44505, 77875, 43639, 77877, 44503],
    ![70286, 27333, 26467, 69415, 26469, 70279, 27331, 69417, 69422, 70281],
    ![69669, 27079, 69667, 26215, 27086, 70533, 26217, 70531, 27081, 26222],
    ![18266, 1305, 18259, 441, 18261, 17402, 439, 17395, 1303, 17397],
    ![34718, 35577, 35582, 62037, 34711, 61171, 35575, 61173, 62035, 34713],
    ![78086, 43710, 78097, 78951, 78087, 44574, 78950, 43712, 78961, 44576],
    ![26823, 25969, 26822, 69344, 26833, 70208, 25958, 69342, 25959, 70206],
    ![26208, 27082, 69670, 26218, 27087, 27072, 69660, 70534, 70524, 26223],
    ![26137, 27011, 61385, 26147, 61384, 27001, 60528, 60521, 61392, 60520],
    ![52201, 53075, 53065, 70744, 69888, 69881, 70752, 69880, 70745, 52211]]

def reducedNormalizerWord2 : RootCase → Fin 10 → Nat :=
  ![![44518, 43654, 78762, 77898, 43662, 44526, 78752, 77888, 78754, 77890],
    ![26490, 27354, 70292, 69428, 27346, 26482, 69430, 70294, 70302, 69438],
    ![69682, 70546, 27092, 26228, 69690, 70554, 26230, 27094, 27102, 26238],
    ![462, 1326, 1318, 454, 18282, 17418, 18272, 17408, 18274, 17410],
    ![35598, 34734, 62058, 61194, 35588, 34724, 62050, 61186, 35590, 34726],
    ![78100, 78964, 78111, 78975, 78101, 78965, 43725, 44589, 44597, 43733],
    ![26847, 25983, 70221, 69357, 70229, 69365, 26836, 25972, 26837, 25973],
    ![26231, 27095, 26233, 27097, 69691, 70555, 69683, 70547, 27103, 26239],
    ![26160, 27024, 26162, 27026, 61408, 60544, 61399, 60535, 61398, 60534],
    ![53088, 52224, 70768, 69904, 69895, 70759, 70758, 69894, 52226, 53090]]

def reducedNormalizerWord7 : RootCase → Fin 10 → Nat :=
  ![![83951, 80495, 81359, 84815, 85679, 82223, 78767, 77903, 83087, 79631],
    ![77219, 73763, 70307, 69443, 75491, 72035, 71171, 74627, 72899, 76355],
    ![28835, 32291, 27107, 26243, 34019, 30563, 27971, 31427, 29699, 33155],
    ![25199, 21743, 23471, 20015, 20879, 24335, 18287, 17423, 22607, 19151],
    ![38195, 41651, 39059, 42515, 35603, 34739, 40787, 37331, 39923, 36467],
    ![78118, 78982, 85030, 81574, 79846, 83302, 80710, 84166, 82438, 85894],
    ![29446, 32902, 32038, 28582, 30310, 33766, 26854, 25990, 31174, 27718],
    ![27968, 31424, 26240, 27104, 33152, 29696, 28832, 32288, 30560, 34016],
    ![27897, 31353, 26169, 27033, 33081, 29625, 28761, 32217, 30489, 33945],
    ![57417, 53961, 59145, 55689, 58281, 54825, 56553, 60009, 52233, 53097]]

def reducedNormalizerWord : SupportKind → RootCase → Fin 10 → Nat
  | .support0 => reducedNormalizerWord0
  | .support2 => reducedNormalizerWord2
  | .support7 => reducedNormalizerWord7

def reducedNormalizerSelector (kind : SupportKind) (root : RootCase)
    (first : Fin 10) : MatrixSelector :=
  Fin.ofNat 36 (reducedNormalizerWord kind root first)

def reducedNormalizerFreeAction (kind : SupportKind) (root : RootCase)
    (first : Fin 10) : FreeLabelAction :=
  Fin.ofNat 24 (reducedNormalizerWord kind root first / 36)

def reducedNormalizerFirstAction (kind : SupportKind) (root : RootCase)
    (first : Fin 10) : Fin 10 :=
  Fin.ofNat 10 (reducedNormalizerWord kind root first / (36 * 24))

def reducedNormalizerSecondAction (kind : SupportKind) (root : RootCase)
    (first : Fin 10) : Fin 10 :=
  Fin.ofNat 10 (reducedNormalizerWord kind root first / (36 * 24 * 10))

def ReducedCandidateCovered (kind : SupportKind) (root : RootCase)
    (first : Fin 10) : Prop :=
  matrixPair (reducedNormalizerSelector kind root first) = supportKindPair kind ∧
    ∀ left right : Fin 14, left ≠ right →
      checkedCandidateColor kind root 0 first 0
          (checkedOrbitCoordinate kind (reducedNormalizerFreeAction kind root first)
            (reducedNormalizerFirstAction kind root first)
            (reducedNormalizerSecondAction kind root first) left)
          (checkedOrbitCoordinate kind (reducedNormalizerFreeAction kind root first)
            (reducedNormalizerFirstAction kind root first)
            (reducedNormalizerSecondAction kind root first) right) =
        representativeMatrixColor (reducedNormalizerSelector kind root first) left right

instance (kind : SupportKind) (root : RootCase) (first : Fin 10) :
    Decidable (ReducedCandidateCovered kind root first) := by
  unfold ReducedCandidateCovered
  infer_instance

theorem candidateVertex_stageOne
    (kind : SupportKind) (root : RootCase) (free : FreeLabelAction)
    (first second : Fin 10) (p : Fin 14) :
    candidateVertex kind root free first second
        (orbitCoordinate kind (freeNormalizerAction free)
          (firstNormalizerAction kind root first)
          (secondNormalizerAction root second) p) =
      candidateVertex kind root 0 (firstReduced kind root first) 0 p := by
  rw [← matrixCoordinateIndex_coordinate p]
  generalize matrixCoordinate p = c
  rcases c with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · simp [candidateVertex, orbitCoordinate, freeNormalizer_equation]
    · simp [candidateVertex, orbitCoordinate, firstNormalizer_equation]
  · simp [candidateVertex, orbitCoordinate, secondNormalizer_equation]

theorem candidateColor_stageOne
    (kind : SupportKind) (root : RootCase) (free : FreeLabelAction)
    (first second : Fin 10) (left right : Fin 14) :
    candidateColor kind root free first second
        (orbitCoordinate kind (freeNormalizerAction free)
          (firstNormalizerAction kind root first)
          (secondNormalizerAction root second) left)
        (orbitCoordinate kind (freeNormalizerAction free)
          (firstNormalizerAction kind root first)
          (secondNormalizerAction root second) right) =
      candidateColor kind root 0 (firstReduced kind root first) 0
        left right := by
  unfold candidateColor
  rw [candidateVertex_stageOne, candidateVertex_stageOne]

theorem reducedCoverage_support0 (root : RootCase) (first : Fin 10)
    (hreduced : firstReduced .support0 root first = first) :
    ReducedCandidateCovered .support0 root first := by
  fin_cases root <;> fin_cases first <;> (revert hreduced; decide)

theorem reducedCoverage_support2 (root : RootCase) (first : Fin 10)
    (hreduced : firstReduced .support2 root first = first) :
    ReducedCandidateCovered .support2 root first := by
  fin_cases root <;> fin_cases first <;> (revert hreduced; decide)

theorem reducedCoverage_support7 (root : RootCase) (first : Fin 10)
    (hreduced : firstReduced .support7 root first = first) :
    ReducedCandidateCovered .support7 root first := by
  fin_cases root <;> fin_cases first <;> (revert hreduced; decide)

theorem reducedCoverage (kind : SupportKind) (root : RootCase)
    (first : Fin 10) (hreduced : firstReduced kind root first = first) :
    ReducedCandidateCovered kind root first := by
  cases kind
  · exact reducedCoverage_support0 root first hreduced
  · exact reducedCoverage_support2 root first hreduced
  · exact reducedCoverage_support7 root first hreduced

#print axioms candidateColor_stageOne
#print axioms reducedCoverage

end ProfileDUUUFourSupportP0OrbitData61
end R4333
