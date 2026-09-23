import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueData61
import R4333Lean.ProfileDUUUFourSupportP0SemanticOrbit61
import R4333Lean.ProfileDUUUFourSupportP15SwapFiniteCoverage61

/-!
# Kernel checks for the factorized P15 semantic catalogue

The generated data first lists the ten labelings compatible with each rooted
template and physical support.  Strong support stabilizers reduce those ten
choices to five (and to one for `s4`), leaving only 2,250 residual matrices.
This file checks each of those claims in Lean; it contains no SAT premise.
-/

namespace R4333
namespace ProfileDUUUFourSupportP15SemanticCatalogueFinite61

open SingleRootStarCNF
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDFourSupportRestoredRootK15
open ProfileDUUUFourSupportP0OrbitData61
open ProfileDUUUFourSupportP0SemanticOrbit61
open ProfileDUUUDegreeNineFactorOrbitCoverage61
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open ProfileDUUUFourSupportP15SemanticCatalogueData61
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev RootCase :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.RootCase

/-! ## The ten compatible labelings are exact and complete -/

def FirstCompatibility (supportRepresentative : SupportRepresentative)
    (root : RootCase) (perm : Fin 5 → Fin 5) : Prop :=
  ∀ left right, left ≠ right →
    canonicalPalette 3
        (k15Template (rootTwisted root)
          (rootFirstGroupVertex root (perm left))
          (rootFirstGroupVertex root (perm right))) =
      canonicalPalette 1
        (k15Template false
          ((support supportRepresentative).embedding left)
          ((support supportRepresentative).embedding right))

instance (supportRepresentative : SupportRepresentative) (root : RootCase)
    (perm : Fin 5 → Fin 5) :
    Decidable (FirstCompatibility supportRepresentative root perm) := by
  unfold FirstCompatibility
  infer_instance

def SecondCompatibility (supportRepresentative : SupportRepresentative)
    (root : RootCase) (perm : Fin 5 → Fin 5) : Prop :=
  ∀ left right, left ≠ right →
    canonicalPalette 3
        (k15Template (rootTwisted root)
          (rootSecondGroupVertex root (perm left))
          (rootSecondGroupVertex root (perm right))) =
      canonicalPalette 2
        (k15Template false
          ((support supportRepresentative).embedding left)
          ((support supportRepresentative).embedding right))

instance (supportRepresentative : SupportRepresentative) (root : RootCase)
    (perm : Fin 5 → Fin 5) :
    Decidable (SecondCompatibility supportRepresentative root perm) := by
  unfold SecondCompatibility
  infer_instance

theorem firstCompatiblePerm_bijective
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (action : LabelAction) :
    Function.Bijective
      (firstCompatiblePerm supportRepresentative root action) := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases action <;>
    decide

theorem secondCompatiblePerm_bijective
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (action : LabelAction) :
    Function.Bijective
      (secondCompatiblePerm supportRepresentative root action) := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases action <;>
    decide

theorem firstCompatiblePerm_compatible
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (action : LabelAction) :
    FirstCompatibility supportRepresentative root
      (firstCompatiblePerm supportRepresentative root action) := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases action <;>
    decide

theorem secondCompatiblePerm_compatible
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (action : LabelAction) :
    SecondCompatibility supportRepresentative root
      (secondCompatiblePerm supportRepresentative root action) := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases action <;>
    decide

theorem firstCompatiblePerm_complete_at
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (index : Fin 120)
    (hcompat : FirstCompatibility supportRepresentative root
      (fivePermutationAt index)) :
    ∃ action : LabelAction, ∀ p,
      fivePermutationAt index p =
        firstCompatiblePerm supportRepresentative root action p := by
  cases supportRepresentative <;> (revert root index hcompat; decide)

theorem secondCompatiblePerm_complete_at
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (index : Fin 120)
    (hcompat : SecondCompatibility supportRepresentative root
      (fivePermutationAt index)) :
    ∃ action : LabelAction, ∀ p,
      fivePermutationAt index p =
        secondCompatiblePerm supportRepresentative root action p := by
  cases supportRepresentative <;> (revert root index hcompat; decide)

theorem firstCompatiblePerm_complete
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (perm : Equiv.Perm (Fin 5))
    (hcompat : FirstCompatibility supportRepresentative root perm) :
    ∃ action : LabelAction, ∀ p,
      perm p = firstCompatiblePerm supportRepresentative root action p := by
  have hcompatAt : FirstCompatibility supportRepresentative root
      (fivePermutationAt (fivePermutationIndex perm)) := by
    simpa only [fivePermutationAt_index] using hcompat
  obtain ⟨action, ha⟩ := firstCompatiblePerm_complete_at
    supportRepresentative root (fivePermutationIndex perm) hcompatAt
  refine ⟨action, ?_⟩
  intro p
  rw [fivePermutationAt_index] at ha
  exact ha p

theorem secondCompatiblePerm_complete
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (perm : Equiv.Perm (Fin 5))
    (hcompat : SecondCompatibility supportRepresentative root perm) :
    ∃ action : LabelAction, ∀ p,
      perm p = secondCompatiblePerm supportRepresentative root action p := by
  have hcompatAt : SecondCompatibility supportRepresentative root
      (fivePermutationAt (fivePermutationIndex perm)) := by
    simpa only [fivePermutationAt_index] using hcompat
  obtain ⟨action, ha⟩ := secondCompatiblePerm_complete_at
    supportRepresentative root (fivePermutationIndex perm) hcompatAt
  refine ⟨action, ?_⟩
  intro p
  rw [fivePermutationAt_index] at ha
  exact ha p

/-! ## Algebraic reduction by the strong support stabilizers -/

theorem firstNormalizer_equation
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (action : LabelAction) (p : Fin 5) :
    firstCompatiblePerm supportRepresentative root action
        (q2SupportAction supportRepresentative
          (firstNormalizerAction supportRepresentative root action) p) =
      firstReducedPerm supportRepresentative root
        (firstReducedChoice supportRepresentative root action) p := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases action <;>
    fin_cases p <;> decide

theorem secondNormalizer_equation
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (action : LabelAction) (p : Fin 5) :
    secondCompatiblePerm supportRepresentative root action
        (q2SupportAction supportRepresentative
          (secondNormalizerAction supportRepresentative root action) p) =
      secondReducedPerm supportRepresentative root
        (secondReducedChoice supportRepresentative root action) p := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases action <;>
    fin_cases p <;> decide

theorem firstReducedPerm_bijective
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (reduced : ReducedLabel) :
    Function.Bijective
      (firstReducedPerm supportRepresentative root reduced) := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases reduced <;>
    decide

theorem secondReducedPerm_bijective
    (supportRepresentative : SupportRepresentative) (root : RootCase)
    (reduced : ReducedLabel) :
    Function.Bijective
      (secondReducedPerm supportRepresentative root reduced) := by
  cases supportRepresentative <;> fin_cases root <;> fin_cases reduced <;>
    decide

/-! ## The 2,250 residual matrices -/

def reducedCandidateVertex (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) (p : Fin 14) : Fin 15 :=
  match fourFiveFiveEquiv.symm p with
  | .inl (.inl free) => rootFreeGroupVertex root free
  | .inl (.inr firstPosition) =>
      rootFirstGroupVertex root
        (firstReducedPerm (pairFirst pair) root first firstPosition)
  | .inr secondPosition =>
      rootSecondGroupVertex root
        (secondReducedPerm (pairSecond pair) root second secondPosition)

def reducedCandidateColor (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) (left right : Fin 14) : Fin 4 :=
  canonicalPalette 3
    (k15Template (rootTwisted root)
      (reducedCandidateVertex pair root first second left)
      (reducedCandidateVertex pair root first second right))

theorem reducedLeaf_first (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) :
    orderedFirst (reducedLeaf pair root first second) = pairFirst pair := by
  revert first second
  fin_cases pair <;> fin_cases root <;> decide

theorem reducedLeaf_second (pair : Fin 9) (root : RootCase)
    (first second : ReducedLabel) :
    orderedSecond (reducedLeaf pair root first second) = pairSecond pair := by
  revert first second
  fin_cases pair <;> fin_cases root <;> decide

#print axioms firstCompatiblePerm_complete
#print axioms secondCompatiblePerm_complete
#print axioms firstNormalizer_equation
#print axioms secondNormalizer_equation
#print axioms reducedLeaf_first
#print axioms reducedLeaf_second

end ProfileDUUUFourSupportP15SemanticCatalogueFinite61
end R4333
