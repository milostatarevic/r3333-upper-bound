import PricingG.UUTD9Swap
import PricingG.UUTD9StrongSemantic
import PricingG.UUTD9Root1Semantic
import PricingG.UUTD9Root4Semantic
import PricingG.UUTD9Root12Semantic

namespace PricingG.UUTD9Restricted
open R4333
open ProfileDUUUDegreeNineFiniteBoundary61
open UUTD9Realization
open UUTD9Swap
open UUTD9StrongCase
open UUTD9Root1Case
open UUTD9Root4Case
open UUTD9Root12Case

set_option maxHeartbeats 0

abbrev Leaf := Fin 72 ⊕ (Fin 132 ⊕ (Fin 132 ⊕ Fin 72))

def formula : Leaf → Sat.Fmla
  | .inl i => UUTD9StrongFormula.quotientLeafFmla i
  | .inr (.inl i) => UUTD9Root1Formula.quotientLeafFmla i
  | .inr (.inr (.inl i)) => UUTD9Root4Formula.quotientLeafFmla i
  | .inr (.inr (.inr i)) => UUTD9Root12Formula.quotientLeafFmla i

theorem leaf_card : Fintype.card Leaf = 408 := by simp [Leaf]

def SomeLeafSatisfiable : Prop :=
  ∃ leaf : Leaf, ∃ valuation : Sat.Valuation, valuation.satisfies_fmla (formula leaf)

section
open UUTD9StrongOrbit
open UUTD9StrongFormula
open UUTD9StrongSemantic

theorem strong_supplies_leaf (realization : DegreeNineCaseRealization strongCase) :
    SomeLeafSatisfiable := by
  obtain ⟨representative, normalized, hnormalized⟩ :=
    strongRealization_reduces_to_72 realization
  refine ⟨.inl representative, quotientFinalValuation representative normalized, ?_⟩
  change (quotientFinalValuation representative normalized).satisfies_fmla
    (quotientLeafFmla representative)
  apply factorAssignmentRealization_satisfies_quotientLeafFmla representative normalized
  simpa [quotientRepresentativeFree, quotientRepresentativeLarge,
    quotientRepresentativeSmall] using hnormalized
end

section
open UUTD9Root1Orbit
open UUTD9Root1Formula
open UUTD9Root1Semantic

theorem twistedRoot1_supplies_leaf (realization : DegreeNineCaseRealization twistedRoot1Case) :
    SomeLeafSatisfiable := by
  obtain ⟨representative, normalized, hnormalized⟩ :=
    twistedRoot1Realization_reduces_to_132 realization
  refine ⟨.inr (.inl representative), quotientFinalValuation representative normalized, ?_⟩
  change (quotientFinalValuation representative normalized).satisfies_fmla
    (quotientLeafFmla representative)
  apply factorAssignmentRealization_satisfies_quotientLeafFmla representative normalized
  simpa [quotientRepresentativeFree, quotientRepresentativeLarge,
    quotientRepresentativeSmall] using hnormalized
end

section
open UUTD9Root4Orbit
open UUTD9Root4Formula
open UUTD9Root4Semantic

theorem twistedRoot4_supplies_leaf (realization : DegreeNineCaseRealization twistedRoot4Case) :
    SomeLeafSatisfiable := by
  obtain ⟨representative, normalized, hnormalized⟩ :=
    twistedRoot4Realization_reduces_to_132 realization
  refine ⟨.inr (.inr (.inl representative)), quotientFinalValuation representative normalized, ?_⟩
  change (quotientFinalValuation representative normalized).satisfies_fmla
    (quotientLeafFmla representative)
  apply factorAssignmentRealization_satisfies_quotientLeafFmla representative normalized
  simpa [quotientRepresentativeFree, quotientRepresentativeLarge,
    quotientRepresentativeSmall] using hnormalized
end

section
open UUTD9Root12Orbit
open UUTD9Root12Formula
open UUTD9Root12Semantic

theorem twistedRoot12_supplies_leaf (realization : DegreeNineCaseRealization twistedRoot12Case) :
    SomeLeafSatisfiable := by
  obtain ⟨representative, normalized, hnormalized⟩ :=
    twistedRoot12Realization_reduces_to_72 realization
  refine ⟨.inr (.inr (.inr representative)), quotientFinalValuation representative normalized, ?_⟩
  change (quotientFinalValuation representative normalized).satisfies_fmla
    (quotientLeafFmla representative)
  apply factorAssignmentRealization_satisfies_quotientLeafFmla representative normalized
  simpa [quotientRepresentativeFree, quotientRepresentativeLarge,
    quotientRepresentativeSmall] using hnormalized
end

/-- Exactly the four retained slot-three families, with whole semantic
witnesses carried through root and support normalization. -/
theorem false_orientation_supplies_leaf
    (rootCase : DegreeNineTemplateRootCase (residualDeficientColor 3 false))
    (realization : DegreeNineCaseRealization (⟨3, false, rootCase⟩ : UUTD9Realization.ResidualCase)) :
    SomeLeafSatisfiable := by
  rcases rootCase with ⟨twisted, ⟨root, hroot⟩⟩
  cases twisted
  · have hroot_eq : root = 2 := by
      rw [residualUntwistedRootRepresentativeSet 3 false] at hroot
      simpa using hroot
    subst root
    apply strong_supplies_leaf
    simpa [strongCase, strongRootCase] using realization
  · have hroot_cases : root = 1 ∨ root = 4 ∨ root = 12 := by
      rw [residualTwistedRootRepresentativeSet 3 false] at hroot
      simpa using hroot
    rcases hroot_cases with hroot_eq | hroot_eq | hroot_eq
    · subst root
      apply twistedRoot1_supplies_leaf
      simpa [twistedRoot1Case, twistedRoot1RootCase] using realization
    · subst root
      apply twistedRoot4_supplies_leaf
      simpa [twistedRoot4Case, twistedRoot4RootCase] using realization
    · subst root
      apply twistedRoot12_supplies_leaf
      simpa [twistedRoot12Case, twistedRoot12RootCase] using realization

/-- The other physical 5+4 orientation reaches the same exact 408 formulas
by the already-proved simultaneous equal-K15 swap. No Tier2 family occurs. -/
theorem slot_three_supplies_leaf
    (firstLarge : Bool)
    (rootCase : DegreeNineTemplateRootCase (residualDeficientColor 3 firstLarge))
    (realization : DegreeNineCaseRealization (⟨3, firstLarge, rootCase⟩ : UUTD9Realization.ResidualCase)) :
    SomeLeafSatisfiable := by
  cases firstLarge
  · exact false_orientation_supplies_leaf rootCase realization
  · obtain ⟨target, hslot, horientation, ⟨targetRealization⟩⟩ :=
      exists_opposite_blockTwo_caseRealization true rootCase realization
    rcases target with ⟨targetSlot, targetFirstLarge, targetRootCase⟩
    change targetSlot = 3 at hslot
    change targetFirstLarge = !true at horientation
    have hfalse : targetFirstLarge = false := by simpa using horientation
    subst targetSlot
    subst targetFirstLarge
    exact false_orientation_supplies_leaf targetRootCase targetRealization

/-- Construct the finite case from a complete positioned exact-degree-nine
branch, retaining all row and cross-edge compatibility in its realization. -/
theorem positioned_branch_supplies_leaf
    (branch : ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport
      .uut 2 (Fin.last 15))
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (ProfileDColumnOwnColorIncidence61.blockRootColor 2)
      (ProfileDTripleJoinReduction.blockVertex 2 15) = 9) :
    SomeLeafSatisfiable := by
  obtain ⟨skeleton, normal, rootCase, htwisted, hroot⟩ :=
    UUTD9Realization.exists_templateRootCase_for_positioned_degreeNine 3 branch hdegree
  exact slot_three_supplies_leaf skeleton.firstLarge rootCase {
    branch := branch
    tailOwnDegreeNine := hdegree
    skeleton := skeleton
    caseFirstLarge_eq := rfl
    normal := normal
    caseTwisted_eq := htwisted
    caseRoot_eq := hroot
  }

#print axioms slot_three_supplies_leaf
#print axioms positioned_branch_supplies_leaf
end PricingG.UUTD9Restricted
