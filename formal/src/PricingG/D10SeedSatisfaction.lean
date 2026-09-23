import R4333Lean.ProfileDUUUDegreeTenExactEntranceUUU2P15

namespace PricingG.D10SeedSatisfaction
open R4333
open ProfileDHighOwnFiveSupportC5CNF ProfileDHighOwnFiveSupportC5Formula
open ProfileDColumnOwnColorIncidence61
open ProfileDTripleJoinReduction
open ProfileDDegreeTenMatrixLeafDataUUU2P15

/-- Full semantic entrance to exactly the 82 selected-Q16 degree-ten formulas,
with an explicit satisfying valuation; no search/refutation premise. -/
theorem branch_supplies_seed
    (branch : CanonicalBranch .uuu 2 selectedPosition)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor 2) (blockVertex 2 selectedPosition.val) = 10) :
    ∃ leaf : Leaf, ∃ valuation : Sat.Valuation,
      valuation.satisfies_fmla (formula leaf) := by
  obtain ⟨leaf, ⟨exact⟩⟩ :=
    ProfileDUUUDegreeTenExactEntranceUUU2P15.exists_representativeExactBranch_of_canonical_degreeTen
      branch hdegree
  exact ⟨leaf, finalValuation exact.branch, representativeExactBranch_satisfies_formula leaf exact⟩

#print axioms branch_supplies_seed
end PricingG.D10SeedSatisfaction
