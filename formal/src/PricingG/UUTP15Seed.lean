import PricingG.UUTP15Swap

namespace PricingG.UUTP15Seed
open R4333
open UUTP15SupportPair
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61
open UUTP15Leaves
open UUTP15Transport
open UUTP15Swap

/-- A full positioned four-support branch supplies a satisfying valuation of
one of the exact 189 retained matrix-only formulas. The equal-K15 swap moves
all semantic data together. No obstruction assembly or refutation is assumed. -/
theorem branch_supplies_seed (branch : UUTP15SupportPair.Branch) :
    ∃ seed : ProfileDUUUFourSupportP15SwapData61.SwapSeed,
      ∃ valuation : Sat.Valuation,
        valuation.satisfies_fmla (matrixLeafFmla (seedLeaf seed)) := by
  obtain ⟨leaf, ⟨exact⟩⟩ := exists_exactOrderedLeaf branch
  obtain ⟨seed, hcover, hswap⟩ := exists_exact_seed_cover leaf
  have hexact : Nonempty (ExactOrderedLeaf (seedLeaf seed)) := by
    rcases hcover with hdirect | hswapped
    · exact hdirect ▸ ⟨exact⟩
    · exact hswapped ▸ exactOrderedLeaf_swap exact hswap
  obtain ⟨normalized⟩ := hexact
  exact ⟨seed, baseValuation normalized, exact_satisfies_matrixLeafFmla normalized⟩

#print axioms branch_supplies_seed
end PricingG.UUTP15Seed
