import R4333Lean.ProfileDUUUFourSupportP15SwapTransport61

namespace PricingG.P15SeedSatisfaction
open R4333
open ProfileDUUUFourSupportP15SupportPair61
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61
open ProfileDUUUFourSupportP15MatrixOnlyLeaves61
open ProfileDUUUFourSupportP15SemanticTransport61
open ProfileDUUUFourSupportP15SwapTransport61

/-- A full positioned four-support branch supplies a satisfying valuation of
one of the exact 189 retained matrix-only formulas. The equal-K15 swap moves
all semantic data together. No obstruction assembly or refutation is assumed. -/
theorem branch_supplies_seed (branch : ProfileDUUUFourSupportP15SupportPair61.Branch) :
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
end PricingG.P15SeedSatisfaction
