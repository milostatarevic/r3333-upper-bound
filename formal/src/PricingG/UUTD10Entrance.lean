import PricingG.UUTD10Complete
import PricingG.DGenericExactMatrix

namespace PricingG.UUTD10Entrance
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveSupportC5CNF ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixLeafDataUUU2P15

theorem canonical_branch_supplies_leaf
    (branch : CanonicalBranch .uut 2 selectedPosition)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor 2) (blockVertex 2 selectedPosition.val) = 10) :
    ∃ leaf : Leaf, ∃ valuation : Sat.Valuation,
      valuation.satisfies_fmla (UUTD10Complete.formula leaf) := by
  obtain ⟨coordinates,matrix,⟨exact⟩⟩ :=
    PricingG.DGenericExactMatrix.exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten branch hdegree
  obtain ⟨leaf,⟨reduced⟩⟩ := UUTD10Complete.exists_representativeExactBranch_of_exact exact
  exact ⟨leaf,ProfileDHighOwnFiveSupportC5Formula.finalValuation reduced.branch,
    UUTD10Complete.representative_satisfies_formula leaf reduced⟩

#print axioms canonical_branch_supplies_leaf
end PricingG.UUTD10Entrance
