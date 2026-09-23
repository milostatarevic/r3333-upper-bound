import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61

namespace R4333
namespace ProfileDUUUFourSupportP15SemanticCatalogueResidualPair761

open ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem residualExact_pair7 (root : RootCase)
    (first second : ReducedLabel) :
    ResidualExactAt (7 : Fin 9) root first second := by
  apply residualExact_of_upper
  unfold ResidualUpperExactAt residualCoordinate
  revert first second
  fin_cases root <;> decide

#print axioms residualExact_pair7

end ProfileDUUUFourSupportP15SemanticCatalogueResidualPair761
end R4333
