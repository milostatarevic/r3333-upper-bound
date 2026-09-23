import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61

namespace R4333
namespace ProfileDUUUFourSupportP15SemanticCatalogueResidualPair061

open ProfileDUUUFourSupportP15SemanticCatalogueResidualBase61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem residualExact_pair0 (root : RootCase)
    (first second : ReducedLabel) :
    ResidualExactAt (0 : Fin 9) root first second := by
  apply residualExact_of_upper
  unfold ResidualUpperExactAt residualCoordinate
  revert first second
  fin_cases root <;> decide

#print axioms residualExact_pair0

end ProfileDUUUFourSupportP15SemanticCatalogueResidualPair061
end R4333
