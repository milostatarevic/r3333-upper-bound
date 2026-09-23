import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row19_ok : RowOK 19 := by decide +kernel
#print axioms row19_ok
end PricingIntegration.PairAdmission
