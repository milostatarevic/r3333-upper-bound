import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row25_ok : RowOK 25 := by decide +kernel
#print axioms row25_ok
end PricingIntegration.PairAdmission
