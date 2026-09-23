import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row30_ok : RowOK 30 := by decide +kernel
#print axioms row30_ok
end PricingIntegration.PairAdmission
