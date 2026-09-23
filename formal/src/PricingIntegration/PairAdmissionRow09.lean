import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row09_ok : RowOK 9 := by decide +kernel
#print axioms row09_ok
end PricingIntegration.PairAdmission
