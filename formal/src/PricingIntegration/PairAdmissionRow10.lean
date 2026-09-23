import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row10_ok : RowOK 10 := by decide +kernel
#print axioms row10_ok
end PricingIntegration.PairAdmission
