import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row24_ok : RowOK 24 := by decide +kernel
#print axioms row24_ok
end PricingIntegration.PairAdmission
