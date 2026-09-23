import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row01_ok : RowOK 1 := by decide +kernel
#print axioms row01_ok
end PricingIntegration.PairAdmission
