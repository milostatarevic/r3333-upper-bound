import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row15_ok : RowOK 15 := by decide +kernel
#print axioms row15_ok
end PricingIntegration.PairAdmission
