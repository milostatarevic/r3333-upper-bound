import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row05_ok : RowOK 5 := by decide +kernel
#print axioms row05_ok
end PricingIntegration.PairAdmission
