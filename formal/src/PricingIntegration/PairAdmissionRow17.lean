import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row17_ok : RowOK 17 := by decide +kernel
#print axioms row17_ok
end PricingIntegration.PairAdmission
