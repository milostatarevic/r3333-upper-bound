import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row28_ok : RowOK 28 := by decide +kernel
#print axioms row28_ok
end PricingIntegration.PairAdmission
