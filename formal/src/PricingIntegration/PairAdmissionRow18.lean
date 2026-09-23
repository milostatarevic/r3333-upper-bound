import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row18_ok : RowOK 18 := by decide +kernel
#print axioms row18_ok
end PricingIntegration.PairAdmission
