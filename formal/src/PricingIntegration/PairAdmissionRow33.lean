import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row33_ok : RowOK 33 := by decide +kernel
#print axioms row33_ok
end PricingIntegration.PairAdmission
