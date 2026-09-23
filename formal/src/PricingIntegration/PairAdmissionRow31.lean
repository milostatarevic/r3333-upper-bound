import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row31_ok : RowOK 31 := by decide +kernel
#print axioms row31_ok
end PricingIntegration.PairAdmission
