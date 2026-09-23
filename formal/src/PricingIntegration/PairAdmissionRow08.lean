import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row08_ok : RowOK 8 := by decide +kernel
#print axioms row08_ok
end PricingIntegration.PairAdmission
