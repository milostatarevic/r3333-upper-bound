import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row29_ok : RowOK 29 := by decide +kernel
#print axioms row29_ok
end PricingIntegration.PairAdmission
