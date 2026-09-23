import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row26_ok : RowOK 26 := by decide +kernel
#print axioms row26_ok
end PricingIntegration.PairAdmission
