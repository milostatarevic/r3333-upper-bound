import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row04_ok : RowOK 4 := by decide +kernel
#print axioms row04_ok
end PricingIntegration.PairAdmission
