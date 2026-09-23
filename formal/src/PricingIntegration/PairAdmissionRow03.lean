import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row03_ok : RowOK 3 := by decide +kernel
#print axioms row03_ok
end PricingIntegration.PairAdmission
