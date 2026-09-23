import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row00_ok : RowOK 0 := by decide +kernel
#print axioms row00_ok
end PricingIntegration.PairAdmission
