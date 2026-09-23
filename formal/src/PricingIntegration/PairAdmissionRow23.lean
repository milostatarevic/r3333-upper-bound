import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row23_ok : RowOK 23 := by decide +kernel
#print axioms row23_ok
end PricingIntegration.PairAdmission
