import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row35_ok : RowOK 35 := by decide +kernel
#print axioms row35_ok
end PricingIntegration.PairAdmission
