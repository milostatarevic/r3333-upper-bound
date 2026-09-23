import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row27_ok : RowOK 27 := by decide +kernel
#print axioms row27_ok
end PricingIntegration.PairAdmission
