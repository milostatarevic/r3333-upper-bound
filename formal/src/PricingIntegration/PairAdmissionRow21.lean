import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row21_ok : RowOK 21 := by decide +kernel
#print axioms row21_ok
end PricingIntegration.PairAdmission
