import PricingIntegration.PairAdmissionData
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem row12_ok : RowOK 12 := by decide +kernel
#print axioms row12_ok
end PricingIntegration.PairAdmission
