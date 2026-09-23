import PricingIntegration.PairNativeBinding
namespace PricingIntegration.PairAdmission
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem native_binding_part1 : ∀j : Fin 100,NativeBinding (bindingIndex 1 j) := by decide +kernel
end PricingIntegration.PairAdmission
