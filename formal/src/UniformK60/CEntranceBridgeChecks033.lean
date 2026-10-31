import UniformK60.CEntranceBridgeData033

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_033 : ∀ i : Fin 32, Valid (batch033[i.val]!) := by decide +kernel
#print axioms checked_033
end UniformK60.CEntranceBridge
