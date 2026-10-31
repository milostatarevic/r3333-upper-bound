import UniformK60.CEntranceBridgeData102

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_102 : ∀ i : Fin 32, Valid (batch102[i.val]!) := by decide +kernel
#print axioms checked_102
end UniformK60.CEntranceBridge
