import UniformK60.CEntranceBridgeData093

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_093 : ∀ i : Fin 32, Valid (batch093[i.val]!) := by decide +kernel
#print axioms checked_093
end UniformK60.CEntranceBridge
