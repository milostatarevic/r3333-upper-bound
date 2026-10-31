import UniformK60.CEntranceBridgeData034

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_034 : ∀ i : Fin 32, Valid (batch034[i.val]!) := by decide +kernel
#print axioms checked_034
end UniformK60.CEntranceBridge
