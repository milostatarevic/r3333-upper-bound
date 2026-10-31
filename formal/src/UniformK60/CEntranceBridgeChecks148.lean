import UniformK60.CEntranceBridgeData148

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_148 : ∀ i : Fin 32, Valid (batch148[i.val]!) := by decide +kernel
#print axioms checked_148
end UniformK60.CEntranceBridge
