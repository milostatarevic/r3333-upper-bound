import UniformK60.CEntranceBridgeData051

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_051 : ∀ i : Fin 32, Valid (batch051[i.val]!) := by decide +kernel
#print axioms checked_051
end UniformK60.CEntranceBridge
