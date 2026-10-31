import UniformK60.CEntranceBridgeData015

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_015 : ∀ i : Fin 32, Valid (batch015[i.val]!) := by decide +kernel
#print axioms checked_015
end UniformK60.CEntranceBridge
