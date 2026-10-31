import UniformK60.CEntranceBridgeData028

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_028 : ∀ i : Fin 32, Valid (batch028[i.val]!) := by decide +kernel
#print axioms checked_028
end UniformK60.CEntranceBridge
