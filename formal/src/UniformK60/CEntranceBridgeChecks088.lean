import UniformK60.CEntranceBridgeData088

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_088 : ∀ i : Fin 32, Valid (batch088[i.val]!) := by decide +kernel
#print axioms checked_088
end UniformK60.CEntranceBridge
