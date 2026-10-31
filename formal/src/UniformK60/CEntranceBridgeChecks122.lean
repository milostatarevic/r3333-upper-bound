import UniformK60.CEntranceBridgeData122

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_122 : ∀ i : Fin 32, Valid (batch122[i.val]!) := by decide +kernel
#print axioms checked_122
end UniformK60.CEntranceBridge
