import UniformK60.CEntranceBridgeData084

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_084 : ∀ i : Fin 32, Valid (batch084[i.val]!) := by decide +kernel
#print axioms checked_084
end UniformK60.CEntranceBridge
