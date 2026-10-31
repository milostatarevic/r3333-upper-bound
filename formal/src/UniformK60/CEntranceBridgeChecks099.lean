import UniformK60.CEntranceBridgeData099

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A bounded32-case kernel check of full bijections and signed facts. -/
theorem checked_099 : ∀ i : Fin 32, Valid (batch099[i.val]!) := by decide +kernel
#print axioms checked_099
end UniformK60.CEntranceBridge
