import UniformK60.CEntranceBridgeData

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open UniformK60.CEntranceSource CompletionC.NativeMatrices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem lookup_0_7 : ∀ i : Fin 100, Eligible 0 (pairIndex 7 i) →
    ∀ j : Fin (pairTable (pairIndex 7 i)).count, Link 0 (pairIndex 7 i) j := by
  decide +kernel
#print axioms lookup_0_7
end UniformK60.CEntranceBridge
