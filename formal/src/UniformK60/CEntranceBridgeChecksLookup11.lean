import UniformK60.CEntranceBridgeData

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open UniformK60.CEntranceSource CompletionC.NativeMatrices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem lookup_1_1 : ∀ i : Fin 100, Eligible 1 (pairIndex 1 i) →
    ∀ j : Fin (pairTable (pairIndex 1 i)).count, Link 1 (pairIndex 1 i) j := by
  decide +kernel
#print axioms lookup_1_1
end UniformK60.CEntranceBridge
