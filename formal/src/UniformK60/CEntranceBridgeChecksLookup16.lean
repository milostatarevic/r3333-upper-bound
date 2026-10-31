import UniformK60.CEntranceBridgeData

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open UniformK60.CEntranceSource CompletionC.NativeMatrices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem lookup_1_6 : ∀ i : Fin 100, Eligible 1 (pairIndex 6 i) →
    ∀ j : Fin (pairTable (pairIndex 6 i)).count, Link 1 (pairIndex 6 i) j := by
  decide +kernel
#print axioms lookup_1_6
end UniformK60.CEntranceBridge
