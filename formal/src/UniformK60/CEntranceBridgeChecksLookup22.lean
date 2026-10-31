import UniformK60.CEntranceBridgeData

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open UniformK60.CEntranceSource CompletionC.NativeMatrices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem lookup_2_2 : ∀ i : Fin 100, Eligible 2 (pairIndex 2 i) →
    ∀ j : Fin (pairTable (pairIndex 2 i)).count, Link 2 (pairIndex 2 i) j := by
  decide +kernel
#print axioms lookup_2_2
end UniformK60.CEntranceBridge
