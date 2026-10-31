import UniformK60.CEntranceBridgeData

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open UniformK60.CEntranceSource CompletionC.NativeMatrices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem lookup_2_4 : ∀ i : Fin 100, Eligible 2 (pairIndex 4 i) →
    ∀ j : Fin (pairTable (pairIndex 4 i)).count, Link 2 (pairIndex 4 i) j := by
  decide +kernel
#print axioms lookup_2_4
end UniformK60.CEntranceBridge
