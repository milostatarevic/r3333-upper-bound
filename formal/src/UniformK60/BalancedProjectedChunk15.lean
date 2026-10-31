import UniformK60.BalancedProjectedPrelude

set_option autoImplicit false
namespace UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- This process checks100native cases, including all active matrix edges. -/
theorem chunk_1_5 : ∀ j : Fin 100,
    Structural 1 (chunkIndex 5 j) ∧ MatrixTransport 1 (chunkIndex 5 j) := by
  decide +kernel
#print axioms chunk_1_5
end UniformK60.BalancedProjectedFinite
