import UniformK60.BalancedProjectedPrelude

set_option autoImplicit false
namespace UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- This process checks100native cases, including all active matrix edges. -/
theorem chunk_7_0 : ∀ j : Fin 100,
    Structural 7 (chunkIndex 0 j) ∧ MatrixTransport 7 (chunkIndex 0 j) := by
  decide +kernel
#print axioms chunk_7_0
end UniformK60.BalancedProjectedFinite
