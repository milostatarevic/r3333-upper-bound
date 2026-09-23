import PricingC.RemainingOrbit24Data
namespace PricingC.RemainingOrbit24
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- Bind the exact selected normalizer used by the complete737pair action data.
The retained table was already covered by an earlier theorem with another selection. -/
theorem complete_matrix_cover : ∀i:Fin 600,∀a b:Fin 14,a≠b →
 matrix (representative (target i)) a b=matrix (candidate i) (coordinate i a) (coordinate i b):=by decide +kernel
#print axioms complete_matrix_cover
end PricingC.RemainingOrbit24
