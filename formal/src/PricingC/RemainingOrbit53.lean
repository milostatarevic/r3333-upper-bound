import PricingC.RemainingOrbit53Data
namespace PricingC.RemainingOrbit53
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- Every native600word candidate reaches an originalretained representative;
all91/105physicalmatrix edges, including internal supports, are transported. -/
theorem complete_matrix_cover : ∀i:Fin 600,∀a b:Fin 15,a≠b →
 matrix (representative (target i)) a b=matrix (candidate i) (coordinate i a) (coordinate i b):=by decide +kernel
#print axioms complete_matrix_cover
end PricingC.RemainingOrbit53
