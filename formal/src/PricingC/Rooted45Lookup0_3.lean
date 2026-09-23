import PricingC.Rooted45Matrix
namespace PricingC.Rooted45Orientation
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem rooted45_lookup0_3 : ∀ j : Fin 50,∀ a b : Fin 14,a≠b →
 matrix false (word (candidate false (target false ⟨150+j.val,by omega⟩))) a b =
 colorBack false (PricingABD.P15MatrixTransport.matrix
 (PricingABD.P15MatrixTransport.word (PricingABD.P15PairOrbit.candidate ⟨150+j.val,by omega⟩))
 (oldIndex false a) (oldIndex false b)) := by decide
end PricingC.Rooted45Orientation
