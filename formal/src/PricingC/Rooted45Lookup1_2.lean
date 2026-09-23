import PricingC.Rooted45Matrix
namespace PricingC.Rooted45Orientation
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem rooted45_lookup1_2 : ∀ j : Fin 50,∀ a b : Fin 14,a≠b →
 matrix true (word (candidate true (target true ⟨100+j.val,by omega⟩))) a b =
 colorBack true (PricingABD.P15MatrixTransport.matrix
 (PricingABD.P15MatrixTransport.word (PricingABD.P15PairOrbit.candidate ⟨100+j.val,by omega⟩))
 (oldIndex true a) (oldIndex true b)) := by decide
end PricingC.Rooted45Orientation
