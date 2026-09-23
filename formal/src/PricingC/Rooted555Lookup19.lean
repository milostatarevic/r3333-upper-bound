import PricingC.Rooted555Matrix

namespace PricingC.Rooted555
open R4333
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rooted555_lookup19 : ∀ l u : Fin 10,∀ a b : Fin 15,a≠b →
 (k16Template (rootTwisted 1) (chosenVertex 1 9 l u a) (chosenVertex 1 9 l u b)).val =
 (matrix (word (candidate (catalogueIndex 1 9 l u))) a b).val := by decide

end PricingC.Rooted555
