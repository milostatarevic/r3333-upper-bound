import PricingC.Rooted555Matrix

namespace PricingC.Rooted555
open R4333
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rooted555_lookup03 : ∀ l u : Fin 10,∀ a b : Fin 15,a≠b →
 (k16Template (rootTwisted 0) (chosenVertex 0 3 l u a) (chosenVertex 0 3 l u b)).val =
 (matrix (word (candidate (catalogueIndex 0 3 l u))) a b).val := by decide

end PricingC.Rooted555
