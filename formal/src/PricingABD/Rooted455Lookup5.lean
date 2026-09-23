import PricingABD.Rooted455LookupDefs
namespace PricingABD.Rooted455Lookup
open R4333 PricingABD.Rooted455Data PricingABD.P15PairOrbit PricingABD.P15MatrixTransport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
 theorem rooted_choice_5 : ∀ f : Fin 2, ∀ l u : Fin 10, ∀ a b : Fin 14,a≠b →
      (k15Template (rootTwisted 5) (chosenVertex 5 f l u a) (chosenVertex 5 f l u b)).val =
        (matrix (word (candidate (catalogueIndex 5 f l u))) a b).val := by decide +kernel
#print axioms rooted_choice_5
end PricingABD.Rooted455Lookup
