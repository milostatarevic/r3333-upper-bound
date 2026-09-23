import PricingABD.Rooted455Lookup0
import PricingABD.Rooted455Lookup1
import PricingABD.Rooted455Lookup2
import PricingABD.Rooted455Lookup3
import PricingABD.Rooted455Lookup4
import PricingABD.Rooted455Lookup5
import PricingABD.Rooted455Lookup6
import PricingABD.Rooted455Lookup7
import PricingABD.Rooted455Lookup8
import PricingABD.Rooted455Lookup9
namespace PricingABD.Rooted455Lookup
open R4333 PricingABD.Rooted455Data PricingABD.P15PairOrbit PricingABD.P15MatrixTransport
 theorem all_rooted_choices_in_exact_catalogue (r : Fin 10) : ∀ f : Fin 2, ∀ l u : Fin 10, ∀ a b : Fin 14,a≠b →
      (k15Template (rootTwisted r) (chosenVertex r f l u a) (chosenVertex r f l u b)).val =
        (matrix (word (candidate (catalogueIndex r f l u))) a b).val := by
  fin_cases r
  · exact rooted_choice_0
  · exact rooted_choice_1
  · exact rooted_choice_2
  · exact rooted_choice_3
  · exact rooted_choice_4
  · exact rooted_choice_5
  · exact rooted_choice_6
  · exact rooted_choice_7
  · exact rooted_choice_8
  · exact rooted_choice_9

#print axioms all_rooted_choices_in_exact_catalogue
end PricingABD.Rooted455Lookup
