import PricingC.Rooted555Lookup00
import PricingC.Rooted555Lookup01
import PricingC.Rooted555Lookup02
import PricingC.Rooted555Lookup03
import PricingC.Rooted555Lookup04
import PricingC.Rooted555Lookup05
import PricingC.Rooted555Lookup06
import PricingC.Rooted555Lookup07
import PricingC.Rooted555Lookup08
import PricingC.Rooted555Lookup09
import PricingC.Rooted555Lookup10
import PricingC.Rooted555Lookup11
import PricingC.Rooted555Lookup12
import PricingC.Rooted555Lookup13
import PricingC.Rooted555Lookup14
import PricingC.Rooted555Lookup15
import PricingC.Rooted555Lookup16
import PricingC.Rooted555Lookup17
import PricingC.Rooted555Lookup18
import PricingC.Rooted555Lookup19
namespace PricingC.Rooted555
open R4333

theorem all_rooted_choices_in_catalogue (r : Fin 2) (f : Fin 10) : ∀ l u : Fin 10,
 ∀ a b : Fin 15,a≠b →
 (k16Template (rootTwisted r) (chosenVertex r f l u a) (chosenVertex r f l u b)).val =
 (matrix (word (candidate (catalogueIndex r f l u))) a b).val := by
 fin_cases r <;> fin_cases f
 · exact rooted555_lookup00
 · exact rooted555_lookup01
 · exact rooted555_lookup02
 · exact rooted555_lookup03
 · exact rooted555_lookup04
 · exact rooted555_lookup05
 · exact rooted555_lookup06
 · exact rooted555_lookup07
 · exact rooted555_lookup08
 · exact rooted555_lookup09
 · exact rooted555_lookup10
 · exact rooted555_lookup11
 · exact rooted555_lookup12
 · exact rooted555_lookup13
 · exact rooted555_lookup14
 · exact rooted555_lookup15
 · exact rooted555_lookup16
 · exact rooted555_lookup17
 · exact rooted555_lookup18
 · exact rooted555_lookup19

#print axioms all_rooted_choices_in_catalogue
end PricingC.Rooted555
