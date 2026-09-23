import PricingIntegration.RemainingGCore
import PricingC.GLayoutRefinement

namespace PricingIntegration.RemainingGCore
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingC.GLayoutRefinement
open PricingC.GIsomorphic PricingG.Completion72

def skeleton (d : Fin 72) : CoreBase := eraseCore (base 0 d 0)

theorem base_erase_eq (x : Fin 2) (d y : Fin 72) :
    eraseCore (base x d y) = skeleton d := by
  funext a b
  simp only [eraseCore,skeleton,base]
  split_ifs with heq
  · rfl
  · cases ha : view a with
    | none => cases hb : view b <;> rfl
    | some aa =>
      cases aa with
      | mk sa va =>
        cases hb : view b with
        | none => rfl
        | some bb =>
          cases bb with
          | mk sb vb =>
            cases sa <;> cases sb
            · exact erase_xPalette_reference _ _ _ _
            · rfl
            · rfl
            · exact erase_yPalette_reference _ _ _ _

theorem base_refines_skeleton (x : Fin 2) (d y : Fin 72) :
    Refines (base x d y) (skeleton d) := by
  rw [← base_erase_eq x d y]
  exact erase_refines _

#print axioms base_refines_skeleton
end PricingIntegration.RemainingGCore
