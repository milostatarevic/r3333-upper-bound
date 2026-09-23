import PricingC.GRelations
import PricingC.GLayoutSkeleton

namespace PricingC.GScopeAgreement
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.LocalRelations

def Agrees (s t : ScopeSpec) : Prop :=
 (∀ a,s.roles a=t.roles a) ∧ (∀ q,s.colors q=t.colors q) ∧
 ∀ a b,a<b → s.observed a b=t.observed a b

instance (s t : ScopeSpec) : Decidable (Agrees s t) :=
 inferInstanceAs (Decidable ((∀ a,s.roles a=t.roles a) ∧ (∀ q,s.colors q=t.colors q) ∧
 ∀ a b,a<b → s.observed a b=t.observed a b))

theorem predicted_eq (s t : ScopeSpec) (h : Agrees s t) (i : Fin 72) (a b : Fin 10) :
 predicted s i a b=predicted t i a b := by
 unfold predicted
 rw [h.1 a,h.1 b,h.2.1]

theorem compatible_iff (s t : ScopeSpec) (h : Agrees s t) (i : Fin 72) :
 Compatible s i ↔ Compatible t i := by
 constructor
 · intro hc a b hab
   rw [←h.2.2 a b hab,←predicted_eq s t h]
   exact hc a b hab
 · intro hc a b hab
   rw [h.2.2 a b hab,predicted_eq s t h]
   exact hc a b hab

theorem rows_eq (s t : ScopeSpec) (h : Agrees s t) : rows s=rows t := by
 unfold rows
 congr 1
 funext i
 by_cases hs : Compatible s i
 · have ht := (compatible_iff s t h i).mp hs
   simp only [decide_eq_true hs,decide_eq_true ht]
 · have ht : ¬ Compatible t i := fun ht => hs ((compatible_iff s t h i).mpr ht)
   simp only [decide_eq_false hs,decide_eq_false ht]

theorem empty_eq (s t : ScopeSpec) (h : Agrees s t) : emptyCheck s=emptyCheck t := by
 unfold emptyCheck
 rw [rows_eq s t h]

theorem forced_eq (s t : ScopeSpec) (h : Agrees s t) (a b : Fin 10) (q : Color) :
 forcedCheck s a b q=forcedCheck t a b q := by
 unfold forcedCheck
 rw [rows_eq s t h]
 congr 1
 funext i
 rw [predicted_eq s t h]

end PricingC.GScopeAgreement
