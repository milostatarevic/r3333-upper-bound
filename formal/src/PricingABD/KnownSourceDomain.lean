import PricingABD.KnownSourceFold
namespace PricingABD.KnownSourceDomain
open PricingIntegration.FoldedThreshold PricingABD.KnownSourceFold
 theorem update_none (k:Known) (p:Nat×Bool) (a:Nat) :
     setKnown k p a=none ↔ a≠p.1 ∧ k a=none := by
   by_cases h:a=p.1
   · simp [setKnown,h]
   · simp [setKnown,h]
 theorem fold_none (facts:List (Nat×Bool)) (k:Known) (a:Nat) :
     facts.foldl setKnown k a=none ↔ k a=none ∧ ∀p∈facts,a≠p.1 := by
   induction facts generalizing k with
   | nil => simp
   | cons p ps ih =>
     rw [List.foldl_cons,ih,update_none]
     simp only [List.mem_cons,forall_eq_or_imp]
     tauto
 theorem unknown_eq_of_domain (k₁ k₂:Known)
     (h:∀a,k₁ a=none ↔ k₂ a=none) (xs:List Lit) : unknown k₁ xs=unknown k₂ xs := by
   unfold unknown
   apply List.filter_congr
   intro l _
   have hh:=h l.2
   cases h₁:k₁ l.2 <;> cases h₂:k₂ l.2 <;> simp_all [knownValue]
 theorem folded_sources_same_keys (f₁ f₂:List (Nat×Bool))
     (h: f₁.map Prod.fst=f₂.map Prod.fst) (xs:List Lit) :
     unknown (f₁.foldl setKnown (fun _=>none)) xs =
       unknown (f₂.foldl setKnown (fun _=>none)) xs := by
   apply unknown_eq_of_domain
   intro a
   simp only [fold_none,true_and]
   constructor
   · intro h₁ p hp he
     have ha:a∈f₂.map Prod.fst := by rw [he];exact List.mem_map.mpr ⟨p,hp,rfl⟩
     rw [←h] at ha
     obtain ⟨q,hq,hqa⟩:=List.mem_map.mp ha
     exact h₁ q hq hqa.symm
   · intro h₂ p hp he
     have ha:a∈f₁.map Prod.fst := by rw [he];exact List.mem_map.mpr ⟨p,hp,rfl⟩
     rw [h] at ha
     obtain ⟨q,hq,hqa⟩:=List.mem_map.mp ha
     exact h₂ q hq hqa.symm
#print axioms folded_sources_same_keys
end PricingABD.KnownSourceDomain
