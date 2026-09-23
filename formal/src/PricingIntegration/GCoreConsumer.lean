import PricingIntegration.RemainingGCore
import PricingC.GScopeAgreement

namespace PricingIntegration.GCoreConsumer
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.LocalRelations PricingIntegration.CoreLayout
open PricingIntegration.RemainingGCore PricingC.GScopeAgreement

def High (c : Host) (phys : Fin 33 ↪ Vertex) : Prop :=
  (∀ a : Fin 16,15 ≤ colorDegree c (palette 1) (phys (xVertex a))) ∧
  (∀ a : Fin 16,15 ≤ colorDegree c (palette 0) (phys (yVertex a)))

def OwnerValid (l : ScopeLayout) : Prop :=
  if l.side then 16 < l.owner.val else 0 < l.owner.val ∧ l.owner.val ≤ 16

instance (l : ScopeLayout) : Decidable (OwnerValid l) := by
  unfold OwnerValid; infer_instance

theorem owner_high (c : Host) (phys : Fin 33 ↪ Vertex) (hh : High c phys)
    (l : ScopeLayout) (ho : OwnerValid l) :
    15 ≤ colorDegree c (palette (omittedColor l.side)) (phys l.owner) := by
  cases hs : l.side with
  | false =>
    have hb : 0 < l.owner.val ∧ l.owner.val ≤ 16 := by simpa only [OwnerValid,hs,Bool.false_eq_true,ite_false] using ho
    let a : Fin 16 := ⟨l.owner.val-1,by omega⟩
    have he : xVertex a = l.owner := by apply Fin.ext; dsimp [xVertex,a]; omega
    simpa only [hs,omittedColor,Bool.false_eq_true,ite_false,he] using hh.1 a
  | true =>
    have hb : 16 < l.owner.val := by simpa only [OwnerValid,hs,ite_true] using ho
    let a : Fin 16 := ⟨l.owner.val-17,by omega⟩
    have he : yVertex a = l.owner := by apply Fin.ext; dsimp [yVertex,a]; omega
    simpa only [hs,omittedColor,ite_true,he] using hh.2 a

theorem empty_core_excludes (c : Host) (hc : NoMonochromaticTriangle c)
    (phys : Fin 33 ↪ Vertex) (base : CoreBase) (hr : Realizes c phys base) (hh : High c phys)
    (l : ScopeLayout) (hl : LayoutValid base l) (ho : OwnerValid l)
    (s : ScopeSpec) (ha : Agrees (spec base l) s) (he : emptyCheck s = true) : False := by
  exact empty_check_excludes c hc (spec base l)
    (physicalScope_of_layout c phys base hr l hl (owner_high c phys hh l ho))
    ((empty_eq _ _ ha).trans he)

theorem conflict_core_excludes (c : Host) (hc : NoMonochromaticTriangle c)
    (phys : Fin 33 ↪ Vertex) (base : CoreBase) (hr : Realizes c phys base) (hh : High c phys)
    (l m : ScopeLayout) (hl : LayoutValid base l) (hm : LayoutValid base m)
    (hol : OwnerValid l) (hom : OwnerValid m)
    (s t : ScopeSpec) (hs : Agrees (spec base l) s) (ht : Agrees (spec base m) t)
    (a b d e : Fin 10) (hab : a ≠ b) (hde : d ≠ e) (q r : Color) (hqr : q ≠ r)
    (hf : forcedCheck s a b q = true) (hg : forcedCheck t d e r = true)
    (hedge : (l.slots a = m.slots d ∧ l.slots b = m.slots e) ∨
       (l.slots a = m.slots e ∧ l.slots b = m.slots d)) : False := by
  apply forced_conflict_excludes c hc (spec base l) (spec base m)
    (physicalScope_of_layout c phys base hr l hl (owner_high c phys hh l hol))
    (physicalScope_of_layout c phys base hr m hm (owner_high c phys hh m hom))
    a b d e hab hde q r hqr
    ((forced_eq _ _ hs a b q).trans hf) ((forced_eq _ _ ht d e r).trans hg)
  rcases hedge with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨congrArg phys ha,congrArg phys hb⟩
  · exact Or.inr ⟨congrArg phys ha,congrArg phys hb⟩

#print axioms empty_core_excludes
#print axioms conflict_core_excludes
end PricingIntegration.GCoreConsumer
