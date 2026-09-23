import PricingG.ActualCoreCover
import PricingIntegration.GCoreConsumer

namespace PricingG
open Ramsey61 Ramsey61.CEncodingCore PricingC
open PricingIntegration.CoreLayout PricingIntegration.GCoreConsumer

/-- The proved physical high conditions in the finite consumer's literal
X/Y index convention. -/
theorem coreHigh_consumer (c : Host) (phys : Fin 33 ↪ Vertex) (hh : CoreHigh c phys) : High c phys := by
  constructor
  · intro a
    exact hh _ false a (PricingIntegration.RemainingGCore.view_x a)
  · intro a
    exact hh _ true a (PricingIntegration.RemainingGCore.view_y a)

def ConsumerCoreCovered (c : Host) : Prop :=
  (∃ (kind : Fin 2) (y : Fin 72) (g : Fin 25) (phys : Fin 33 ↪ Vertex),
    Realizes c phys (GIsomorphic.baseCore kind y g) ∧ High c phys) ∨
  (∃ (kind : Fin 2) (d y : Fin 72) (phys : Fin 33 ↪ Vertex),
    Realizes c phys (PricingIntegration.RemainingGCore.base kind d y) ∧ High c phys)

theorem coreCovered_consumer (c : Host) (hh : CoreCovered c) : ConsumerCoreCovered c := by
  rcases hh with ⟨k,y,g,phys,hr,hh⟩ | ⟨k,d,y,phys,hr,hh⟩
  · exact Or.inl ⟨k,y,g,phys,hr,coreHigh_consumer c phys hh⟩
  · exact Or.inr ⟨k,d,y,phys,hr,coreHigh_consumer c phys hh⟩

theorem canonical_guard_supplies_consumer (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hG : RegularOverlapGuard c r (palette 0) (palette 1)) : ConsumerCoreCovered c :=
  coreCovered_consumer c (canonical_guard_supplies_core c hc r hG)

theorem regular_overlap_supplies_consumer (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (p q : FourColor) (hG : RegularOverlapGuard c r p q) :
    ∃ σ : Equiv.Perm FourColor, σ (palette 0) = p ∧ σ (palette 1) = q ∧
      NoMonochromaticTriangle (colorRelabel c σ) ∧ ConsumerCoreCovered (colorRelabel c σ) := by
  obtain ⟨σ,hp,hq,hc',hh⟩ := regular_overlap_supplies_core c hc r p q hG
  exact ⟨σ,hp,hq,hc',coreCovered_consumer (colorRelabel c σ) hh⟩

#print axioms regular_overlap_supplies_consumer
end PricingG
