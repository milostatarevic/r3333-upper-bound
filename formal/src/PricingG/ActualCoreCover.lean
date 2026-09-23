import PricingG.RemainingCoreTransport

namespace PricingG
open Ramsey61 Ramsey61.CEncodingCore PricingC
open PricingIntegration.CoreLayout

/-- The exact opposite-high condition used at every selected retained scope. -/
def CoreHigh (c : Host) (phys : Fin 33 ↪ Vertex) : Prop :=
  ∀ (u : Fin 33) (side : Bool) (a : Fin 16),
    PricingIntegration.RemainingGCore.view u = some (side,a) →
    15 ≤ colorDegree c (palette (omittedColor side)) (phys u)

theorem coreHigh_of_blocks (c : Host) (phys : Fin 33 ↪ Vertex)
    (hX : ∀ i, 15 ≤ colorDegree c (palette 1) (phys (coreX i)))
    (hY : ∀ i, 15 ≤ colorDegree c (palette 0) (phys (coreY i))) : CoreHigh c phys := by
  intro u side a hu
  rcases coreIndex_cases u with rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [PricingIntegration.RemainingGCore.view_root] at hu
    contradiction
  · rw [remaining_view_X] at hu
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hu)
    exact hX i
  · rw [remaining_view_Y] at hu
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hu)
    exact hY i

def CoreCovered (c : Host) : Prop :=
  (∃ (kind : Fin 2) (y : Fin 72) (g : Fin 25) (phys : Fin 33 ↪ Vertex),
    Realizes c phys (GIsomorphic.baseCore kind y g) ∧ CoreHigh c phys) ∨
  (∃ (kind : Fin 2) (d y : Fin 72) (phys : Fin 33 ↪ Vertex),
    Realizes c phys (PricingIntegration.RemainingGCore.base kind d y) ∧ CoreHigh c phys)

/-- The exhaustive physical finite-case cover, with both concrete retained
base functions. All mathematical graph and label reductions are proved. -/
theorem canonical_guard_supplies_core (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hG : RegularOverlapGuard c r (palette 0) (palette 1)) : CoreCovered c := by
  obtain ⟨m⟩ := regular_overlap_has_graph_model c hc r (palette 0) (palette 1) hG
  have hd : GraphRootedDichotomy m.K m.J m.imageRule := m.shared_graph_rooted_dichotomy hc hG
  rcases GParity.defectCount_zero_or_sixteen m.K m.J m.K_srg m.J_srg m.imageRule hd with hz | hz
  · obtain ⟨kind,y,g,phys,hr,hX,hY⟩ := isomorphic_core_realized c hc r hG m hz
    exact Or.inl ⟨kind,y,g,phys,hr,coreHigh_of_blocks c phys hX hY⟩
  · obtain ⟨kind,d,y,phys,hr,hX,hY⟩ := remaining_core_realized c hc r hG m hz
    exact Or.inr ⟨kind,d,y,phys,hr,coreHigh_of_blocks c phys hX hY⟩

/-- Arbitrary physical color names are handled by one whole-host palette
permutation, retaining the same61 vertices. -/
theorem regular_overlap_supplies_core (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (p q : FourColor) (hG : RegularOverlapGuard c r p q) :
    ∃ σ : Equiv.Perm FourColor, σ (palette 0) = p ∧ σ (palette 1) = q ∧
      NoMonochromaticTriangle (colorRelabel c σ) ∧ CoreCovered (colorRelabel c σ) := by
  obtain ⟨σ,hp,hq,hc',hG'⟩ := exists_canonical_guard c hc r p q hG
  exact ⟨σ,hp,hq,hc',canonical_guard_supplies_core (colorRelabel c σ) hc' r hG'⟩

#print axioms canonical_guard_supplies_core
#print axioms regular_overlap_supplies_core
end PricingG
