import PricingC.AnchorTables
import PricingC.PhysicalMask

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore AnchorTables

 theorem generators_injective : Function.Injective generators := by decide

/-- An ordered independent anchor becomes the complete five-neighborhood of
its uniquely determined center; this equivalence keeps its given order. -/
noncomputable def anchorPointEquiv {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present)
    (r : Fin 16) (hr : referenceAnchor m a = R4333.colorNeighborhood m.model 0 r) :
    Fin 5 ≃ ↥(R4333.clebschA (R4333.colorGraph m.model 0) r) := by
  classical
  have hn : R4333.clebschA (R4333.colorGraph m.model 0) r =
      R4333.colorNeighborhood m.model 0 r :=
    R4333.colorGraph_neighborFinset_eq_colorNeighborhood m.model 0 r
  let f : Fin 5 → ↥(R4333.clebschA (R4333.colorGraph m.model 0) r) :=
    fun i => ⟨(a i).val,by
      rw [hn,←hr]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  exact Equiv.ofBijective f ⟨by
    intro i j h
    exact a.injective (Subtype.ext (congrArg (fun z : ↥(R4333.clebschA (R4333.colorGraph m.model 0) r) => z.val) h)),by
    intro v
    have hv : v.val ∈ referenceAnchor m a := by
      simpa only [hn,←hr] using v.property
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
    exact ⟨i,Subtype.ext hi⟩⟩

@[simp] theorem anchorPointEquiv_val {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present)
    (r : Fin 16) (hr : referenceAnchor m a = R4333.colorNeighborhood m.model 0 r) (j : Fin 5) :
    (anchorPointEquiv m a r hr j).val = (a j).val := rfl

/-- Every full actual independent anchor admits a positive-cycle ordering,
without recoloring either the host or the reference palette. -/
theorem completed_anchor_cycle {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present)
    (hind : R4333.IsColorIndependentSet m.model 0 (referenceAnchor m a)) :
    ∃ pi : Fin 5 ≃ Fin 5, ∀ j k, j ≠ k →
      c (m.vertex (a (pi j))) (m.vertex (a (pi k))) = (palette (cycleColor j k)).val := by
  classical
  obtain ⟨r,hr,_⟩ := PricingIntegration.IndependentFive.good_K16_independent_five_unique_center
    m.model m.good 0 (referenceAnchor m a) (referenceAnchor_card m a) hind
  let pts := anchorPointEquiv m a r hr
  obtain ⟨i,e,_,he,hcolor⟩ := ordered_anchor_reference m.model m.good r pts
  refine ⟨cycleOrder i,?_⟩
  intro j k hjk
  rw [m.map_color _ _ (a.injective.ne ((cycleOrder i).injective.ne hjk))]
  have hm := hcolor (generators (cycleOrder i j)) (generators (cycleOrder i k))
    (generators_injective.ne ((cycleOrder i).injective.ne hjk))
  rw [he _,he _] at hm
  change m.model (a (cycleOrder i j)).val (a (cycleOrder i k)).val = _ at hm
  rw [hm,cycleOrder_color i j k hjk]

/-- With a common physical positive-cycle ordering already fixed, the exact
completion is one of the six retained anchored rows. -/
theorem centered_anchor_to_six {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present)
    (r : Fin 16) (hr : referenceAnchor m a = R4333.colorNeighborhood m.model 0 r)
    (hcycle : ∀ j k, j ≠ k → c (m.vertex (a j)) (m.vertex (a k)) = (palette (cycleColor j k)).val) :
    ∃ (i : Fin 6) (e : Fin 16 ≃ Fin 16),
      e 0 = r ∧ (∀ j, e (generators j) = (a j).val) ∧
      ∀ u v, u ≠ v → m.model (e u) (e v) =
        PricingG.Completion72.referenceColor (anchoredIndex i) u v := by
  classical
  let pts := anchorPointEquiv m a r hr
  obtain ⟨i,e,her,he,hcolor⟩ := ordered_anchor_reference m.model m.good r pts
  have hi : HasCycleAnchor i := by
    intro j k hjk
    have hm := hcolor (generators j) (generators k) (generators_injective.ne hjk)
    rw [he _,he _] at hm
    change m.model (a j).val (a k).val = _ at hm
    have hp := hcycle j k hjk
    rw [m.map_color _ _ (a.injective.ne hjk),hm] at hp
    exact palette.injective (Subtype.ext hp)
  obtain ⟨i',hi'⟩ := (anchored_exhaustive i).mp hi
  refine ⟨i',e,her,?_,?_⟩
  · exact fun j => he j
  · simpa only [hi'] using hcolor

/-- With a common physical positive-cycle ordering already fixed, the exact
completion is one of the six retained anchored rows. -/
theorem completed_anchor_to_six {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present)
    (hind : R4333.IsColorIndependentSet m.model 0 (referenceAnchor m a))
    (hcycle : ∀ j k, j ≠ k → c (m.vertex (a j)) (m.vertex (a k)) = (palette (cycleColor j k)).val) :
    ∃ (i : Fin 6) (e : Fin 16 ≃ Fin 16),
      (∀ j, e (generators j) = (a j).val) ∧
      ∀ u v, u ≠ v → m.model (e u) (e v) =
        PricingG.Completion72.referenceColor (anchoredIndex i) u v := by
  classical
  obtain ⟨r,hr,_⟩ := PricingIntegration.IndependentFive.good_K16_independent_five_unique_center
    m.model m.good 0 (referenceAnchor m a) (referenceAnchor_card m a) hind
  let pts := anchorPointEquiv m a r hr
  obtain ⟨i,e,_,he,hcolor⟩ := ordered_anchor_reference m.model m.good r pts
  have hi : HasCycleAnchor i := by
    intro j k hjk
    have hm := hcolor (generators j) (generators k) (generators_injective.ne hjk)
    rw [he _,he _] at hm
    change m.model (a j).val (a k).val = _ at hm
    have hp := hcycle j k hjk
    rw [m.map_color _ _ (a.injective.ne hjk),hm] at hp
    exact palette.injective (Subtype.ext hp)
  obtain ⟨i',hi'⟩ := (anchored_exhaustive i).mp hi
  refine ⟨i',e,?_,?_⟩
  · exact fun j => he j
  · simpa only [hi'] using hcolor

#print axioms completed_anchor_cycle
#print axioms completed_anchor_to_six
end PricingC
