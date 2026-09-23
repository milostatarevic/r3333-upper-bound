import PricingABD.TemplateNormalization

set_option autoImplicit false

namespace PricingIntegration.FixedPhysicalNeighborhood
open Ramsey61 Ramsey61.ClassificationAdapter

/-- The displayed palette is only a coordinate change of one actual
neighborhood; the61-vertex host coloring itself is never changed. -/
def modelInPalette {n : Nat} {c : Host} {r : Fin 61} {q : FourColor}
    {template : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r q template)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) : R4333.EdgeColoring (Fin n) (Fin 3) :=
  R4333.mapEdgeColors template (m.colors.trans pal.symm)

noncomputable def mapOfNormalization {n : Nat} {c : Host} {r : Fin 61} {q : FourColor}
    {template target : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r q template)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q})
    (e : Fin n ≃ Fin n)
    (he : ∀ u v,u ≠ v → modelInPalette m pal (e u) (e v) = target u v) :
    PhysicalNeighborhoodMap c r q target where
  vertex := e.toEmbedding.trans m.vertex
  mem_neighborhood i := m.mem_neighborhood (e i)
  covers_neighborhood := by
    intro v hv
    obtain ⟨i,hi⟩ := m.covers_neighborhood v hv
    refine ⟨e.symm i,?_⟩
    simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using hi
  colors := pal
  map_color := by
    intro u v huv
    have hm := m.map_color (e u) (e v) (e.injective.ne huv)
    have hc := he u v huv
    change pal.symm (m.colors (template (e u) (e v))) = target u v at hc
    have hp : m.colors (template (e u) (e v)) = pal (target u v) := by
      rw [←hc,Equiv.apply_symm_apply]
    exact hm.trans (congrArg Subtype.val hp)

theorem physical_k15_fixed_palette (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (hd : colorDegree c q r = 15)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ t : Bool,∃ m : PhysicalNeighborhoodMap c r q (R4333.k15Template t),m.colors = pal := by
  obtain ⟨template,ht,⟨m⟩⟩ := physical_neighborhood_k15 c hc r q hd
  have hg : R4333.NoMonochromaticTriangle (modelInPalette m pal) :=
    R4333.noMono_mapEdgeColors _ _ (R4333.k15CriticalCatalogue_complete.1 template ht)
  obtain ⟨t,e,he⟩ := PricingABD.TemplateNormalization.k15_color_preserving_complete _ hg
  exact ⟨t,mapOfNormalization m pal e he,rfl⟩

theorem physical_k16_fixed_palette (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (hd : colorDegree c q r = 16)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ t : Bool,∃ m : PhysicalNeighborhoodMap c r q (R4333.k16Template t),m.colors = pal := by
  obtain ⟨template,ht,⟨m⟩⟩ := physical_neighborhood_k16 c hc r q hd
  have hg : R4333.NoMonochromaticTriangle (modelInPalette m pal) :=
    R4333.noMono_mapEdgeColors _ _ (R4333.k16CriticalCatalogue_complete.1 template ht)
  obtain ⟨t,e,he⟩ := PricingABD.TemplateNormalization.k16_color_preserving_complete _ hg
  exact ⟨t,mapOfNormalization m pal e he,rfl⟩

/-- Every chosen physical vertex of a16-cell can occupy retained label15,
with all host colors and all vertices preserved. -/
theorem physical_k16_marked_fixed_palette (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (hd : colorDegree c q r = 16)
    (mark : Fin 61) (hmark : mark ∈ colorNeighborhood c q r)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ t : Bool,∃ m : PhysicalNeighborhoodMap c r q (R4333.k16Template t),
      m.colors = pal ∧ m.vertex 15 = mark := by
  obtain ⟨template,ht,⟨m⟩⟩ := physical_neighborhood_k16 c hc r q hd
  obtain ⟨i,hi⟩ := m.covers_neighborhood mark hmark
  have hg : R4333.NoMonochromaticTriangle (modelInPalette m pal) :=
    R4333.noMono_mapEdgeColors _ _ (R4333.k16CriticalCatalogue_complete.1 template ht)
  obtain ⟨t,e,hroot,he⟩ := PricingABD.TemplateNormalization.k16_rooted_color_preserving_complete _ hg i
  refine ⟨t,mapOfNormalization m pal e he,rfl,?_⟩
  change m.vertex (e 15) = mark
  rw [hroot,hi]

#print axioms physical_k15_fixed_palette
#print axioms physical_k16_marked_fixed_palette
end PricingIntegration.FixedPhysicalNeighborhood
