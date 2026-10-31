import PricingABD.TemplateNormalization
import UniformK60.ClassificationAdapter

set_option autoImplicit false

namespace UniformK60.ClassificationFixedPalette
open Ramsey61 UniformK60.ClassificationAdapter

/-- The displayed palette is only a coordinate change of one actual
neighborhood; the 60-vertex host coloring itself is never changed. -/
def modelInPalette {n : Nat} {c : Host} {r : Fin 60} {q : FourColor}
    {template : R4333.EdgeColoring (Fin n) (Fin 3)}
    (m : PhysicalNeighborhoodMap c r q template)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) : R4333.EdgeColoring (Fin n) (Fin 3) :=
  R4333.mapEdgeColors template (m.colors.trans pal.symm)

noncomputable def mapOfNormalization {n : Nat} {c : Host} {r : Fin 60} {q : FourColor}
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
    (r : Fin 60) (q : FourColor) (hd : colorDegree c q r = 15)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ t : Bool,∃ m : PhysicalNeighborhoodMap c r q (R4333.k15Template t),m.colors = pal := by
  obtain ⟨template,ht,⟨m⟩⟩ := physical_neighborhood_k15 c hc r q hd
  have hg : R4333.NoMonochromaticTriangle (modelInPalette m pal) :=
    R4333.noMono_mapEdgeColors _ _ (R4333.k15CriticalCatalogue_complete.1 template ht)
  obtain ⟨t,e,he⟩ := PricingABD.TemplateNormalization.k15_color_preserving_complete _ hg
  exact ⟨t,mapOfNormalization m pal e he,rfl⟩

theorem physical_k16_fixed_palette (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hd : colorDegree c q r = 16)
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
    (r : Fin 60) (q : FourColor) (hd : colorDegree c q r = 16)
    (mark : Fin 60) (hmark : mark ∈ colorNeighborhood c q r)
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

/-- The fixed K15 model is the literal restriction of its K16 model. -/
theorem k15Template_castSucc (t : Bool) (i j : Fin 15) :
    R4333.k15Template t i j = R4333.k16Template t i.castSucc j.castSucc := by
  cases t <;> rfl

/-- Every critical neighborhood embeds in a full reference template in the
specified palette. No reference position is asserted to be a host vertex. -/
theorem physical_high_embedding (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hh : 15 ≤ colorDegree c q r)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ t : Bool, ∃ f : {v // v ∈ colorNeighborhood c q r} ↪ Fin 16,
      ∀ u v, u ≠ v → c u.val v.val = (pal (R4333.k16Template t (f u) (f v))).val := by
  have upper := fourColor_colorDegree_le_sixteen c hc q r
  have cases : colorDegree c q r = 15 ∨ colorDegree c q r = 16 := by omega
  rcases cases with h15 | h16
  · obtain ⟨t, m, hm⟩ := physical_k15_fixed_palette c hc r q h15 pal
    let e := m.neighborhoodEquiv
    let f : {v // v ∈ colorNeighborhood c q r} ↪ Fin 16 :=
      e.symm.toEmbedding.trans ⟨Fin.castSucc, Fin.castSucc_injective 15⟩
    refine ⟨t, f, ?_⟩
    intro u v huv
    have h := m.map_color (e.symm u) (e.symm v) (e.symm.injective.ne huv)
    have hu : m.vertex (e.symm u) = u.val := congrArg Subtype.val (e.apply_symm_apply u)
    have hv : m.vertex (e.symm v) = v.val := congrArg Subtype.val (e.apply_symm_apply v)
    rw [hu, hv, hm, k15Template_castSucc] at h
    exact h
  · obtain ⟨t, m, hm⟩ := physical_k16_fixed_palette c hc r q h16 pal
    let e := m.neighborhoodEquiv
    refine ⟨t, e.symm.toEmbedding, ?_⟩
    intro u v huv
    have h := m.map_color (e.symm u) (e.symm v) (e.symm.injective.ne huv)
    have hu : m.vertex (e.symm u) = u.val := congrArg Subtype.val (e.apply_symm_apply u)
    have hv : m.vertex (e.symm v) = v.val := congrArg Subtype.val (e.apply_symm_apply v)
    simpa only [hu, hv, hm, Equiv.toEmbedding_apply] using h

/-- Restricting a critical neighborhood embedding gives all visible-subset
embeddings without assigning positions to any unseen physical vertices. -/
theorem physical_subset_embeds (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hh : 15 ≤ colorDegree c q r)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q})
    (S : Finset (Fin 60)) (hS : S ⊆ colorNeighborhood c q r) :
    ∃ t : Bool, ∃ f : {v // v ∈ S} ↪ Fin 16,
      ∀ u v, u ≠ v → c u.val v.val = (pal (R4333.k16Template t (f u) (f v))).val := by
  obtain ⟨t, f, hf⟩ := physical_high_embedding c hc r q hh pal
  let inc : {v // v ∈ S} ↪ {v // v ∈ colorNeighborhood c q r} :=
    ⟨fun v => ⟨v.val, hS v.property⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun x : {v // v ∈ colorNeighborhood c q r} => x.val) h)⟩
  exact ⟨t, inc.trans f, fun u v huv => hf (inc u) (inc v) (inc.injective.ne huv)⟩

#print axioms physical_k15_fixed_palette
#print axioms physical_k16_marked_fixed_palette
end UniformK60.ClassificationFixedPalette
