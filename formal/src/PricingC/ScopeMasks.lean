import PricingC.ScopeModels
import PricingC.CanonicalGraph

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter

/-- A full five-neighbor anchor has only the center mask or a two-point mask
at any point outside the anchor. This is the exact 16,5,0,2 incidence law. -/
theorem model_neighborhood_mask (d : R4333.EdgeColoring (Fin 16) (Fin 3))
    (hd : R4333.NoMonochromaticTriangle d) (q : Fin 3) (r y : Fin 16)
    (hy : y ∉ R4333.colorNeighborhood d q r) :
    ((R4333.colorNeighborhood d q r).filter (fun a => d a y = q)).card = 2 ∨
    ((R4333.colorNeighborhood d q r).filter (fun a => d a y = q)).card = 5 := by
  classical
  let G := R4333.colorGraph d q
  have hs := R4333.k16_colorGraph_isSRG d hd q
  by_cases hyr : y = r
  · subst y
    right
    have heq : (R4333.colorNeighborhood d q r).filter (fun a => d a r = q) =
        R4333.colorNeighborhood d q r := by
      apply Finset.filter_eq_self.mpr
      intro a ha
      have hc := (R4333.mem_colorNeighborhood d q r a).mp ha
      exact (d.color_symm a r).trans hc.2
    rw [heq]
    exact R4333.threeColor_degree_eq_five_at_16 d hd q r
  · left
    have hn : ¬G.Adj r y := by
      simpa [G,R4333.colorGraph,R4333.mem_colorNeighborhood,ne_comm] using hy
    have hh := hs.of_not_adj (Ne.symm hyr) hn
    have heq : (R4333.colorNeighborhood d q r).filter (fun a => d a y = q) =
        (G.commonNeighbors r y).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
      constructor
      · rintro ⟨ha,hcol⟩
        have hr := (R4333.mem_colorNeighborhood d q r a).mp ha
        have hay : a ≠ y := by intro e; exact hy (e ▸ ha)
        exact ⟨⟨hr.1.symm,hr.2⟩,⟨hay.symm,(d.color_symm y a).trans hcol⟩⟩
      · rintro ⟨hra,hya⟩
        exact ⟨(R4333.mem_colorNeighborhood d q r a).mpr ⟨hra.1.symm,hra.2⟩,
          (d.color_symm a y).trans hya.2⟩
    rw [heq]
    simpa only [Set.toFinset_card] using hh

/-- Pull an ordered actual anchor back into a completed scope. -/
def referenceAnchor {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present) : Finset (Fin 16) :=
  Finset.univ.image (fun i => (a i).val)

theorem referenceAnchor_card {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present) :
    (referenceAnchor m a).card = 5 := by
  rw [referenceAnchor,Finset.card_image_iff.mpr]
  · simp
  · exact fun i _ j _ h => a.injective (Subtype.ext h)

theorem referenceAnchor_independent {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present) (q : Fin 3)
    (hind : ∀ i j, i ≠ j → c (m.vertex (a i)) (m.vertex (a j)) ≠ (palette q).val) :
    R4333.IsColorIndependentSet m.model q (referenceAnchor m a) := by
  intro u hu v hv huv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
  have hij : i ≠ j := by intro e; exact huv (congrArg (fun k => (a k).val) e)
  intro hq
  apply hind i j hij
  rw [m.map_color _ _ (a.injective.ne hij),hq]

/-- Physical mask transport preserves every literal and uses only present
reference positions. The unique center may itself be the omitted point. -/
theorem ordered_physical_mask {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present) (q : Fin 3)
    (y : m.present) (hout : ∀ i, a i ≠ y)
    (r : Fin 16) (hr : referenceAnchor m a = R4333.colorNeighborhood m.model q r) :
    (Finset.univ.filter (fun i => c (m.vertex (a i)) (m.vertex y) = (palette q).val)).card = 2 ∨
    (Finset.univ.filter (fun i => c (m.vertex (a i)) (m.vertex y) = (palette q).val)).card = 5 := by
  classical
  have hy : y.val ∉ R4333.colorNeighborhood m.model q r := by
    rw [←hr]
    intro hmem
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
    exact hout i (Subtype.ext hi)
  have hf : ∀ i, c (m.vertex (a i)) (m.vertex y) = (palette q).val ↔
      m.model (a i).val y.val = q := by
    intro i
    rw [m.map_color _ _ (hout i)]
    exact ⟨fun h => palette.injective (Subtype.ext h),fun h => congrArg (fun z => (palette z).val) h⟩
  have hcard : (Finset.univ.filter (fun i => c (m.vertex (a i)) (m.vertex y) = (palette q).val)).card =
      ((R4333.colorNeighborhood m.model q r).filter (fun z => m.model z y.val = q)).card := by
    apply Finset.card_bij (fun i _ => (a i).val)
    · intro i hi
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
      refine Finset.mem_filter.mpr ⟨?_,(hf i).mp hi⟩
      rw [←hr]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    · intro i _ j _ h
      exact a.injective (Subtype.ext h)
    · intro z hz
      obtain ⟨hz,hcol⟩ := Finset.mem_filter.mp hz
      rw [←hr] at hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hf i).mpr hcol⟩,rfl⟩
  rw [hcard]
  exact model_neighborhood_mask m.model m.good q r y.val hy

#print axioms model_neighborhood_mask
#print axioms ordered_physical_mask
end PricingC
