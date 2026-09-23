import PricingABD.ABPhysicalBounds

set_option autoImplicit false
namespace PricingABD.ABNumericBounds
open Ramsey61 Ramsey61.CEncodingCore Finset PricingABD.ABLayout PricingABD.ABPhysicalBounds
 theorem free_bounds {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (i : Fin (freeSize l)) (q : Fin 4) (hq : q≠0) :
    11≤tailCount f (ABLayout.free l i) 0 ∧ tailCount f (ABLayout.free l i) 0≤15 ∧
    7≤tailCount f (ABLayout.free l i) q ∧ tailCount f (ABLayout.free l i) q≤27-lowSize l ∧
    22≤tailCount f (ABLayout.free l i) 0+tailCount f (ABLayout.free l i) q := by
  simp only [tailCount_eq]
  have h := free_vertex_tail_intervals c hc f.root (palette 0) (f.vertex (ABLayout.free l i)) (free_mem f i)
    (palette q) (palette_injective.ne hq)
  rw [f.low_degree]at h
  omega
 theorem tail_nonzero_bounds {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (i : Fin (tailSize l)) (q : Fin 4) (hq : q≠0) :
    6≤tailCount f (ABLayout.tail l i) q ∧ (q≠owner l (ABLayout.tail l i) → 7≤tailCount f (ABLayout.tail l i) q) := by
  rw [tailCount_eq]
  have h := tail_vertex_nonzero_degree_lower c hc f.root (palette 0) (f.vertex (ABLayout.tail l i)) (palette q) (palette_injective.ne hq)
  refine ⟨h.1,?_⟩
  intro hqown
  exact h.2 (by rw [f.spokes];exact palette_injective.ne hqown)
 theorem tail_zero_bound {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (i : Fin (tailSize l)) :
    12+freeSize l-lowSize l≤retainedDegree f (ABLayout.tail l i) 0 := by
  have h := tail_vertex_retained_low_degree c hc f.root (palette 0) (f.vertex (ABLayout.tail l i)) (tail_mem f i)
    (support f) (support_subset f)
  rw [support_card,f.low_degree,←retained_eq]at h
  change 12+freeSize l≤retainedDegree f (ABLayout.tail l i) 0+lowSize l at h
  omega
 theorem surviving_high_count {c : Host} {l : Layout} (f : Frame c l) :
    tailSize l+freeSize l-lowSize l≤(Incoming c f.root ∩ retained f).card := by
  have h:=genuine_high_retention_count c f.root (palette 0) (support f) (support_subset f)
  rw [support_card,f.low_degree,←retained_eq] at h
  have hs:=f.selected
  omega
 theorem high_free_proxy {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (i : Fin (freeSize l))
    (hi : f.vertex (ABLayout.free l i) ∈ Incoming c f.root) : 14≤tailCount f (ABLayout.free l i) 0 := by
  have hh := ((mem_highOwnNeighborSupport _ _ _).mp hi).2
  rw [f.spokes,ABLayout.owner_free]at hh
  rw [tailCount_eq]
  exact genuine_high_free_vertex_proxy c hc f.root (palette 0) _ (free_mem f i) hh
 theorem high_tail_proxy {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (i : Fin (tailSize l))
    (hi : f.vertex (ABLayout.tail l i) ∈ Incoming c f.root) : 9≤tailCount f (ABLayout.tail l i) (owner l (ABLayout.tail l i)) := by
  have h := genuine_high_tail_vertex_proxy c hc f.root (palette 0) _ (tail_mem f i) hi
  rw [f.spokes]at h
  rwa [tailCount_eq]
 theorem retained_caps {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (u : Fin (vertexCount l)) (q : Fin 4) :
    retainedDegree f u q ≤ if q=owner l u then 15 else 16 := by
  have hroot : f.root ∉ retained f := by
    intro h
    obtain ⟨i,_,he⟩ := mem_image.mp h
    exact f.ne_root i he
  have hs : colorNeighborhood c (palette q) (f.vertex u) ∩ retained f ⊆
      (colorNeighborhood c (palette q) (f.vertex u)).erase f.root := by
    intro v hv
    exact mem_erase.mpr ⟨fun he => hroot (he ▸ (mem_inter.mp hv).2),(mem_inter.mp hv).1⟩
  have hle := card_le_card hs
  have hcap := fourColor_colorDegree_le_sixteen c hc (palette q) (f.vertex u)
  change (colorNeighborhood c (palette q) (f.vertex u)).card≤16 at hcap
  change retainedDegree f u q≤_ at hle
  by_cases hq : q=owner l u
  · have hr : f.root ∈ colorNeighborhood c (palette q) (f.vertex u) := by
      apply (mem_colorNeighborhood _ _ _ _).mpr
      exact ⟨(f.ne_root u).symm,by rw [c.color_symm,f.spokes,hq]⟩
    have hh := card_erase_add_one hr
    rw [if_pos hq]
    omega
  · rw [if_neg hq]
    exact le_trans (le_trans hle (card_le_card (erase_subset _ _))) hcap

#print axioms free_bounds
#print axioms surviving_high_count
#print axioms retained_caps
end PricingABD.ABNumericBounds
