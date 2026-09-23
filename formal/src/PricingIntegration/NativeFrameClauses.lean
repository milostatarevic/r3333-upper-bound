import PricingIntegration.NativePrimary
import PricingIntegration.NativeColoringClauses

set_option autoImplicit false
namespace PricingIntegration.NativeFrameClauses
open Ramsey61 Ramsey61.DenseCounter
open Ramsey61.CEncodingCore (palette palette_injective palette_surjective)
open PricingABD.ABLayout PricingIntegration.NativePrimaryCore PricingIntegration.NativePrimary PricingIntegration.NativeColoringClauses
theorem primary_oneHot {c : Host} {l : Layout} (f : Frame c l) (u v : Fin (vertexCount l)) (huv : u < v) :
    FormulaSat (primary f) (oneHotClauses u v) := by
  rw [oneHotClauses, formulaSat_append]
  constructor
  · intro clause hclause
    simp only [List.mem_singleton] at hclause
    subst clause
    obtain ⟨q,hq⟩ := palette_surjective (c (f.vertex u) (f.vertex v))
    refine ⟨(true,orderedEdgeVar u v q), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨q,by simp,rfl⟩
    · exact (primary_ordered f u v q huv).2 hq.symm
  · intro clause hclause
    simp only [List.mem_flatMap, List.mem_map] at hclause
    obtain ⟨q,hq,r,hr,rfl⟩ := hclause
    have hqr : q < r := by simpa using (List.mem_filter.mp hr).2
    by_cases hcq : c (f.vertex u) (f.vertex v) = palette q
    · refine ⟨(false,orderedEdgeVar u v r),by simp,?_⟩
      apply (primary_ordered_false f u v r huv).2
      intro hcr
      have heq := palette_injective (hcq.symm.trans hcr)
      exact (ne_of_lt hqr) heq
    · exact ⟨(false,orderedEdgeVar u v q),by simp,
        (primary_ordered_false f u v q huv).2 hcq⟩

theorem primary_physical {c : Host} {l : Layout} (f : Frame c l) :
    FormulaSat (primary f) (physicalClauses (vertexCount l)) := by
  intro clause hclause
  obtain ⟨pair,hpair,hclause⟩ := List.mem_flatMap.mp hclause
  simp only [orderedPairs, List.mem_flatMap, List.mem_map] at hpair
  obtain ⟨u,hu,v,hv,rfl⟩ := hpair
  exact primary_oneHot f u v (by simpa using (List.mem_filter.mp hv).2) clause hclause

theorem primary_triangles {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) :
    FormulaSat (primary f) (triangleClauses (vertexCount l)) := by
  intro clause hclause
  simp only [triangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨u,hu,v,hv,w,hw,q,hq,rfl⟩ := hclause
  have huv : u < v := by simpa using (List.mem_filter.mp hv).2
  have hvw : v < w := by simpa using (List.mem_filter.mp hw).2
  have huw : u < w := lt_trans huv hvw
  by_cases hab : c (f.vertex u) (f.vertex v) = palette q
  · by_cases hac : c (f.vertex u) (f.vertex w) = palette q
    · refine ⟨(false,orderedEdgeVar v w q),by simp,?_⟩
      apply (primary_ordered_false f v w q hvw).2
      intro hbc
      exact hc (f.vertex u) (f.vertex v) (f.vertex w)
        ⟨f.vertex.injective.ne (ne_of_lt huv),f.vertex.injective.ne (ne_of_lt huw),f.vertex.injective.ne (ne_of_lt hvw)⟩
        ⟨hab.trans hac.symm,hac.trans hbc.symm⟩
    · exact ⟨(false,orderedEdgeVar u w q),by simp,
        (primary_ordered_false f u w q huw).2 hac⟩
  · exact ⟨(false,orderedEdgeVar u v q),by simp,
      (primary_ordered_false f u v q huv).2 hab⟩




#print axioms primary_physical
#print axioms primary_triangles
end PricingIntegration.NativeFrameClauses
