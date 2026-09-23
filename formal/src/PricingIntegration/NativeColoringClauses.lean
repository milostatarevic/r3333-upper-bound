import PricingIntegration.NativePrimaryCore

set_option autoImplicit false
namespace PricingIntegration.NativeColoringClauses
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingIntegration.NativePrimaryCore
def orderedPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v).map fun v => (u,v)

def oneHotClauses {n : Nat} (u v : Fin n) : CNF :=
  [(List.finRange 4).map fun q => (true, orderedEdgeVar u v q)] ++
  (List.finRange 4).flatMap fun q =>
    ((List.finRange 4).filter fun r => q < r).map fun r =>
      [(false, orderedEdgeVar u v q), (false, orderedEdgeVar u v r)]

def physicalClauses (n : Nat) : CNF := (orderedPairs n).flatMap fun pair => oneHotClauses pair.1 pair.2

def triangleClauses (n : Nat) : CNF :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v).flatMap fun v =>
      ((List.finRange n).filter fun w => v < w).flatMap fun w =>
        (List.finRange 4).map fun q =>
          [(false, orderedEdgeVar u v q), (false, orderedEdgeVar u w q),
           (false, orderedEdgeVar v w q)]

theorem physicalValuation_oneHot {n : Nat} (hn : 50≤n ∧ n≤53) (c : Coloring n) (u v : Fin n) (huv : u < v) :
    FormulaSat (physicalValuation c) (oneHotClauses u v) := by
  rw [oneHotClauses, formulaSat_append]
  constructor
  · intro clause hclause
    simp only [List.mem_singleton] at hclause
    subst clause
    obtain ⟨q,hq⟩ := palette_surjective (c u v)
    refine ⟨(true,orderedEdgeVar u v q), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨q,by simp,rfl⟩
    · exact (physicalValuation_ordered hn c u v q huv).2 hq.symm
  · intro clause hclause
    simp only [List.mem_flatMap, List.mem_map] at hclause
    obtain ⟨q,hq,r,hr,rfl⟩ := hclause
    have hqr : q < r := by simpa using (List.mem_filter.mp hr).2
    by_cases hcq : c u v = palette q
    · refine ⟨(false,orderedEdgeVar u v r),by simp,?_⟩
      apply (physicalValuation_ordered_false hn c u v r huv).2
      intro hcr
      have heq := palette_injective (hcq.symm.trans hcr)
      exact (ne_of_lt hqr) heq
    · exact ⟨(false,orderedEdgeVar u v q),by simp,
        (physicalValuation_ordered_false hn c u v q huv).2 hcq⟩

theorem physicalValuation_physical {n : Nat} (hn : 50≤n ∧ n≤53) (c : Coloring n) :
    FormulaSat (physicalValuation c) (physicalClauses n) := by
  intro clause hclause
  obtain ⟨pair,hpair,hclause⟩ := List.mem_flatMap.mp hclause
  simp only [orderedPairs, List.mem_flatMap, List.mem_map] at hpair
  obtain ⟨u,hu,v,hv,rfl⟩ := hpair
  exact physicalValuation_oneHot hn c u v (by simpa using (List.mem_filter.mp hv).2) clause hclause

theorem physicalValuation_triangles {n : Nat} (hn : 50≤n ∧ n≤53) (c : Coloring n) (hc : NoMonochromaticTriangle c) :
    FormulaSat (physicalValuation c) (triangleClauses n) := by
  intro clause hclause
  simp only [triangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨u,hu,v,hv,w,hw,q,hq,rfl⟩ := hclause
  have huv : u < v := by simpa using (List.mem_filter.mp hv).2
  have hvw : v < w := by simpa using (List.mem_filter.mp hw).2
  have huw : u < w := lt_trans huv hvw
  by_cases hab : c u v = palette q
  · by_cases hac : c u w = palette q
    · refine ⟨(false,orderedEdgeVar v w q),by simp,?_⟩
      apply (physicalValuation_ordered_false hn c v w q hvw).2
      intro hbc
      exact hc u v w ⟨ne_of_lt huv,ne_of_lt huw,ne_of_lt hvw⟩
        ⟨hab.trans hac.symm,hac.trans hbc.symm⟩
    · exact ⟨(false,orderedEdgeVar u w q),by simp,
        (physicalValuation_ordered_false hn c u w q huw).2 hac⟩
  · exact ⟨(false,orderedEdgeVar u v q),by simp,
      (physicalValuation_ordered_false hn c u v q huv).2 hab⟩



#print axioms physicalValuation_physical
#print axioms physicalValuation_triangles
end PricingIntegration.NativeColoringClauses
