import PricingIntegration.NativeColoringClauses
set_option autoImplicit false
namespace PricingIntegration.NativeClauseBounds
open Ramsey61.DenseCounter PricingIntegration.NativePrimaryCore PricingIntegration.NativeColoringClauses
theorem oneHotClauses_bound {n : Nat} (hn : 50≤n ∧ n≤53) (u v : Fin n) (huv : u < v) :
    ∀ clause ∈ oneHotClauses u v, ∀ literal ∈ clause, literal.2 < edgeLimit n := by
  intro clause hclause literal hliteral
  rcases List.mem_append.mp hclause with hfirst | hrest
  · simp only [List.mem_singleton] at hfirst
    subst clause
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hliteral
    exact (orderedEdgeVar_bounds hn u v q huv).2
  · obtain ⟨q,hq,hclause⟩ := List.mem_flatMap.mp hrest
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hclause
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
    rcases hliteral with rfl | rfl
    · exact (orderedEdgeVar_bounds hn u v q huv).2
    · exact (orderedEdgeVar_bounds hn u v r huv).2

theorem physicalClauses_bound {n : Nat} (hn : 50≤n ∧ n≤53) :
    ∀ clause ∈ physicalClauses n, ∀ literal ∈ clause, literal.2 < edgeLimit n := by
  intro clause hclause literal hliteral
  obtain ⟨pair,hpair,hclause⟩ := List.mem_flatMap.mp hclause
  simp only [orderedPairs, List.mem_flatMap, List.mem_map] at hpair
  obtain ⟨u,hu,v,hv,rfl⟩ := hpair
  exact oneHotClauses_bound hn u v (by simpa using (List.mem_filter.mp hv).2) clause hclause literal hliteral

theorem triangleClauses_bound {n : Nat} (hn : 50≤n ∧ n≤53) :
    ∀ clause ∈ triangleClauses n, ∀ literal ∈ clause, literal.2 < edgeLimit n := by
  intro clause hclause literal hliteral
  simp only [triangleClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨u,hu,v,hv,w,hw,q,hq,rfl⟩ := hclause
  have huv : u < v := by simpa using (List.mem_filter.mp hv).2
  have hvw : v < w := by simpa using (List.mem_filter.mp hw).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
  rcases hliteral with rfl | rfl | rfl
  · exact (orderedEdgeVar_bounds hn u v q huv).2
  · exact (orderedEdgeVar_bounds hn u w q (lt_trans huv hvw)).2
  · exact (orderedEdgeVar_bounds hn v w q hvw).2



#print axioms physicalClauses_bound
#print axioms triangleClauses_bound
end PricingIntegration.NativeClauseBounds
