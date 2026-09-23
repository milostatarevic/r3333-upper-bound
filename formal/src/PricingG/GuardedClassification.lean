import PricingG.IsomorphismEndpoint
import PricingC.GraphResidual

namespace PricingG
open Ramsey61 PricingC

/-- Complete analytic dichotomy on the actual physical G model. All mixed
counts are eliminated; the two outcomes preserve both root embeddings,
center permutations, and physical color maps. -/
theorem GuardedGraphModel.classified {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q) :
    (m.K = m.J ∧ ∀ (e : xorGraph ≃g m.K), ∃ i : Fin 25, ∀ v,
      e.symm (m.imageRule (e v)) = AdjacentAutomorphisms.retainedMap i v) ∨
    ((∀ v, m.imageRule v = v) ∧ ∀ (e : xorGraph ≃g m.K), ∃ i : Fin 72,
      ∀ u v, u ≠ v → decompositionColoring m.K m.J (e u) (e v) = Completion72.referenceColor i u v) := by
  have hd : GraphRootedDichotomy m.K m.J m.imageRule := m.shared_graph_rooted_dichotomy hc hG
  rcases GParity.defectCount_zero_or_sixteen m.K m.J m.K_srg m.J_srg m.imageRule hd with hz | hz
  · left
    exact ⟨zero_defects_graph_eq m.K m.J m.K_srg m.J_srg hd.unrooted hz,
      fun e => m.zero_defects_exact25_coordinates hc hG hz e⟩
  · right
    exact ⟨full_defects_image_identity m.K m.J m.K_srg m.J_srg m.imageRule hd hz,
      fun e => full_defects_exact72_coordinates m.K m.J m.K_srg m.J_srg m.imageRule hd hz e⟩

/-- A genuine guarded host supplies the classified physical data. Neither
center bijections, shared-graph classification nor table completeness is an
assumption of this entrance theorem. -/
theorem regular_overlap_classified (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (p q : FourColor) (hG : RegularOverlapGuard c r p q) :
    ∃ m : GuardedGraphModel c r p q hG.colors_distinct,
    (m.K = m.J ∧ ∀ (e : xorGraph ≃g m.K), ∃ i : Fin 25, ∀ v,
      e.symm (m.imageRule (e v)) = AdjacentAutomorphisms.retainedMap i v) ∨
    ((∀ v, m.imageRule v = v) ∧ ∀ (e : xorGraph ≃g m.K), ∃ i : Fin 72,
      ∀ u v, u ≠ v → decompositionColoring m.K m.J (e u) (e v) = Completion72.referenceColor i u v) := by
  obtain ⟨m⟩ := regular_overlap_has_graph_model c hc r p q hG
  exact ⟨m,m.classified hc hG⟩

#print axioms GuardedGraphModel.classified
#print axioms regular_overlap_classified
end PricingG
