import PricingC.ScopeModels
import PricingC.CanonicalGraph
import PricingG.Completion72

namespace PricingC
open Finset R4333 SimpleGraph

/-- Literal equality between our graph presentation and the shared retained
72-state relation's Boolean designated-color graph. -/
theorem xor_graph_binding (u v : Fin 16) :
    xorGraph.Adj u v ↔ u ≠ v ∧ PricingG.Completion72.xorClebsch u v = true := by
  revert u v
  decide

/-- An arbitrarily ordered actual five-neighborhood can be normalized to
the same five generator positions without permuting the color palette. -/
theorem ordered_anchor_reference (d : EdgeColoring (Fin 16) (Fin 3))
    (hd : NoMonochromaticTriangle d) (r : Fin 16)
    (points : Fin 5 ≃ ↥(clebschA (colorGraph d 0) r)) :
    ∃ (i : Fin 72) (e : Fin 16 ≃ Fin 16),
      e 0 = r ∧ (∀ j, e (generators j) = (points j).val) ∧
      ∀ u v, u ≠ v → d (e u) (e v) = PricingG.Completion72.referenceColor i u v := by
  classical
  let G := colorGraph d (0 : Fin 3)
  have hs := k16_colorGraph_isSRG d hd (0 : Fin 3)
  let e := anchoredCoordinates G hs r points
  let d' := relabelVertices d e.toEquiv
  have hd' : NoMonochromaticTriangle d' := noMono_relabelVertices d e.toEquiv hd
  have hz : ∀ u v, u ≠ v → (d' u v = 0 ↔ PricingG.Completion72.xorClebsch u v = true) := by
    intro u v huv
    have hm : G.Adj (e u) (e v) ↔ xorGraph.Adj u v := e.map_rel_iff
    rw [xor_graph_binding] at hm
    change (e u ≠ e v ∧ d (e u) (e v) = 0) ↔ _ at hm
    constructor
    · intro hc
      exact (hm.mp ⟨e.injective.ne huv,hc⟩).2
    · intro hc
      exact (hm.mpr ⟨huv,hc⟩).2
  obtain ⟨i,hi⟩ := PricingG.Completion72.reference_exhaustive d' hd' hz
  refine ⟨i,e.toEquiv,anchoredCoordinates_root G hs r points,?_,hi⟩
  exact fun j => anchoredCoordinates_point G hs r points j

#print axioms ordered_anchor_reference
end PricingC
