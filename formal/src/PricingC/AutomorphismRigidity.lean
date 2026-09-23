import PricingC.UnanchoredReference
import PricingC.AnchoredScope

namespace PricingC
open R4333

set_option maxRecDepth 100000 in
 theorem outside_anchor_mask_injective : ∀ u v : Fin 16,
    (∀ j, u ≠ generators j) → (∀ j, v ≠ generators j) →
    (∀ j, xorGraph.Adj u (generators j) ↔ xorGraph.Adj v (generators j)) → u = v := by decide

 theorem automorphism_fixed_on_anchor (e : xorGraph ≃g xorGraph)
    (h : ∀ j, e (generators j) = generators j) : ∀ v, e v = v := by
  intro v
  by_cases hv : ∃ j, v = generators j
  · obtain ⟨j,rfl⟩ := hv; exact h j
  · have ho : ∀ j, v ≠ generators j := by simpa using hv
    have heo : ∀ j, e v ≠ generators j := by
      intro j he
      exact ho j (e.injective (he.trans (h j).symm))
    apply outside_anchor_mask_injective (e v) v heo ho
    intro j
    have hm : xorGraph.Adj (e v) (e (generators j)) ↔ xorGraph.Adj v (generators j) := e.map_rel_iff
    rw [h j] at hm
    exact hm

 theorem automorphisms_equal_on_anchor (e f : xorGraph ≃g xorGraph)
    (h : ∀ j, e (generators j) = f (generators j)) : ∀ v, e v = f v := by
  let g := e.trans f.symm
  have hg : ∀ j, g (generators j) = generators j := by
    intro j
    change f.symm (e (generators j)) = generators j
    rw [h j]
    exact f.symm_apply_apply _
  intro v
  have hv := automorphism_fixed_on_anchor g hg v
  have hh := congrArg f hv
  exact (f.apply_symm_apply (e v)).symm.trans hh

set_option maxRecDepth 100000 in
 theorem translated_neighbor_coordinates : ∀ t v : Fin 16,
    xorGraph.Adj t v ↔ ∃ j : Fin 5, v = xorTranslation t (generators j) := by decide

 theorem root_adjacent_generator : ∀ v : Fin 16,
    xorGraph.Adj 0 v ↔ ∃ j : Fin 5, v = generators j := by decide

/-- The actual images of an ordered five-neighborhood are described by one
permutation of generator labels and the actual image of the root. -/
theorem automorphism_anchor_parameters (e : xorGraph ≃g xorGraph) :
    ∃ pi : Fin 5 → Fin 5, Function.Injective pi ∧
      ∀ j, e (generators j) = xorTranslation (e 0) (generators (pi j)) := by
  have ha : ∀ j, xorGraph.Adj 0 (generators j) := by decide
  have he : ∀ j, ∃ k : Fin 5, e (generators j) = xorTranslation (e 0) (generators k) := by
    intro j
    exact (translated_neighbor_coordinates _ _).mp (e.map_rel_iff.mpr (ha j))
  choose pi hp using he
  refine ⟨pi,?_,hp⟩
  intro i j hij
  apply generators_injective
  apply e.injective
  exact (hp i).trans ((congrArg (fun k => xorTranslation (e 0) (generators k)) hij).trans (hp j).symm)

#print axioms automorphisms_equal_on_anchor
#print axioms automorphism_anchor_parameters
end PricingC
