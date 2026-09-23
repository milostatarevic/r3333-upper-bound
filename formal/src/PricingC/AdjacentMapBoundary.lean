import PricingC.AdjacentMapData

namespace PricingC.AdjacentAutomorphisms
open PricingC

/- Every injective assignment of the five actual neighbor images that
satisfies the displacement restriction is one of the25 literal retained maps.
Only5×3125 finite assignments are inspected; no graph search is assumed. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem adjacent_anchor_boundary (t : Fin 5) : ∀ pi : Fin 5 → Fin 5,
    Function.Injective pi →
    (∀ j, xorGraph.Adj (generators j) (xorTranslation (generators t) (generators (pi j)))) →
    ∃ i : Fin 25, retainedMap i 0 = generators t ∧
      ∀ j, retainedMap i (generators j) = xorTranslation (generators t) (generators (pi j)) := by
  fin_cases t <;> decide +kernel

#print axioms adjacent_anchor_boundary
end PricingC.AdjacentAutomorphisms
