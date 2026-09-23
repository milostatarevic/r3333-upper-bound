import PricingC.AutomorphismRigidity
import PricingC.AdjacentMapBoundary

namespace PricingC.AdjacentAutomorphisms
open PricingC

/-- Exact exhaustiveness of the25 retained direct maps. Every graph
isomorphism displacing each vertex to a neighbor is literally one stored
array in the existing physical XOR labels. -/
theorem adjacent_automorphism_retained (e : xorGraph ≃g xorGraph)
    (hadj : ∀ v, xorGraph.Adj v (e v)) :
    ∃ i : Fin 25, ∀ v, e v = retainedMap i v := by
  obtain ⟨t,ht⟩ := (root_adjacent_generator (e 0)).mp (hadj 0)
  obtain ⟨pi,hpi,hcoords⟩ := automorphism_anchor_parameters e
  have hpattern : ∀ j, xorGraph.Adj (generators j)
      (xorTranslation (generators t) (generators (pi j))) := by
    intro j
    rw [←ht,←hcoords j]
    exact hadj (generators j)
  obtain ⟨i,_,hi⟩ := adjacent_anchor_boundary t pi hpi hpattern
  refine ⟨i,automorphisms_equal_on_anchor e (retainedAuto i) ?_⟩
  intro j
  change e (generators j) = retainedMap i (generators j)
  rw [hcoords j,ht,hi j]

 theorem adjacent_equivalence_retained (e : Fin 16 ≃ Fin 16)
    (hgraph : ∀ u v, xorGraph.Adj (e u) (e v) ↔ xorGraph.Adj u v)
    (hadj : ∀ v, xorGraph.Adj v (e v)) :
    ∃ i : Fin 25, ∀ v, e v = retainedMap i v :=
  adjacent_automorphism_retained { toEquiv := e, map_rel_iff' := hgraph _ _ } hadj

#print axioms adjacent_automorphism_retained
#print axioms adjacent_equivalence_retained
end PricingC.AdjacentAutomorphisms
