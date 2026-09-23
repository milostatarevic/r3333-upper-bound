import PricingG.StarPentagonTransport
import PricingG.SignMatrix

namespace PricingG.SignDesign
open Finset PricingC

def rootedFiveCandidates (v : Fin 16) := (univ \ xorGraph.neighborFinset v).powersetCard 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact pentagon centroid on every root, checked only on its462candidate
five-subsets. Roots remain labeled, and every coordinate sign is retained. -/
theorem pentagon_centroid_check (v : Fin 16) :
    ∀ A : rootedFiveCandidates v, RootPentagonLaw xorGraph v A.val →
      ∀ i : Fin 5, ∑ a ∈ A.val, row a i = row v i := by
  fin_cases v <;> decide

theorem pentagon_centroid (v : Fin 16) (A : Finset (Fin 16))
    (hA : A.card = 5) (havoid : Disjoint A (xorGraph.neighborFinset v))
    (hlaw : RootPentagonLaw xorGraph v A) :
    ∀ i : Fin 5, ∑ a ∈ A, row a i = row v i := by
  have hsub : A ⊆ univ \ xorGraph.neighborFinset v := by
    intro a ha
    exact mem_sdiff.mpr ⟨mem_univ _,fun h => disjoint_left.mp havoid ha h⟩
  exact pentagon_centroid_check v ⟨A,mem_powersetCard.mpr ⟨hsub,hA⟩⟩ hlaw

#print axioms pentagon_centroid
end PricingG.SignDesign
