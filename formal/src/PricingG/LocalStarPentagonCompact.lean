import PricingG.EightPentagons
import PricingC.CanonicalGraph

namespace PricingG
open Finset PricingC

instance inducedDegreeTwoDecidable {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (S : Finset V) :
    Decidable (InducedDegreeTwo K S) :=
  inferInstanceAs (Decidable (∀ x ∈ S, (S.filter fun y => K.Adj x y).card = 2))

def RootMaskCondition (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (v : Fin 16) (A : Finset (Fin 16)) : Prop :=
  ∀ x ∈ K.neighborFinset v,
    (A.filter fun a => K.Adj x a).card = 2 ∨ (A.filter fun a => K.Adj x a).card = 5

instance rootMaskConditionDecidable (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (v : Fin 16) (A : Finset (Fin 16)) : Decidable (RootMaskCondition K v A) :=
  inferInstanceAs (Decidable (∀ x ∈ K.neighborFinset v,
    (A.filter fun a => K.Adj x a).card = 2 ∨ (A.filter fun a => K.Adj x a).card = 5))

/-- Exact incidence law of a pentagonal five-set relative to its unique
zero-neighbor. It also describes the complementary parity pentagon. -/
def RootPentagonLaw (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (v : Fin 16) (A : Finset (Fin 16)) : Prop :=
  ∀ x, (A.filter fun a => K.Adj x a).card =
    if x = v then 0 else if x ∈ A ∨ K.Adj v x then 2 else 1

instance rootPentagonLawDecidable (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (v : Fin 16) (A : Finset (Fin 16)) : Decidable (RootPentagonLaw K v A) :=
  inferInstanceAs (Decidable (∀ x, (A.filter fun a => K.Adj x a).card =
    if x = v then 0 else if x ∈ A ∨ K.Adj v x then 2 else 1))

/-- Explicit 462-candidate subtype, avoiding an accidental outer powerset
quantifier over every finite set. -/
def fiveCandidates := (univ \ xorGraph.neighborFinset 0).powersetCard 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_root_star_or_pentagon_compact :
    ∀ A : fiveCandidates, RootMaskCondition xorGraph 0 A.val →
      (∃ a : Fin 16, xorGraph.Adj 0 a ∧ A.val = xorGraph.neighborFinset a) ∨
      (InducedDegreeTwo xorGraph A.val ∧ RootPentagonLaw xorGraph 0 A.val) := by
  decide

theorem canonical_root_star_or_pentagon (A : Finset (Fin 16))
    (hA : A ∈ (univ \ xorGraph.neighborFinset 0).powersetCard 5)
    (hmask : RootMaskCondition xorGraph 0 A) :
    (∃ a : Fin 16, xorGraph.Adj 0 a ∧ A = xorGraph.neighborFinset a) ∨
    (InducedDegreeTwo xorGraph A ∧ RootPentagonLaw xorGraph 0 A) :=
  canonical_root_star_or_pentagon_compact ⟨A,hA⟩ hmask

#print axioms canonical_root_star_or_pentagon
end PricingG
