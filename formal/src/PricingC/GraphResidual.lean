import PricingC.GParityGeometry
import PricingC.ResidualSmall
import PricingG.GeneralMixedCases
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace PricingC.GParity
open Finset Matrix PricingG

theorem productSupport_eq_oddSupport (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (y : Fin 16) :
    columnSupport (parityProduct K J) y = oddSupport K (J.neighborFinset y) := by
  ext x
  simp [columnSupport,oddSupport,parityProduct_entry,ZMod.natCast_eq_one_iff_odd]

theorem rooted_pair_has_residual (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ) :
    Nonempty (ResidualPentagons K (defectCount K J)) := by
  classical
  let D := univ.filter fun y => InducedDegreeTwo K (J.neighborFinset y)
  have horth := parityProduct_orthogonal K J hK hJ
  apply extract_residual_pentagons K (parityProduct K J) horth.1 horth.2 D
  · intro y hy
    have hn : ¬ InducedDegreeTwo K (J.neighborFinset y) := by simpa [D] using hy
    obtain ⟨a,_,ha⟩ := (hd y).resolve_right (fun hp => hn hp.1)
    exact ⟨a,columnSupport_unit _ _ _ (parityProduct_star K J hK a y ha)⟩
  · intro y hy
    have hp : InducedDegreeTwo K (J.neighborFinset y) := (mem_filter.mp hy).2
    have hcard : (J.neighborFinset y).card = 5 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hJ.regular y
    have hlaw : RootPentagonLaw K (ρ y) (J.neighborFinset y) := by
      rcases hd y with ⟨a,_,ha⟩ | hh
      · obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (J.neighborFinset y).card by omega)
        have h2 := hp x hx
        rw [ha] at hx h2
        have h0 := star_filter_card_zero K hK a x hx
        omega
      · exact hh.2
    rw [productSupport_eq_oddSupport]
    exact pentagon_odd_support K hK (ρ y) (J.neighborFinset y) hcard hp hlaw

/-- The trace counts directed edges of the intersection graph, hence is even. -/
theorem common_trace_even (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] :
    Even (trace (K.adjMatrix ℤ * J.adjMatrix ℤ)) := by
  classical
  have hdiag (v : Fin 16) : (K.adjMatrix ℤ * J.adjMatrix ℤ) v v = ((K ⊓ J).degree v : ℤ) := by
    rw [K.adjMatrix_mul_apply]
    simp only [SimpleGraph.adjMatrix_apply]
    have heq : ∑ x ∈ K.neighborFinset v, (if J.Adj x v then (1 : ℤ) else 0) =
        (((K.neighborFinset v).filter fun x => J.Adj v x).card : ℤ) := by
      simp_rw [J.adj_comm]
      simp [← sum_filter]
    rw [heq]
    congr 1
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext x
    simp
  have heq : trace (K.adjMatrix ℤ * J.adjMatrix ℤ) = ∑ x, ((K ⊓ J).degree x : ℤ) := by
    simp only [Matrix.trace,Matrix.diag,hdiag]
  rw [heq]
  have h := (K ⊓ J).sum_degrees_eq_twice_card_edges
  have hc := congrArg (fun n : Nat => (n : ℤ)) h
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat] at hc
  refine ⟨((@SimpleGraph.edgeFinset (Fin 16) (K ⊓ J) (K ⊓ J).fintypeEdgeSet).card : ℤ), ?_⟩
  rw [← two_mul]
  exact hc

theorem defectCount_even (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ) :
    Even (defectCount K J) := by
  have h := common_edges_and_defects K J hK hJ (fun y => by
    rcases hd y with ⟨a,_,ha⟩ | hp
    · exact Or.inl ⟨a,ha⟩
    · exact Or.inr hp.1)
  obtain ⟨n,hn⟩ := common_trace_even K J
  rw [hn] at h
  rw [Nat.even_iff]
  omega

theorem defectCount_zero_or_sixteen (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ) :
    defectCount K J = 0 ∨ defectCount K J = 16 := by
  have he := defectCount_even K J hK hJ ρ hd
  have hm := high_mixed_counts_excluded K J hK hJ ρ hd
  have hle : defectCount K J ≤ 16 := by
    exact le_trans (card_le_univ _) (by simp)
  have hsmall : ¬ (0 < defectCount K J ∧ defectCount K J ≤ 8) := by
    rintro ⟨hp,hle⟩
    obtain ⟨f⟩ := rooted_pair_has_residual K J hK hJ ρ hd
    exact residual_not_small K _ f hp he hle
  rw [Nat.even_iff] at he
  omega

#print axioms rooted_pair_has_residual
#print axioms defectCount_zero_or_sixteen
end PricingC.GParity
