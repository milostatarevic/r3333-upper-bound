import PricingG.GuardedGraphModel
import Mathlib.LinearAlgebra.Matrix.Trace

namespace PricingG
open Finset Matrix

def defectCount (K J : SimpleGraph (Fin 16)) [DecidableRel K.Adj] [DecidableRel J.Adj] : Nat :=
  (univ.filter fun y => InducedDegreeTwo K (J.neighborFinset y)).card

/-- The diagonal of JKJ counts K-incidences inside one actual J-neighborhood. -/
theorem triple_product_diagonal (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (y : Fin 16) :
    ((J.adjMatrix ℤ * K.adjMatrix ℤ) * J.adjMatrix ℤ) y y =
      ∑ x ∈ J.neighborFinset y, (((J.neighborFinset y).filter fun z => K.Adj x z).card : ℤ) := by
  rw [J.mul_adjMatrix_apply]
  simp_rw [J.adjMatrix_mul_apply]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  simp [SimpleGraph.adjMatrix_apply,← sum_filter]

theorem star_filter_card_zero (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (a x : Fin 16) (hx : x ∈ K.neighborFinset a) :
    ((K.neighborFinset a).filter fun z => K.Adj x z).card = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact R4333.clebschA_pair_not_adj K hK hx (mem_filter.mp hz).1 (mem_filter.mp hz).2

/-- Mixed-edge counting, including the exact factor of two for directed
adjacency matrices. It is valid on any common labeling of the two graphs. -/
theorem common_edges_and_defects
    (K J : SimpleGraph (Fin 16)) [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (hdich : ∀ y, (∃ a, J.neighborFinset y = K.neighborFinset a) ∨
      InducedDegreeTwo K (J.neighborFinset y)) :
    Matrix.trace (K.adjMatrix ℤ * J.adjMatrix ℤ) + 5 * (defectCount K J : ℤ) = 80 := by
  have hdiag (y : Fin 16) :
      ((J.adjMatrix ℤ * K.adjMatrix ℤ) * J.adjMatrix ℤ) y y =
        if InducedDegreeTwo K (J.neighborFinset y) then 10 else 0 := by
    rw [triple_product_diagonal]
    by_cases hp : InducedDegreeTwo K (J.neighborFinset y)
    · rw [if_pos hp]
      have heq : (∑ x ∈ J.neighborFinset y,
          (((J.neighborFinset y).filter fun z => K.Adj x z).card : ℤ)) =
          ∑ _x ∈ J.neighborFinset y, (2 : ℤ) := by
        apply sum_congr rfl
        intro x hx
        rw [hp x hx]
        norm_num
      rw [heq]
      have hdeg : ∀ x, J.degree x = 5 := hJ.regular
      simp [SimpleGraph.card_neighborFinset_eq_degree,hdeg]
    · rw [if_neg hp]
      obtain ⟨a,ha⟩ := (hdich y).resolve_right hp
      rw [ha]
      apply sum_eq_zero
      intro x hx
      rw [star_filter_card_zero K hK a x hx]
      rfl
  have ht : Matrix.trace ((J.adjMatrix ℤ * K.adjMatrix ℤ) * J.adjMatrix ℤ) =
      10 * (defectCount K J : ℤ) := by
    simp only [Matrix.trace,Matrix.diag,hdiag]
    simp [defectCount,← sum_filter,mul_comm]
  have hsq : J.adjMatrix ℤ * J.adjMatrix ℤ =
      5 • (1 : Matrix (Fin 16) (Fin 16) ℤ) + 2 • Jᶜ.adjMatrix ℤ := by
    simpa only [pow_two,zero_smul,add_zero] using hJ.matrix_eq (α := ℤ)
  have hcycle : Matrix.trace ((J.adjMatrix ℤ * K.adjMatrix ℤ) * J.adjMatrix ℤ) =
      2 * Matrix.trace (K.adjMatrix ℤ * Jᶜ.adjMatrix ℤ) := by
    rw [Matrix.trace_mul_cycle,hsq]
    simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_add,Matrix.trace_smul,
      SimpleGraph.trace_adjMatrix,smul_zero,zero_add]
    rw [Matrix.trace_mul_comm]
    rfl
  have htotal : Matrix.trace (K.adjMatrix ℤ * J.adjMatrix ℤ) +
      Matrix.trace (K.adjMatrix ℤ * Jᶜ.adjMatrix ℤ) = 80 := by
    have hcomp := J.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℤ)
    rw [J.compl_adjMatrix_eq_adjMatrix_compl ℤ] at hcomp
    have h := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℤ => Matrix.trace (K.adjMatrix ℤ * M)) hcomp
    simp only [Matrix.mul_add,Matrix.mul_one,Matrix.trace_add,SimpleGraph.trace_adjMatrix,zero_add] at h
    have hr : Matrix.trace (K.adjMatrix ℤ * Matrix.of (1 : Fin 16 → Fin 16 → ℤ)) = 80 := by
      simp only [Matrix.trace,Matrix.diag,K.adjMatrix_mul_apply]
      have hdeg : ∀ x, K.degree x = 5 := hK.regular
      simp [hdeg]
    rwa [hr] at h
  omega

#print axioms common_edges_and_defects
end PricingG
