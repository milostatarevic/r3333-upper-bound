import PricingG.SmallMixedCases
import PricingG.OverlapContraction

namespace PricingG.SignDesign
open Finset PricingC

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem energy_six_zeros_check : (boundedVectors 5 4).all (fun b =>
    decide (squareNorm b = 6 → (univ.filter fun i => b i = 0).card = 2)) = true := by decide

theorem energy_six_two_zeros (b : Fin 5 → ℤ) (hbound : ∑ i, (b i).natAbs ≤ 4)
    (he : squareNorm b = 6) : (univ.filter fun i => b i = 0).card = 2 := by
  have h := List.all_eq_true.mp energy_six_zeros_check b (boundedVectors_complete 5 4 b hbound)
  exact (of_decide_eq_true h) he

def baseSix : Finset (Fin 16) := {0,1,2,4,8,15}
def pairVertex (i j : Fin 5) : Fin 16 := R4333.xorIndex16 (generators i) (generators j)

theorem baseSix_card : baseSix.card = 6 := by decide

theorem baseSix_membership : ∀ u : Fin 16, u ∈ baseSix ↔ u = 0 ∨ ∃ i, u = generators i := by decide

theorem pair_not_base : ∀ i j : Fin 5, i ≠ j → pairVertex i j ∉ baseSix := by decide

private theorem generator_signs : ∀ i k : Fin 5, row (generators i) k = if k = i then 1 else -1 := by decide

private theorem pair_signs : ∀ i j : Fin 5, i ≠ j → ∀ k,
    row (pairVertex i j) k = if k = i ∨ k = j then -1 else 1 := by decide

theorem root_evaluation (b : Fin 5 → ℤ) : (∑ k, row 0 k * b k) = ∑ k, b k := by
  have hh : ∀ k, row 0 k = 1 := by decide
  simp only [hh,one_mul]

theorem generator_evaluation (b : Fin 5 → ℤ) (i : Fin 5) :
    (∑ k, row (generators i) k * b k) = 2 * b i - ∑ k, b k := by
  have ht (k : Fin 5) : row (generators i) k * b k =
      2 * (if k = i then b i else 0) - b k := by
    rw [generator_signs]
    by_cases h : k = i <;> simp [h] <;> ring
  simp_rw [ht]
  rw [sum_sub_distrib,← mul_sum]
  simp

theorem pair_evaluation (b : Fin 5 → ℤ) (i j : Fin 5) (hij : i ≠ j) :
    (∑ k, row (pairVertex i j) k * b k) = (∑ k, b k) - 2*b i - 2*b j := by
  have ht (k : Fin 5) : row (pairVertex i j) k * b k = b k -
      2 * (if k = i then b i else 0) - 2 * (if k = j then b j else 0) := by
    rw [pair_signs i j hij]
    by_cases hki : k = i
    · subst k; simp [hij]; ring
    · by_cases hkj : k = j
      · subst k; simp [hij.symm]; ring
      · simp [hki,hkj]
  simp_rw [ht]
  rw [sum_sub_distrib,sum_sub_distrib,← mul_sum,← mul_sum]
  simp

/-- Column l1 equality forces every coefficient nonnegative. -/
theorem nonnegative_of_column_sum (b : Fin 5 → ℤ)
    (hb : ∑ i, |b i| ≤ 4) (hs : ∑ i, b i = 4) : ∀ i, 0 ≤ b i := by
  have hle : (∑ i, b i) ≤ ∑ i, |b i| := sum_le_sum (fun i _ => le_abs_self (b i))
  have heq : (∑ i, b i) = ∑ i, |b i| := by omega
  have hh := (sum_eq_sum_iff_of_le (fun i _ => le_abs_self (b i))).mp heq
  intro i
  rw [hh i (mem_univ i)]
  exact abs_nonneg _

#print axioms energy_six_two_zeros
#print axioms pair_evaluation
end PricingG.SignDesign
