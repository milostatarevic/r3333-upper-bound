import PricingG.SignDesign

namespace PricingG.SignDesign
open Finset Matrix

/-- Balanced sign columns have an integral quarter inner product. The proof
uses their common positive positions, not a finite permutation enumeration. -/
theorem balanced_sign_dot_divisible_four (a b : Fin 16 → ℤ)
    (ha : ∀ x, a x = 1 ∨ a x = -1) (hb : ∀ x, b x = 1 ∨ b x = -1)
    (hsa : ∑ x, a x = 0) (hsb : ∑ x, b x = 0) :
    (4 : ℤ) ∣ ∑ x, a x * b x := by
  let A := univ.filter fun x => a x = 1
  let B := univ.filter fun x => b x = 1
  have hca : (A.card : ℤ) = 8 := by
    have he : ∀ x, a x = 2 * (if a x = 1 then 1 else 0) - 1 := by
      intro x; rcases ha x with h | h <;> simp [h]
    have hre := sum_congr (s₁ := (univ : Finset (Fin 16))) rfl (fun x _ => he x)
    rw [hre] at hsa
    have hh : (∑ x : Fin 16, (2 * (if a x = 1 then 1 else 0 : ℤ) - 1)) =
        2 * A.card - 16 := by
      simp [A,sum_sub_distrib,← mul_sum,← sum_filter,mul_comm]
    rw [hh] at hsa
    omega
  have hcb : (B.card : ℤ) = 8 := by
    have he : ∀ x, b x = 2 * (if b x = 1 then 1 else 0) - 1 := by
      intro x; rcases hb x with h | h <;> simp [h]
    have hre := sum_congr (s₁ := (univ : Finset (Fin 16))) rfl (fun x _ => he x)
    rw [hre] at hsb
    have hh : (∑ x : Fin 16, (2 * (if b x = 1 then 1 else 0 : ℤ) - 1)) =
        2 * B.card - 16 := by
      simp [B,sum_sub_distrib,← mul_sum,← sum_filter,mul_comm]
    rw [hh] at hsb
    omega
  have hterm : ∀ x, a x * b x =
      4 * (if a x = 1 ∧ b x = 1 then 1 else 0) -
        2 * (if a x = 1 then 1 else 0) - 2 * (if b x = 1 then 1 else 0) + 1 := by
    intro x
    rcases ha x with h | h <;> rcases hb x with h' | h' <;> norm_num [h,h']
  have hdot : (∑ x, a x * b x) = 4 * ((A ∩ B).card : ℤ) - 16 := by
    simp_rw [hterm]
    have hint : (univ.filter fun x => a x = 1 ∧ b x = 1) = A ∩ B := by
      ext x; simp [A,B]
    simp only [sum_add_distrib,sum_sub_distrib,← mul_sum]
    simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one,
      card_univ, Fintype.card_fin, hint]
    change 4 * ((A ∩ B).card : ℤ) - 2 * A.card - 2 * B.card + 16 = _
    rw [hca,hcb]
    ring
  refine ⟨((A ∩ B).card : ℤ) - 4,?_⟩
  rw [hdot]
  ring

/-- Integer overlap matrix for any second Clebsch labeling on the same
physical sixteen positions. -/
def overlap (σ : Equiv.Perm (Fin 16)) (i j : Fin 5) : ℤ :=
  (∑ u, row (σ u) i * row u j) / 4

theorem overlap_rescale (σ : Equiv.Perm (Fin 16)) (i j : Fin 5) :
    4 * overlap σ i j = ∑ u, row (σ u) i * row u j := by
  have hd := balanced_sign_dot_divisible_four (fun u => row (σ u) i) (fun u => row u j)
    (fun u => row_entries (σ u) i) (fun u => row_entries u j)
    (by rw [Equiv.sum_comp σ (fun u => row u i)]; exact column_balance i) (column_balance j)
  exact (mul_comm _ _).trans (Int.ediv_mul_cancel hd)

/-- A bound on all physical sign evaluations forces the claimed l1 bound
on a column, including either parity of coefficient signs. -/
theorem column_l1_bound (b : Fin 5 → ℤ)
    (heval : ∀ u, |∑ i, row u i * b i| ≤ 4) : ∑ i, |b i| ≤ 4 := by
  let s : Fin 5 → Bool := fun i => decide (0 ≤ b i)
  have hterm (i : Fin 5) : (if s i then 1 else -1 : ℤ) * b i = |b i| := by
    by_cases hb : 0 ≤ b i
    · simp [s,hb,abs_of_nonneg hb]
    · simp [s,hb,abs_of_neg (by omega : b i < 0)]
  obtain ⟨u,hu|hu⟩ := every_sign_up_to_negation s
  · have h := heval u
    simp_rw [hu,hterm] at h
    rwa [abs_of_nonneg (sum_nonneg (fun i _ => abs_nonneg (b i)))] at h
  · have h := heval u
    have hval : (∑ i, row u i * b i) = -(∑ i, |b i|) := by
      simp_rw [hu,neg_mul,hterm]
      simp only [sum_neg_distrib]
    rw [hval,abs_neg,abs_of_nonneg (sum_nonneg (fun i _ => abs_nonneg (b i)))] at h
    exact h

#print axioms overlap_rescale
#print axioms column_l1_bound
end PricingG.SignDesign
