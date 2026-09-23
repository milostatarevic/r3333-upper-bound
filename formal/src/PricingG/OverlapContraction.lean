import PricingG.SignEvaluations

namespace PricingG.SignDesign
open Finset Matrix

set_option maxRecDepth 100000 in
theorem sign_column_gram : signMatrixᵀ * signMatrix = (16 : ℤ) • (1 : M5) := by decide

theorem perm_column_gram (σ : Equiv.Perm (Fin 16)) :
    (permRows σ)ᵀ * permRows σ = (16 : ℤ) • (1 : M5) := by
  ext i j
  have h := congrFun (congrFun sign_column_gram i) j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,permRows] at h ⊢
  rw [Equiv.sum_comp σ (fun u => row u i * row u j)]
  exact h

private theorem dot_mulVec_gram {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) (x : n → ℤ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec]
  exact (Matrix.dotProduct_transpose_mulVec A x (A *ᵥ x)).symm

/-- The norm bound required by the s=6 argument follows from an explicit
sum of integer squares, avoiding any unverified spectral computation. -/
theorem overlap_contracts (σ : Equiv.Perm (Fin 16)) (x : Fin 5 → ℤ) :
    (overlapMatrix σ *ᵥ x) ⬝ᵥ (overlapMatrix σ *ᵥ x) ≤ 16 * (x ⬝ᵥ x) := by
  let V := signMatrix
  let W := permRows σ
  let B := overlapMatrix σ
  let y := V *ᵥ x
  let z := B *ᵥ x
  have hy : y ⬝ᵥ y = 16 * (x ⬝ᵥ x) := by
    rw [dot_mulVec_gram,sign_column_gram,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
    rfl
  have hz : (W *ᵥ z) ⬝ᵥ (W *ᵥ z) = 16 * (z ⬝ᵥ z) := by
    rw [dot_mulVec_gram,perm_column_gram,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
    rfl
  have hcross : y ⬝ᵥ (W *ᵥ z) = 4 * (z ⬝ᵥ z) := by
    rw [← Matrix.dotProduct_transpose_mulVec W z y]
    have hWy : Wᵀ *ᵥ y = (4 : ℤ) • z := by
      rw [Matrix.mulVec_mulVec,← overlap_matrix_rescale,Matrix.smul_mulVec]
    rw [hWy,dotProduct_smul]
    rfl
  have hpos : 0 ≤ ((4 : ℤ) • y - W *ᵥ z) ⬝ᵥ ((4 : ℤ) • y - W *ᵥ z) := by
    unfold dotProduct
    exact sum_nonneg (fun i _ => mul_self_nonneg _)
  simp only [sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul] at hpos
  have hrev : (W *ᵥ z) ⬝ᵥ y = y ⬝ᵥ (W *ᵥ z) := dotProduct_comm _ _
  rw [hrev,hy,hz,hcross] at hpos
  change 0 ≤ 4 * (4 * (16 * (x ⬝ᵥ x)) - 4 * (z ⬝ᵥ z)) -
    (4 * (4 * (z ⬝ᵥ z)) - 16 * (z ⬝ᵥ z)) at hpos
  change z ⬝ᵥ z ≤ 16 * (x ⬝ᵥ x)
  omega

/-- Four in every column forces four in every row for this actual overlap
matrix; the contraction bound is used at equality. -/
theorem overlap_row_sums_four (σ : Equiv.Perm (Fin 16))
    (hcol : ∀ j, ∑ i, overlap σ i j = 4) :
    ∀ i, ∑ j, overlap σ i j = 4 := by
  let q : Fin 5 → ℤ := fun i => ∑ j, overlap σ i j
  have hqsum : ∑ i, q i = 20 := by
    rw [show (∑ i, q i) = ∑ j, ∑ i, overlap σ i j from sum_comm]
    simp [hcol]
  have hnorm : q ⬝ᵥ q ≤ 80 := by
    have h := overlap_contracts σ (fun _ => 1)
    simpa [Matrix.mulVec,dotProduct,overlapMatrix,q] using h
  have hsq : ∑ i, (q i - 4) ^ 2 ≤ 0 := by
    have heq : (∑ i, (q i - 4) ^ 2) = q ⬝ᵥ q - 8 * (∑ i, q i) + 80 := by
      unfold dotProduct
      simp_rw [show ∀ x : ℤ, (x-4)^2 = x*x - 8*x +16 by intro x; ring]
      simp [sum_add_distrib,sum_sub_distrib,← mul_sum]
    rw [heq,hqsum]
    omega
  intro i
  have hnon : ∀ j ∈ (univ : Finset (Fin 5)), 0 ≤ (q j - 4) ^ 2 := fun j _ => sq_nonneg _
  have hsum := sum_nonneg hnon
  have hi := (sum_eq_zero_iff_of_nonneg hnon).mp (by omega) i (mem_univ i)
  have hz : q i - 4 = 0 := sq_eq_zero_iff.mp hi
  change q i = 4
  omega

#print axioms overlap_contracts
#print axioms overlap_row_sums_four
end PricingG.SignDesign
