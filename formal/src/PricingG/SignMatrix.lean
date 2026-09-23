import PricingG.SignOverlap
import Mathlib.LinearAlgebra.Matrix.Trace

namespace PricingG.SignDesign
open Finset Matrix PricingC

abbrev M16 := Matrix (Fin 16) (Fin 16) ℤ
abbrev M5 := Matrix (Fin 5) (Fin 5) ℤ

def signMatrix : Matrix (Fin 16) (Fin 5) ℤ := Matrix.of row
def overlapMatrix (σ : Equiv.Perm (Fin 16)) : M5 := Matrix.of (overlap σ)

def ones : M16 := fun _ _ => 1
def adjacency : M16 := xorGraph.adjMatrix ℤ

def permRows (σ : Equiv.Perm (Fin 16)) : Matrix (Fin 16) (Fin 5) ℤ := fun u i => row (σ u) i

def permAdj (σ : Equiv.Perm (Fin 16)) : M16 := fun u v => adjacency (σ u) (σ v)

set_option maxRecDepth 100000 in
theorem row_matrix_gram : signMatrix * signMatrixᵀ =
    (4 : ℤ) • (1 : M16) + ones - (4 : ℤ) • adjacency := by decide

set_option maxRecDepth 100000 in
theorem ones_row_zero : ones * signMatrix = 0 := by decide

set_option maxRecDepth 100000 in
theorem adjacency_rows : ∀ u, ∑ v, adjacency u v = 5 := by decide

set_option maxRecDepth 100000 in
theorem adjacency_cols : ∀ v, ∑ u, adjacency u v = 5 := by decide

set_option maxRecDepth 100000 in
theorem ones_square : ones * ones = (16 : ℤ) • ones := by decide

set_option maxRecDepth 100000 in
theorem adjacency_ones : adjacency * ones = (5 : ℤ) • ones := by decide

@[simp] theorem trace_adjacency : Matrix.trace adjacency = 0 := by decide
@[simp] theorem trace_ones : Matrix.trace ones = 16 := by decide
@[simp] theorem trace_identity : Matrix.trace (1 : M16) = 16 := by decide

theorem permRows_gram (σ : Equiv.Perm (Fin 16)) :
    permRows σ * (permRows σ)ᵀ = (4 : ℤ) • (1 : M16) + ones - (4 : ℤ) • permAdj σ := by
  ext u v
  have h := congrFun (congrFun row_matrix_gram (σ u)) (σ v)
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.one_apply,Equiv.apply_eq_iff_eq,permRows,permAdj,ones,signMatrix,Matrix.of_apply] using h

theorem ones_permAdj (σ : Equiv.Perm (Fin 16)) : ones * permAdj σ = (5 : ℤ) • ones := by
  ext u v
  change (∑ w, (1 : ℤ) * adjacency (σ w) (σ v)) = (5 : ℤ)
  simp only [one_mul]
  rw [Equiv.sum_comp σ (fun w => adjacency w (σ v))]
  exact adjacency_cols (σ v)

@[simp] theorem trace_permAdj (σ : Equiv.Perm (Fin 16)) : Matrix.trace (permAdj σ) = 0 := by
  simp [Matrix.trace,Matrix.diag,permAdj,adjacency]

/-- The integral overlap matrix really is one quarter of WᵀV. -/
theorem overlap_matrix_rescale (σ : Equiv.Perm (Fin 16)) :
    (4 : ℤ) • overlapMatrix σ = (permRows σ)ᵀ * signMatrix := by
  ext i j
  change (4 : ℤ) * overlap σ i j = _
  exact overlap_rescale σ i j

/-- No spectral computation is used: the squared Frobenius norm is exactly
the number of directed common edges of the two shared Clebsch graphs. -/
theorem overlap_frobenius (σ : Equiv.Perm (Fin 16)) :
    Matrix.trace ((overlapMatrix σ)ᵀ * overlapMatrix σ) =
      Matrix.trace (adjacency * permAdj σ) := by
  let V := signMatrix
  let W := permRows σ
  let B := overlapMatrix σ
  have hscale : (4 : ℤ) • B = Wᵀ * V := overlap_matrix_rescale σ
  have htrace : (16 : ℤ) * Matrix.trace (Bᵀ * B) =
      Matrix.trace ((V * Vᵀ) * (W * Wᵀ)) := by
    calc
      _ = Matrix.trace (((4 : ℤ) • B)ᵀ * ((4 : ℤ) • B)) := by
        simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,smul_smul]
        change 16 * _ = (4 * 4 : ℤ) * _
        norm_num
      _ = Matrix.trace ((Wᵀ * V)ᵀ * (Wᵀ * V)) := by rw [hscale]
      _ = Matrix.trace ((V * Vᵀ) * (W * Wᵀ)) := by
        rw [Matrix.transpose_mul,Matrix.transpose_transpose]
        calc
          Matrix.trace ((Vᵀ * W) * (Wᵀ * V)) = Matrix.trace ((Vᵀ * (W * Wᵀ)) * V) := by
            simp only [Matrix.mul_assoc]
          _ = Matrix.trace (V * (Vᵀ * (W * Wᵀ))) := Matrix.trace_mul_comm _ _
          _ = _ := by rw [Matrix.mul_assoc]
  have hexpand : Matrix.trace ((V * Vᵀ) * (W * Wᵀ)) =
      (16 : ℤ) * Matrix.trace (adjacency * permAdj σ) := by
    change Matrix.trace ((signMatrix * signMatrixᵀ) * (permRows σ * (permRows σ)ᵀ)) = _
    rw [row_matrix_gram,permRows_gram]
    simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.mul_sub,Matrix.mul_add,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
      ones_square,adjacency_ones,ones_permAdj,Matrix.trace_add,Matrix.trace_sub,
      Matrix.trace_smul,trace_identity,trace_ones,trace_adjacency,trace_permAdj,
      smul_smul,smul_eq_mul]
    ring
  rw [hexpand] at htrace
  change Matrix.trace (Bᵀ * B) = _
  omega

#print axioms overlap_frobenius
end PricingG.SignDesign
