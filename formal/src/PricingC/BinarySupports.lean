import PricingC.GParityMatrix

namespace PricingC.GParity
open Finset Matrix

 def columnSupport {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (j : V) : Finset V := univ.filter fun x => P x j = 1

 theorem binary_mul_indicator : ∀ a b : ZMod 2,
    a * b = if a = 1 ∧ b = 1 then 1 else 0 := by decide

 theorem binary_square_self : ∀ a : ZMod 2, a * a = a := by decide

 theorem binary_column_dot {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (i j : V) :
    (Pᵀ * P) i j = ((columnSupport P i ∩ columnSupport P j).card : ZMod 2) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp_rw [binary_mul_indicator]
  have heq : univ.filter (fun x => P x i = 1 ∧ P x j = 1) =
      columnSupport P i ∩ columnSupport P j := by ext x; simp [columnSupport]
  rw [←sum_filter]
  simp only [heq,sum_const,nsmul_eq_mul,mul_one]

 theorem binary_column_odd {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (hP : Pᵀ * P = 1) (j : V) : Odd (columnSupport P j).card := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  have h := congrArg (fun M : Matrix V V (ZMod 2) => M j j) hP
  rw [binary_column_dot,inter_self] at h
  simpa only [Matrix.one_apply_eq] using h

 theorem binary_columns_even {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (hP : Pᵀ * P = 1) (i j : V) (hij : i ≠ j) :
    Even (columnSupport P i ∩ columnSupport P j).card := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have h := congrArg (fun M : Matrix V V (ZMod 2) => M i j) hP
  rw [binary_column_dot] at h
  simpa only [Matrix.one_apply_ne hij] using h

 theorem binary_columns_injective {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (hP : Pᵀ * P = 1) : Function.Injective (columnSupport P) := by
  intro i j heq
  by_contra hij
  have he := binary_columns_even P hP i j hij
  rw [heq,inter_self] at he
  have ho := binary_column_odd P hP j
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := ho
  omega

 theorem binary_row_odd {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (hP : P * Pᵀ = 1) (j : V) :
    Odd (univ.filter fun x => P j x = 1).card := by
  exact binary_column_odd Pᵀ (by simpa only [Matrix.transpose_transpose] using hP) j

 theorem binary_rows_even {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (hP : P * Pᵀ = 1) (i j : V) (hij : i ≠ j) :
    Even (univ.filter fun x => P i x = 1 ∧ P j x = 1).card := by
  have h := binary_columns_even Pᵀ (by simpa only [Matrix.transpose_transpose] using hP) i j hij
  have heq : columnSupport Pᵀ i ∩ columnSupport Pᵀ j =
      univ.filter (fun x => P i x = 1 ∧ P j x = 1) := by ext x; simp [columnSupport]
  rwa [heq] at h

 theorem columnSupport_unit {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V (ZMod 2)) (j a : V)
    (h : ∀ x, P x j = (1 : Matrix V V (ZMod 2)) x a) : columnSupport P j = {a} := by
  ext x
  simp only [columnSupport,mem_filter,mem_univ,true_and,h,Matrix.one_apply,mem_singleton]
  by_cases hx : x = a <;> simp [hx]

#print axioms binary_columns_injective
#print axioms binary_rows_even
end PricingC.GParity
