import PricingG.MultiSparseCounter

namespace PricingIntegration.MultiSparseCounter
open Finset

theorem start_zero {N : Nat} (base : Nat) (sz : Fin (N + 1) → Nat) :
    start base sz 0 = base := by simp [start]

theorem start_succ {N : Nat} (base : Nat) (sz : Fin (N + 1) → Nat) (i : Fin N) :
    start base sz i.succ = start base sz i.castSucc + sz i.castSucc := by
  have he : Iio i.succ = insert i.castSucc (Iio i.castSucc) := by
    ext j
    simp only [mem_Iio,mem_insert,Fin.lt_def]
    constructor
    · intro h
      by_cases hj : j = i.castSucc
      · exact Or.inl hj
      · right
        have hn : j.val ≠ i.val := by intro he; exact hj (Fin.ext he)
        change j.val < i.val
        change j.val < i.val + 1 at h
        omega
    · rintro (rfl | h)
      · exact Nat.lt_succ_self _
      · change j.val < i.val + 1
        change j.val < i.val at h
        omega
  unfold start
  rw [he,sum_insert (by simp)]
  omega

/-- Literal producer starts need only the first address and adjacent
increments checked; the cumulative disjoint namespace then follows. -/
theorem starts_eq_of_adjacent {N : Nat} (base : Nat) (sz actual : Fin (N + 1) → Nat)
    (h0 : actual 0 = base)
    (hs : ∀ i : Fin N, actual i.succ = actual i.castSucc + sz i.castSucc) :
    ∀ i, actual i = start base sz i := by
  intro i
  induction i using Fin.induction with
  | zero => rw [h0,start_zero]
  | succ i ih => rw [hs,start_succ,ih]

#print axioms starts_eq_of_adjacent
end PricingIntegration.MultiSparseCounter
