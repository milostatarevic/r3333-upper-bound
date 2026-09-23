import PricingG.SignMatrix

namespace PricingG.SignDesign
open Finset

/-- An explicit exhaustive finite boundary for integer vectors with a given
l1 budget. The recursive budget prevents a Cartesian9^5 enumeration. -/
def boundedVectors : (n budget : Nat) → List (Fin n → ℤ)
  | 0, _ => [Fin.elim0]
  | n+1, budget => (List.finRange (2*budget+1)).flatMap fun j =>
      let a : ℤ := (j.val : ℤ) - budget
      (boundedVectors n (budget - a.natAbs)).map (Fin.cons a)

theorem boundedVectors_complete (n budget : Nat) (b : Fin n → ℤ)
    (hb : ∑ i, (b i).natAbs ≤ budget) : b ∈ boundedVectors n budget := by
  induction n generalizing budget with
  | zero =>
    have heq : b = Fin.elim0 := by funext i; exact i.elim0
    simp [boundedVectors,heq]
  | succ n ih =>
    have hsum : (b 0).natAbs + ∑ i : Fin n, (b i.succ).natAbs ≤ budget := by
      simpa only [Fin.sum_univ_succ] using hb
    have hhead : (b 0).natAbs ≤ budget := by omega
    have hcast : |b 0| ≤ (budget : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hhead
    have hlo : -(budget : ℤ) ≤ b 0 := (abs_le.mp hcast).1
    have hhi : b 0 ≤ (budget : ℤ) := (abs_le.mp hcast).2
    let j : Fin (2*budget+1) := ⟨(b 0 + budget).toNat,by omega⟩
    have hj : (j.val : ℤ) - budget = b 0 := by dsimp [j]; omega
    have ht : ∑ i : Fin n, (b i.succ).natAbs ≤ budget - (b 0).natAbs := by omega
    change b ∈ (List.finRange (2*budget+1)).flatMap _
    apply List.mem_flatMap.mpr
    refine ⟨j,by simp,?_⟩
    apply List.mem_map.mpr
    refine ⟨fun i => b i.succ,?_,?_⟩
    · rw [hj]
      exact ih _ _ ht
    · rw [hj]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl

def squareNorm (b : Fin 5 → ℤ) : Nat := ∑ i, (b i).natAbs ^ 2

def fourEvaluations (b : Fin 5 → ℤ) : Nat :=
  (univ.filter fun u : Fin 16 => |∑ i, row u i * b i| = 4).card

def columnData (b : Fin 5 → ℤ) : Nat × Nat := (squareNorm b,fourEvaluations b)

def permittedColumnData : Finset (Nat × Nat) :=
  {(16,16),(10,8),(8,8),(6,4),(4,2),(4,0),(2,0)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The complete seven shape/energy/evaluation possibilities, including all
coefficient signs and all coordinate placements. -/
theorem bounded_column_data_check :
    (boundedVectors 5 4).all (fun b => decide
      ((Even (∑ i, (b i).natAbs) ∧ b ≠ 0) → columnData b ∈ permittedColumnData)) = true := by
  decide

theorem column_data_exhaustive (b : Fin 5 → ℤ)
    (hbound : ∑ i, (b i).natAbs ≤ 4) (heven : Even (∑ i, (b i).natAbs)) (hne : b ≠ 0) :
    columnData b ∈ permittedColumnData := by
  have h := List.all_eq_true.mp bounded_column_data_check b (boundedVectors_complete 5 4 b hbound)
  exact (of_decide_eq_true h) ⟨heven,hne⟩

#print axioms boundedVectors_complete
#print axioms column_data_exhaustive
end PricingG.SignDesign
