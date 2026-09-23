import Ramsey61.DenseCounter

namespace PricingIntegration.FoldedThreshold
open Ramsey61.DenseCounter

abbrev Lit := Bool × Nat
abbrev Known := Nat → Option Bool

def value (v : Valuation) (l : Lit) : Bool := v l.2 == l.1
def knownValue (k : Known) (l : Lit) : Option Bool := (k l.2).map (fun b => b == l.1)
def unknown (k : Known) (xs : List Lit) : List Lit :=
  xs.filter (fun l => (knownValue k l).isNone)
def trueFixed (k : Known) (xs : List Lit) : Nat :=
  xs.countP (fun l => knownValue k l == some true)
def count (v : Valuation) (xs : List Lit) : Nat := xs.countP (value v)
def Sound (v : Valuation) (k : Known) : Prop :=
  ∀ a b, k a = some b → v a = b

/-- Folding only already justified constants preserves the exact signed
literal count. This is the mathematical invariant of the archived A/B
threshold compiler's prefix-constant optimization. -/
theorem count_split (v : Valuation) (k : Known) (hsound : Sound v k) (xs : List Lit) :
    count v xs = trueFixed k xs + count v (unknown k xs) := by
  induction xs with
  | nil => simp [count, trueFixed, unknown]
  | cons l xs ih =>
    rcases l with ⟨sign, atom⟩
    cases hk : k atom with
    | none =>
      simp only [count, trueFixed, unknown, List.countP_cons, List.filter_cons,
        knownValue, hk, Option.map_none, Option.isNone_none, if_true] at ih ⊢
      simp [value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ih]
    | some b =>
      have hv := hsound atom b hk
      cases sign <;> cases b <;>
        simp_all [count, trueFixed, unknown, knownValue, value, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]

/-- The early true/false branches and the reduced target used by the exact
threshold compiler are justified without imposing any extra host constraint. -/
theorem folded_threshold_iff (v : Valuation) (k : Known) (hsound : Sound v k)
    (xs : List Lit) (target : Nat) :
    target ≤ count v xs ↔
      if target ≤ trueFixed k xs then True
      else if (unknown k xs).length < target - trueFixed k xs then False
      else target - trueFixed k xs ≤ count v (unknown k xs) := by
  rw [count_split v k hsound xs]
  have hb : count v (unknown k xs) ≤ (unknown k xs).length := List.countP_le_length
  split_ifs <;> (try simp only [iff_true, iff_false]) <;> omega

/-- A fresh counter's guarded lower bound is exactly the intended necessary
condition. A selectable highness proxy supplies an implication, not a converse. -/
theorem guarded_lower_iff (gate top : Bool) :
    (!gate || top) = true ↔ (gate = true → top = true) := by
  cases gate <;> cases top <;> decide

/-- Upper bounds query threshold(k+1) and negate it. -/
theorem upper_threshold_iff (actual limit : Nat) :
    ¬ limit + 1 ≤ actual ↔ actual ≤ limit := by omega

end PricingIntegration.FoldedThreshold
