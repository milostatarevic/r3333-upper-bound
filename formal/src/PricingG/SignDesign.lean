import PricingC.CanonicalGraph

namespace PricingG.SignDesign
open Finset Matrix PricingC

/-- Even-parity sign representation in the same XOR vertex labels used by
our physical Clebsch coordinates. Powers of two act by four sign flips. -/
def row (u : Fin 16) : Fin 5 → ℤ :=
  match u.val with
  | 0 => ![1, 1, 1, 1, 1]
  | 1 => ![1, -1, -1, -1, -1]
  | 2 => ![-1, 1, -1, -1, -1]
  | 3 => ![-1, -1, 1, 1, 1]
  | 4 => ![-1, -1, 1, -1, -1]
  | 5 => ![-1, 1, -1, 1, 1]
  | 6 => ![1, -1, -1, 1, 1]
  | 7 => ![1, 1, 1, -1, -1]
  | 8 => ![-1, -1, -1, 1, -1]
  | 9 => ![-1, 1, 1, -1, 1]
  | 10 => ![1, -1, 1, -1, 1]
  | 11 => ![1, 1, -1, 1, -1]
  | 12 => ![1, 1, -1, -1, 1]
  | 13 => ![1, -1, 1, 1, -1]
  | 14 => ![-1, 1, 1, 1, -1]
  | _ => ![-1, -1, -1, -1, 1]

theorem row_entries : ∀ u i, row u i = 1 ∨ row u i = -1 := by decide

theorem column_balance : ∀ i, ∑ u, row u i = 0 := by decide

theorem column_gram : ∀ i j, ∑ u, row u i * row u j = if i = j then 16 else 0 := by decide

theorem row_gram : ∀ u v, ∑ i, row u i * row v i =
    if u = v then 5 else if xorGraph.Adj u v then -3 else 1 := by decide

/-- Absolute sign evaluations cover all 32 choices of signs; this uses the
odd dimension and retains every vertex of the sixteen-row design. -/
theorem every_sign_up_to_negation : ∀ s : Fin 5 → Bool,
    ∃ u : Fin 16, (∀ i, row u i = if s i then 1 else -1) ∨
      (∀ i, row u i = -(if s i then 1 else -1 : ℤ)) := by decide

/-- Each intrinsic neighborhood has centroid -3 times its center. -/
theorem neighborhood_centroid : ∀ u i,
    ∑ v ∈ xorGraph.neighborFinset u, row v i = -3 * row u i := by decide

#print axioms row_gram
#print axioms every_sign_up_to_negation
#print axioms neighborhood_centroid
end PricingG.SignDesign
