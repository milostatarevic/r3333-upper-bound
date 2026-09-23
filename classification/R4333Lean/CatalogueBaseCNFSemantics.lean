import R4333Lean.CatalogueBaseCNF

/-!
# Semantics of the elementary catalogue normalizations

The catalogue LRAT formulas append only unit clauses to the canonical
good-colouring CNF.  This file proves their meaning once, directly from the
pairing-based variable convention in `FiniteColorCNF`.
-/

namespace R4333

namespace CatalogueBaseCNF

open FiniteColorCNF

/-- Satisfaction distributes over formula concatenation. -/
theorem satisfies_fmla_append {v : Sat.Valuation} {a b : Sat.Fmla}
    (ha : v.satisfies_fmla a) (hb : v.satisfies_fmla b) :
    v.satisfies_fmla (a ++ b) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with h | h
  · exact ha.prop clause h
  · exact hb.prop clause h

/-- A positive singleton clause has exactly its expected semantics. -/
theorem satisfies_pos_unit {v : Sat.Valuation} {atom : Nat}
    (h : v atom) : v.satisfies_fmla [[Sat.Literal.pos atom]] := by
  constructor
  intro clause hclause
  simp only [List.mem_singleton] at hclause
  subst clause
  change (¬v atom) → False
  exact fun hn => hn h

/-- A negative singleton clause has exactly its expected semantics. -/
theorem satisfies_neg_unit {v : Sat.Valuation} {atom : Nat}
    (h : ¬v atom) : v.satisfies_fmla [[Sat.Literal.neg atom]] := by
  constructor
  intro clause hclause
  simp only [List.mem_singleton] at hclause
  subst clause
  change v atom → False
  exact h

/-- A mapped family of positive unit clauses is satisfied pointwise. -/
theorem satisfies_map_pos_units {v : Sat.Valuation} {A : Type*}
    (xs : List A) (atom : A → Nat)
    (h : ∀ x ∈ xs, v (atom x)) :
    v.satisfies_fmla (xs.map fun x => [Sat.Literal.pos (atom x)]) := by
  constructor
  intro clause hclause
  simp only [List.mem_map] at hclause
  obtain ⟨x, hx, rfl⟩ := hclause
  exact (satisfies_pos_unit (h x hx)).prop _ (List.Mem.head _)

/-- A mapped family of negative unit clauses is satisfied pointwise. -/
theorem satisfies_map_neg_units {v : Sat.Valuation} {A : Type*}
    (xs : List A) (atom : A → Nat)
    (h : ∀ x ∈ xs, ¬v (atom x)) :
    v.satisfies_fmla (xs.map fun x => [Sat.Literal.neg (atom x)]) := by
  constructor
  intro clause hclause
  simp only [List.mem_map] at hclause
  obtain ⟨x, hx, rfl⟩ := hclause
  exact (satisfies_neg_unit (h x hx)).prop _ (List.Mem.head _)

/-- A mapped family of conditionally signed unit clauses is satisfied
pointwise.  This is the direct semantic form used by `selectRootPrefix`. -/
theorem satisfies_map_signed_units {v : Sat.Valuation} {A : Type*}
    (xs : List A) (atom : A → Nat) (selected : A → Bool)
    (hpos : ∀ x ∈ xs, selected x = true → v (atom x))
    (hneg : ∀ x ∈ xs, selected x = false → ¬v (atom x)) :
    v.satisfies_fmla
      (xs.map fun x => [if selected x then
        Sat.Literal.pos (atom x) else Sat.Literal.neg (atom x)]) := by
  constructor
  intro clause hclause
  simp only [List.mem_map] at hclause
  obtain ⟨x, hx, rfl⟩ := hclause
  cases hs : selected x
  · simp only [Bool.false_eq]
    exact (satisfies_neg_unit (hneg x hx hs)).prop _ (List.Mem.head _)
  · simp only [↓reduceIte]
    exact (satisfies_pos_unit (hpos x hx hs)).prop _ (List.Mem.head _)

/-- A concrete edge equality satisfies `setEdge`. -/
theorem coloring_satisfies_setEdge {n k a b q : Nat}
    (c : EdgeColoring (Fin n) (Fin k))
    (ha : a < n) (hb : b < n) (hq : q < k)
    (hcolor : c ⟨a, ha⟩ ⟨b, hb⟩ = ⟨q, hq⟩) :
    (coloringValuation c).satisfies_fmla (setEdge a b q) := by
  apply satisfies_pos_unit
  simp only [coloringValuation, edgeAtom, Nat.unpair_pair, ha, hb, hq,
    dite_true]
  exact hcolor

/-- A concrete edge inequality satisfies `forbidEdge`. -/
theorem coloring_satisfies_forbidEdge {n k a b q : Nat}
    (c : EdgeColoring (Fin n) (Fin k))
    (ha : a < n) (hb : b < n) (hq : q < k)
    (hcolor : c ⟨a, ha⟩ ⟨b, hb⟩ ≠ ⟨q, hq⟩) :
    (coloringValuation c).satisfies_fmla (forbidEdge a b q) := by
  apply satisfies_neg_unit
  simp only [coloringValuation, edgeAtom, Nat.unpair_pair, ha, hb, hq,
    dite_true]
  exact hcolor

/-- The literal K16 base has the semantics of the canonical base formula. -/
theorem coloring_satisfies_k16BaseLiteral
    (c : EdgeColoring (Fin 16) (Fin 3))
    (hc : NoMonochromaticTriangle c) :
    (coloringValuation (n := 16) (k := 3) c).satisfies_fmla k16BaseLiteral := by
  rw [k16BaseLiteral_eq]
  exact coloring_satisfies_goodColoringFmla c hc

/-- The literal K15 base has the semantics of the canonical base formula. -/
theorem coloring_satisfies_k15BaseLiteral
    (c : EdgeColoring (Fin 15) (Fin 3))
    (hc : NoMonochromaticTriangle c) :
    (coloringValuation (n := 15) (k := 3) c).satisfies_fmla k15BaseLiteral := by
  rw [k15BaseLiteral_eq]
  exact coloring_satisfies_goodColoringFmla c hc

#print axioms R4333.CatalogueBaseCNF.coloring_satisfies_setEdge
#print axioms R4333.CatalogueBaseCNF.coloring_satisfies_forbidEdge
#print axioms R4333.CatalogueBaseCNF.coloring_satisfies_k16BaseLiteral

end CatalogueBaseCNF

end R4333
