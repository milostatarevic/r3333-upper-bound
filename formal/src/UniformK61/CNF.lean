import Mathlib.Tactic

/-! Boolean clause semantics and preservation under valuation agreement. -/
namespace Ramsey61.DenseCounter

abbrev Literal := Bool × Nat
abbrev CNF := List (List Literal)
abbrev Valuation := Nat → Bool

def ClauseSat (v : Valuation) (clause : List Literal) : Prop :=
  ∃ literal ∈ clause, v literal.2 = literal.1

def FormulaSat (v : Valuation) (formula : CNF) : Prop :=
  ∀ clause ∈ formula, ClauseSat v clause

@[simp] theorem formulaSat_append (v : Valuation) (first second : CNF) :
    FormulaSat v (first ++ second) ↔ FormulaSat v first ∧ FormulaSat v second := by
  simp [FormulaSat, or_imp, forall_and]

/-- Satisfaction depends only on the variables occurring in the formula. -/
theorem formulaSat_congr_below (v w : Valuation) (f : CNF) (bound : Nat)
    (hb : ∀ c ∈ f, ∀ l ∈ c, l.2 < bound)
    (he : ∀ a < bound, w a = v a) (hs : FormulaSat v f) : FormulaSat w f := by
  intro c hc
  obtain ⟨l,hl,hv⟩ := hs c hc
  exact ⟨l,hl,(he l.2 (hb c hc l hl)).trans hv⟩

end Ramsey61.DenseCounter
