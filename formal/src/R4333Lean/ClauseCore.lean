import R4333Lean.FiniteColorCNF

/-!
# Semantically sound clause-core selection

An LRAT backward trim may retain only selected initial clauses.  The indices
are untrusted data, so selection uses total list lookup.  The theorem below
shows in the kernel that every selected clause came from the original formula;
therefore any valuation satisfying the full formula also satisfies the core.
-/

namespace R4333
namespace ClauseCore

/-- Select in the supplied index order, silently omitting out-of-range
indices.  Concrete certificate modules definitionally compare this list with
their trimmed DIMACS input. -/
def select {α : Type*} (source : List α) : List Nat → List α
  | [] => []
  | index :: indices =>
      match source[index]? with
      | none => select source indices
      | some value => value :: select source indices

theorem mem_source_of_mem_select {α : Type*} (source : List α)
    (indices : List Nat) {value : α} :
    value ∈ select source indices → value ∈ source := by
  induction indices with
  | nil => simp [select]
  | cons index indices ih =>
      simp only [select]
      split <;> rename_i hlookup
      · exact ih
      · intro hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact List.mem_of_getElem? hlookup
        · exact ih htail

theorem satisfies_select (valuation : Sat.Valuation) (formula : Sat.Fmla)
    (indices : List Nat) (hformula : valuation.satisfies_fmla formula) :
    valuation.satisfies_fmla (select formula indices) := by
  constructor
  intro clause hclause
  exact hformula.prop clause
    (mem_source_of_mem_select formula indices hclause)

/-- Linear-time selection for a strictly increasing index list encoded as
gaps: the first gap is the first zero-based index; every later gap is the
number of unselected clauses between consecutive selected clauses.  Passing
the tail after each selected element makes reduction linear in the source
formula rather than repeatedly indexing from its head. -/
def selectGaps {α : Type*} (source : List α) : List Nat → List α
  | [] => []
  | gap :: gaps =>
      match source.drop gap with
      | [] => []
      | value :: tail => value :: selectGaps tail gaps

theorem mem_source_of_mem_selectGaps {α : Type*} (source : List α)
    (gaps : List Nat) {value : α} :
    value ∈ selectGaps source gaps → value ∈ source := by
  induction gaps generalizing source with
  | nil => simp [selectGaps]
  | cons gap gaps ih =>
      simp only [selectGaps]
      generalize hdrop : source.drop gap = dropped
      cases dropped with
      | nil => simp
      | cons head tail =>
          intro hmem
          change value ∈ head :: selectGaps tail gaps at hmem
          have hdropped : List.Sublist (head :: tail) source := by
            rw [← hdrop]
            exact List.drop_sublist gap source
          rcases List.mem_cons.mp hmem with rfl | htail
          · exact hdropped.subset (List.Mem.head tail)
          · exact hdropped.subset (List.Mem.tail head (ih tail htail))

theorem satisfies_selectGaps (valuation : Sat.Valuation)
    (formula : Sat.Fmla) (gaps : List Nat)
    (hformula : valuation.satisfies_fmla formula) :
    valuation.satisfies_fmla (selectGaps formula gaps) := by
  constructor
  intro clause hclause
  exact hformula.prop clause
    (mem_source_of_mem_selectGaps formula gaps hclause)

/-- Satisfaction is preserved by concatenating two independently satisfied
formula fragments. -/
theorem satisfies_append (valuation : Sat.Valuation)
    (first second : Sat.Fmla)
    (hfirst : valuation.satisfies_fmla first)
    (hsecond : valuation.satisfies_fmla second) :
    valuation.satisfies_fmla (first ++ second) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · exact hfirst.prop clause hclause
  · exact hsecond.prop clause hclause

theorem no_full_model_of_core_refutation (formula : Sat.Fmla)
    (indices : List Nat)
    (hcore : Sat.Fmla.proof (select formula indices) Sat.Clause.nil) :
    ¬∃ valuation : Sat.Valuation, valuation.satisfies_fmla formula := by
  rintro ⟨valuation, hvaluation⟩
  exact hcore valuation (satisfies_select valuation formula indices hvaluation)

#print axioms R4333.ClauseCore.satisfies_select
#print axioms R4333.ClauseCore.satisfies_selectGaps
#print axioms R4333.ClauseCore.satisfies_append
#print axioms R4333.ClauseCore.no_full_model_of_core_refutation

end ClauseCore
end R4333
