import UniformK60.MarkedBounds
import UniformK60.CEntranceFormula
import UniformK60.BalancedEncodingBraces
import UniformK60.BalancedEncodingAllFive

/-! The explicit computational boundary of the K60 argument.
Each tagged case denotes the exact CNF emitted for a fresh K60 solve. -/
set_option autoImplicit false
namespace UniformK60.ExactInputs
open Ramsey61

abbrev AllFiveCase := Fin 3
def allFiveOwner : AllFiveCase → BalancedHost.Owner := ![(false,false),(false,true),(true,true)]

abbrev Case := ABDFormula.Case ⊕ EFormula.Case ⊕ CEntranceFormula.Case ⊕
  BalancedEncodingBraces.Case ⊕ AllFiveCase

def formula : Case → DenseCounter.CNF
  | .inl k => ABDFormula.formula k
  | .inr (.inl k) => EFormula.formula k
  | .inr (.inr (.inl k)) => CEntranceFormula.formula k
  | .inr (.inr (.inr (.inl k))) => BalancedEncodingBraces.formula k
  | .inr (.inr (.inr (.inr k))) => BalancedEncodingAllFive.formula (allFiveOwner k)

/-- Native solver outcomes are not axioms of Lean. This is the explicit
external premise, to be supported by exact-input native evidence audits. -/
def AllUnsat : Prop := ∀ k : Case,∀ v : DenseCounter.Valuation,
  ¬DenseCounter.FormulaSat v (formula k)

theorem abd_excluded (h : AllUnsat) : MarkedBounds.ABDExcluded := by
  intro k hv
  obtain ⟨v,hv⟩ := hv
  exact h (.inl k) v hv

theorem e_excluded (h : AllUnsat) : MarkedBounds.EExcluded := by
  intro k hv
  obtain ⟨v,hv⟩ := hv
  exact h (.inr (.inl k)) v hv

theorem entrance_excluded (h : AllUnsat) (k : CEntranceFormula.Case)
    (v : DenseCounter.Valuation) : ¬DenseCounter.FormulaSat v (CEntranceFormula.formula k) :=
  h (.inr (.inr (.inl k))) v

theorem mixed_excluded (h : AllUnsat) (k : BalancedEncodingBraces.Case)
    (v : DenseCounter.Valuation) : ¬DenseCounter.FormulaSat v (BalancedEncodingBraces.formula k) :=
  h (.inr (.inr (.inr (.inl k)))) v

theorem all_five_excluded (h : AllUnsat) (o : BalancedHost.Owner)
    (ho : o=(false,false) ∨ o=(false,true) ∨ o=(true,true))
    (v : DenseCounter.Valuation) : ¬DenseCounter.FormulaSat v (BalancedEncodingAllFive.formula o) := by
  rcases ho with rfl | rfl | rfl
  · exact h (.inr (.inr (.inr (.inr 0)))) v
  · exact h (.inr (.inr (.inr (.inr 1)))) v
  · exact h (.inr (.inr (.inr (.inr 2)))) v

#print axioms abd_excluded
#print axioms all_five_excluded
end UniformK60.ExactInputs
