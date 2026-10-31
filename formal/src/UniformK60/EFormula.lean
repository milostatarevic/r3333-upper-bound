import UniformK60.ABDFormula

/-!
The reduced E input family uses the four ordered type patterns UUU,UUT,
UTT,TTT. A source D reference supplies only signed facts; no theorem
about the satisfiability of its K61 formula is used.
-/

set_option autoImplicit false
namespace UniformK60.EFormula
open PricingABD.ABLayout

def omissionCount (twisted : Bool) : Nat := if twisted then 9 else 3

def omissionPosition : (twisted : Bool) → Fin (omissionCount twisted) → Fin 15
  | false, i => ⟨i.val, by have := i.isLt; change i.val < 3 at this; omega⟩
  | true, i => (![0,1,2,4,5,6,7,9,12] : Fin 9 → Fin 15) i

def omission (twisted : Bool) (i : Fin (omissionCount twisted)) :
    UnitRestriction.Omission :=
  ⟨45 + (omissionPosition twisted i).val, by have := (omissionPosition twisted i).isLt; omega⟩

abbrev UUCase := (twisted : Bool) ×
  (UniformK61.MarkedUU.Leaf × Fin (omissionCount twisted))

/-- The two mixed D source families whose marked template is T. -/
def mixedEligible (k : ABDFormula.CommonCase) : Prop :=
  k.1.profile = .D ∧ k.2.1.marked = true

instance (k : ABDFormula.CommonCase) : Decidable (mixedEligible k) := by
  unfold mixedEligible
  infer_instance

abbrev MixedSource := {k : ABDFormula.CommonCase // mixedEligible k}
abbrev MixedCase := MixedSource × Fin 9
abbrev Case := UUCase ⊕ MixedCase

def referenceUnits : Case → List UnitRestriction.ReferenceUnit
  | .inl ⟨twisted, k, _⟩ =>
      ReferenceSource.units (UniformK61.MarkedUU.caseUnits twisted k)
  | .inr ⟨k, _⟩ => ABDFormula.commonReferenceUnits k.val

def deleted : Case → UnitRestriction.Omission
  | .inl ⟨twisted, _, i⟩ => omission twisted i
  | .inr ⟨_, i⟩ => omission true i

def units (k : Case) : List Core.PhysicalUnit :=
  UnitRestriction.sortedRestriction (deleted k) (referenceUnits k)

def formula (k : Case) : Ramsey61.DenseCounter.CNF := Core.formula (units k)

theorem uu_case_count : Fintype.card UUCase = 8148 := by
  decide +kernel

end UniformK60.EFormula
