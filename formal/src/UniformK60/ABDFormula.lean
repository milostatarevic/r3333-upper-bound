import UniformK60.ReferenceSource
import UniformK61.CommonFormula
import UniformK61.MarkedUU
import CompletionC.CommonCaseCount

/-!
The original360/5096/50918 A/B/D reference boundary, restricted only in
the free complement. Formula definitions alone do not assert coverage.
The K60 host-to-case proofs are supplied separately.
-/

set_option autoImplicit false
namespace UniformK60.ABDFormula
open PricingABD.ABLayout

abbrev CommonCase := CompletionC.CommonCases.Case
abbrev Case := CommonCase ⊕ (Bool × UniformK61.MarkedUU.Leaf)

def commonReferenceUnits (k : CommonCase) : List UnitRestriction.ReferenceUnit :=
  ReferenceSource.units
    (UniformK61.CommonFormula.units k.1 k.2.1 k.2.2.1.val k.2.2.2)

/-- Last vertex of the untemplated free cell in the61-position reference. -/
def commonOmission (l : Layout) : UnitRestriction.Omission :=
  ⟨lowSize l, by have h := sizes l; omega⟩

def referenceUnits : Case → List UnitRestriction.ReferenceUnit
  | .inl k => commonReferenceUnits k
  | .inr (twisted, k) => ReferenceSource.units (UniformK61.MarkedUU.caseUnits twisted k)

def omission : Case → UnitRestriction.Omission
  | .inl k => commonOmission k.1
  | .inr _ => 14

def units (k : Case) : List Core.PhysicalUnit :=
  UnitRestriction.sortedRestriction (omission k) (referenceUnits k)

def formula (k : Case) : Ramsey61.DenseCounter.CNF := Core.formula (units k)

theorem omission_by_profile (l : Layout) :
    (commonOmission l).val = match l.profile with | .A => 12 | .B => 13 | .D => 14 := by
  rcases l with ⟨p, five⟩
  cases p <;> cases five <;> rfl

theorem native_case_count : Fintype.card Case = 56374 := by
  simp only [Case, CommonCase, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool, UniformK61.MarkedUU.Leaf, UniformK61.UUData.Leaf,
    Fintype.card_fin, CompletionC.CommonCaseCount.native_case_count]

#print axioms native_case_count
end UniformK60.ABDFormula
