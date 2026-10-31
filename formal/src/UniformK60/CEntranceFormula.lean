import UniformK60.ReferenceSource
import UniformK61.CEntranceCatalogueData

/-!
The exact692 C1 and7840 C2 input definitions, retaining the original
unit order of the frozen entrance catalogue. A fresh complete K60 base
is always used. Coverage is proved independently of these definitions.
-/

set_option autoImplicit false
namespace UniformK60.CEntranceFormula
open UnitRestriction

abbrev SourceCase := Fin 346
abbrev C1Case := SourceCase × Bool

def referenceUnits (k : SourceCase) : List ReferenceUnit :=
  ReferenceSource.units (UniformK61.CEntrance.Formula.units
    (UniformK61.CEntrance.Catalogue.five k)
    (UniformK61.CEntrance.Catalogue.leftType k)
    (UniformK61.CEntrance.Catalogue.rightType k)
    (UniformK61.CEntrance.Catalogue.pair k)
    (UniformK61.CEntrance.Catalogue.rep k))

/-- False selects the first free-complement position; true selects the
first nonmark position of the untemplated marked group. -/
def c1Omission (k : C1Case) : Omission :=
  if k.2 then 47 else if UniformK61.CEntrance.Catalogue.five k.1 then 6 else 5

def c1Units (k : C1Case) : List Core.PhysicalUnit :=
  restrictUnits (c1Omission k) (referenceUnits k.1)

def c1Formula (k : C1Case) : Ramsey61.DenseCounter.CNF := Core.formula (c1Units k)

def c2Allowed (k : SourceCase) (d : Omission) : Prop :=
  let p := UniformK61.CEntrance.Catalogue.pair k
  (15 ≤ d.val ∧ d.val < 31 ∧
    d.val - 15 ∉ (PricingIntegration.PairAdmission.retained p).left) ∨
  (31 ≤ d.val ∧ d.val < 47 ∧
    d.val - 31 ∉ (PricingIntegration.PairAdmission.retained p).right)

instance (k : SourceCase) (d : Omission) : Decidable (c2Allowed k d) := by
  unfold c2Allowed
  infer_instance

abbrev C2Case := (k : SourceCase) × {d : Omission // c2Allowed k d}

def c2Units (k : C2Case) : List Core.PhysicalUnit :=
  restrictUnits k.2.val (referenceUnits k.1)

def c2Formula (k : C2Case) : Ramsey61.DenseCounter.CNF := Core.formula (c2Units k)

abbrev Case := C1Case ⊕ C2Case

def formula : Case → Ramsey61.DenseCounter.CNF
  | .inl k => c1Formula k
  | .inr k => c2Formula k

theorem c1_case_count : Fintype.card C1Case = 692 := by
  simp [C1Case, SourceCase]

end UniformK60.CEntranceFormula
