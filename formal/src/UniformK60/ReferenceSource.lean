import UniformK60.UnitRestriction
import UniformK61.Core

/-! Reuse of published signed reference facts, without importing their
whole-host satisfiability or exclusion theorems into the K60 argument. -/

set_option autoImplicit false
namespace UniformK60.ReferenceSource

def unit (u : UniformK61.Core.PhysicalUnit) : UnitRestriction.ReferenceUnit :=
  ⟨u.positive, u.u, u.v, u.q⟩

def units (us : List UniformK61.Core.PhysicalUnit) :
    List UnitRestriction.ReferenceUnit := us.map unit

theorem reference_matches (c : UnitRestriction.ReferenceColoring)
    (u : UniformK61.Core.PhysicalUnit) :
    UnitRestriction.referenceMatches c (unit u) ↔ UniformK61.Core.UnitMatches c u := by
  rfl

end UniformK60.ReferenceSource
