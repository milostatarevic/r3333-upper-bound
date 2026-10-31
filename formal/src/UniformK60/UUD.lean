import UniformK60.UUFiniteBridge
import UniformK60.ABDFormula

set_option autoImplicit false
namespace UniformK60.UUD
open Ramsey61 UniformK61.UUSupportData UniformK60.UUSourceFacts
open UniformK61.UUBridgeData

/-- Every native U/U word action fixes the omitted free position14. -/
theorem fixes_omission (q : Bool) (a : Action) :
    vertices q a (14 : Fin 61)=14 := by
  rfl

theorem reference_to_exact_D {q : Bool} {p : Pair} {i : Fin 600}
    {c : UnitRestriction.ReferenceColoring} (w : SourceFacts q p i c)
    (hc : NoMonochromaticTriangle (UnitRestriction.restrictColoring c 14)) :
    ∃ j : UniformK61.MarkedUU.Leaf, ∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (ABDFormula.formula (.inr (q,j))) := by
  obtain ⟨v,hv⟩ := UUFiniteBridge.restricted_satisfiable w 14 14 (fixes_omission q _) hc
  exact ⟨UniformK61.UUData.leaf (target p i),v,hv⟩

#print axioms reference_to_exact_D
end UniformK60.UUD
