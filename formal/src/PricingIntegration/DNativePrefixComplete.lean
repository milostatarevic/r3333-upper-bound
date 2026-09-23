import PricingIntegration.DNativePrefix

set_option autoImplicit false
namespace PricingIntegration.DNativePrefix
open Ramsey61 Ramsey61.DenseCounter
open Ramsey61.CEncodingCore (palette)
open PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.DFrameColoring PricingIntegration.NativePrimaryCore

def base (five : Bool) (t : Types) : CNF := if five then fiveFormula t else fourFormula t

/-- Every native D prefix has one satisfying extension with all physical
edge atoms preserved. D auxiliaries need not preserve A/B's high-flag range. -/
theorem satisfying_extension {c : Host} (five : Bool) (f : Frame c (layout five))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) :
    ∃v : Valuation,FormulaSat v (base five t) ∧
      ∀u w : Fin (vertexCount (layout five)),∀q : Fin 4,u≠w →
        (v (edgeVar u w q)=true ↔ c (f.vertex u) (f.vertex w)=palette q) := by
  cases five
  · exact ⟨fourValuation f,four_satisfied f t hg hc,four_edge f⟩
  · exact ⟨fiveValuation f t hg hc,five_satisfied f t hg hc,five_edge f t hg hc⟩

#check satisfying_extension
#print axioms satisfying_extension
end PricingIntegration.DNativePrefix
