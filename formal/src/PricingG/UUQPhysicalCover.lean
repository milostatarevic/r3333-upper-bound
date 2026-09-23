import PricingG.UUQPhysicalExtension
import PricingG.UUUSelectedSatisfaction
import PricingG.UUTSelectedSatisfaction

set_option autoImplicit false
namespace PricingG.UUQPhysicalCover
open Ramsey61
open PricingABD.ABLayout PricingABD.ABGeometry
open CompletionC.CommonBlocks

/-- The very supplied U/U/U blocks supply one original679 formula. The
full actual K14 and the same fixed three critical-cell maps enter the split. -/
theorem uuu {c : Host} {five : Bool}
    (b : Blocks c ⟨.D,five⟩ ⟨false,false,false⟩) (hc : NoMonochromaticTriangle c) :
    UUUSelectedSatisfaction.SomeLeafSatisfiable := by
  rcases UUQPhysicalExtension.selected_split b hc with ⟨e,he⟩ | ⟨e,he⟩
  · exact UUUSelectedSatisfaction.four_support_supplies_leaf e he
  · exact UUUSelectedSatisfaction.five_support_supplies_leaf e he

/-- Q16 remains twisted throughout. No fresh classification, U/T choice,
physical owner, or substitute coloring is supplied as an extra premise. -/
theorem uut {c : Host} {five : Bool}
    (b : Blocks c ⟨.D,five⟩ ⟨false,false,true⟩) (hc : NoMonochromaticTriangle c) :
    UUTSelectedSatisfaction.SomeLeafSatisfiable := by
  rcases UUQPhysicalExtension.selected_split b hc with ⟨e,he⟩ | ⟨e,he⟩
  · exact UUTSelectedSatisfaction.four_support_supplies_leaf e he
  · exact UUTSelectedSatisfaction.five_support_supplies_leaf e he

#print axioms uuu
#print axioms uut
end PricingG.UUQPhysicalCover
