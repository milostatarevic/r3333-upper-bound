import PricingABD.TemplateNormalization
namespace PricingABD.NativeTemplateDegreeProfiles
open R4333
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
 def rowCount {n:Nat} (c:EdgeColoring (Fin n) ThreeColor) (u:Fin n) (q:ThreeColor) : Nat :=
   ((List.finRange n).filter (fun v => decide (u≠v ∧ c u v=q))).length
 /-- Both literal K16 templates contribute exactly five known true entries to
 each off-diagonal color row. Thus their different fixed colors do not change
 row-threshold folding counts. -/
 theorem k16_rows : ∀t:Bool,∀u:Fin 16,∀q:ThreeColor,rowCount (k16Template t) u q=5 := by
   decide +kernel
 /-- The literal K15 row has four entries precisely in the color lost on
 deleting the distinguished sixteenth vertex, and five in each other color. -/
 theorem k15_rows : ∀t:Bool,∀u:Fin 15,∀q:ThreeColor,
     rowCount (k15Template t) u q =
       if k16Template t ⟨u.val,by omega⟩ 15=q then 4 else 5 := by
   decide +kernel
#print axioms k16_rows
#print axioms k15_rows
end PricingABD.NativeTemplateDegreeProfiles
