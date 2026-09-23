import PricingABD.Schedules.BTUU4
namespace PricingABD.Schedules.BTUU4Chunk15
open PricingABD.Schedules.BTUU4 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 8,FoldOK program types ⟨480+i.val,by omega⟩ := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BTUU4Chunk15
