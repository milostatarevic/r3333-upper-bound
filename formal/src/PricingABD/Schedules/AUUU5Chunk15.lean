import PricingABD.Schedules.AUUU5
namespace PricingABD.Schedules.AUUU5Chunk15
open PricingABD.Schedules.AUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨480+i.val,by omega⟩ := by decide +kernel
#print axioms fold
end PricingABD.Schedules.AUUU5Chunk15
