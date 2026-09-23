import PricingABD.Schedules.BUUU5
namespace PricingABD.Schedules.BUUU5Chunk15
open PricingABD.Schedules.BUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 24,FoldOK program types ⟨480+i.val,by omega⟩ := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BUUU5Chunk15
