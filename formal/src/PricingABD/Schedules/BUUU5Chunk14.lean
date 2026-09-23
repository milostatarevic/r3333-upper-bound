import PricingABD.Schedules.BUUU5
namespace PricingABD.Schedules.BUUU5Chunk14
open PricingABD.Schedules.BUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨448+i.val,by omega⟩ := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BUUU5Chunk14
