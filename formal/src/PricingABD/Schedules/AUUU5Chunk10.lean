import PricingABD.Schedules.AUUU5
namespace PricingABD.Schedules.AUUU5Chunk10
open PricingABD.Schedules.AUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨320+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 32,InputOK program ⟨320+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 32,actualStart ⟨320+i.val+1,by omega⟩=actualStart ⟨320+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨320+i.val,by omega⟩) (inputs ⟨320+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.AUUU5Chunk10
