import PricingABD.Schedules.BUUU5
namespace PricingABD.Schedules.BUUU5Chunk06
open PricingABD.Schedules.BUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨192+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 32,InputOK program ⟨192+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 32,actualStart ⟨192+i.val+1,by omega⟩=actualStart ⟨192+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨192+i.val,by omega⟩) (inputs ⟨192+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BUUU5Chunk06
