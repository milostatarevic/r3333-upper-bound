import PricingABD.Schedules.BUUU4
namespace PricingABD.Schedules.BUUU4Chunk05
open PricingABD.Schedules.BUUU4 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨160+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 32,InputOK program ⟨160+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 32,actualStart ⟨160+i.val+1,by omega⟩=actualStart ⟨160+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨160+i.val,by omega⟩) (inputs ⟨160+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BUUU4Chunk05
