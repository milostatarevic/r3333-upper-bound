import PricingABD.Schedules.AUUU4
namespace PricingABD.Schedules.AUUU4Chunk04
open PricingABD.Schedules.AUUU4 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨128+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 32,InputOK program ⟨128+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 32,actualStart ⟨128+i.val+1,by omega⟩=actualStart ⟨128+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨128+i.val,by omega⟩) (inputs ⟨128+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.AUUU4Chunk04
