import PricingABD.Schedules.BTUU4
namespace PricingABD.Schedules.BTUU4Chunk07
open PricingABD.Schedules.BTUU4 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨224+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 32,InputOK program ⟨224+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 32,actualStart ⟨224+i.val+1,by omega⟩=actualStart ⟨224+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨224+i.val,by omega⟩) (inputs ⟨224+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BTUU4Chunk07
