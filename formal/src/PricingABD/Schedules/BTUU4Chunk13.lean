import PricingABD.Schedules.BTUU4
namespace PricingABD.Schedules.BTUU4Chunk13
open PricingABD.Schedules.BTUU4 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨416+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 17,InputOK program ⟨416+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 16,actualStart ⟨416+i.val+1,by omega⟩=actualStart ⟨416+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨416+i.val,by omega⟩) (inputs ⟨416+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.BTUU4Chunk13
