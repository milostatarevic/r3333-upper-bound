import PricingABD.Schedules.AUUU5
namespace PricingABD.Schedules.AUUU5Chunk14
open PricingABD.Schedules.AUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨448+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 12,InputOK program ⟨448+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 11,actualStart ⟨448+i.val+1,by omega⟩=actualStart ⟨448+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨448+i.val,by omega⟩) (inputs ⟨448+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.AUUU5Chunk14
