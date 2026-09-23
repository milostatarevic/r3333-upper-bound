import PricingABD.Schedules.AUUU5
namespace PricingABD.Schedules.AUUU5Chunk11
open PricingABD.Schedules.AUUU5 PricingABD.ABProgram
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem fold : ∀i:Fin 32,FoldOK program types ⟨352+i.val,by omega⟩ := by decide +kernel
theorem input : ∀i:Fin 32,InputOK program ⟨352+i.val,by omega⟩ := by decide +kernel
theorem adjacent : ∀i:Fin 32,actualStart ⟨352+i.val+1,by omega⟩=actualStart ⟨352+i.val,by omega⟩+PricingIntegration.SparseCounter.offset (height ⟨352+i.val,by omega⟩) (inputs ⟨352+i.val,by omega⟩).length := by decide +kernel
#print axioms fold
end PricingABD.Schedules.AUUU5Chunk11
