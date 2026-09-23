import CompletionC.NativePairShapeDefs
namespace CompletionC.NativeMatrices
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem pair_shape_1 : ∀j:Fin 100,PairShape ⟨100+j.val,by omega⟩:=by decide +kernel
end CompletionC.NativeMatrices
