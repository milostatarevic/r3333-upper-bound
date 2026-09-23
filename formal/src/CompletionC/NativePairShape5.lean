import CompletionC.NativePairShapeDefs
namespace CompletionC.NativeMatrices
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem pair_shape_5 : ∀j:Fin 100,PairShape ⟨500+j.val,by omega⟩:=by decide +kernel
end CompletionC.NativeMatrices
