import UniformK61.UUCheckChunks
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace UniformK61.UUCheckRow38
open UniformK61.UUBridgeData UniformK61.UUCheckChunks
theorem chunk00 : ∀k : Fin 50,checkResidual false 38 (word 0 k)=true := by decide +kernel
theorem chunk01 : ∀k : Fin 50,checkResidual false 38 (word 1 k)=true := by decide +kernel
theorem chunk02 : ∀k : Fin 50,checkResidual false 38 (word 2 k)=true := by decide +kernel
theorem chunk03 : ∀k : Fin 50,checkResidual false 38 (word 3 k)=true := by decide +kernel
theorem chunk04 : ∀k : Fin 50,checkResidual false 38 (word 4 k)=true := by decide +kernel
theorem chunk05 : ∀k : Fin 50,checkResidual false 38 (word 5 k)=true := by decide +kernel
theorem chunk06 : ∀k : Fin 50,checkResidual false 38 (word 6 k)=true := by decide +kernel
theorem chunk07 : ∀k : Fin 50,checkResidual false 38 (word 7 k)=true := by decide +kernel
theorem chunk08 : ∀k : Fin 50,checkResidual false 38 (word 8 k)=true := by decide +kernel
theorem chunk09 : ∀k : Fin 50,checkResidual false 38 (word 9 k)=true := by decide +kernel
theorem chunk10 : ∀k : Fin 50,checkResidual false 38 (word 10 k)=true := by decide +kernel
theorem chunk11 : ∀k : Fin 50,checkResidual false 38 (word 11 k)=true := by decide +kernel
theorem checked (i : Fin 600) : checkResidual false 38 i=true := by
 apply row_of_chunks 38 ?_ i
 intro j k
 fin_cases j
 · exact chunk00 k
 · exact chunk01 k
 · exact chunk02 k
 · exact chunk03 k
 · exact chunk04 k
 · exact chunk05 k
 · exact chunk06 k
 · exact chunk07 k
 · exact chunk08 k
 · exact chunk09 k
 · exact chunk10 k
 · exact chunk11 k
end UniformK61.UUCheckRow38
