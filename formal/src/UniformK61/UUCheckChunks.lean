import UniformK61.UUBridgeData
set_option autoImplicit false
namespace UniformK61.UUCheckChunks
open UniformK61.UUBridgeData UniformK61.UUSupportData

def word (j : Fin 12) (k : Fin 50) : Fin 600 := ⟨50*j.val+k.val,by omega⟩

theorem row_of_chunks (p : Pair)
 (h : ∀j : Fin 12,∀k : Fin 50,checkResidual false p (word j k)=true)
 (i : Fin 600) : checkResidual false p i=true := by
 let j : Fin 12:=⟨i.val/50,by omega⟩
 let k : Fin 50:=⟨i.val%50,Nat.mod_lt _ (by decide)⟩
 have he : word j k=i := by apply Fin.ext;dsimp[word,j,k];omega
 simpa only[he] using h j k
end UniformK61.UUCheckChunks
