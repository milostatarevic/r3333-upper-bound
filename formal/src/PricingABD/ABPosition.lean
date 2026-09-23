import PricingABD.ABLayout

set_option autoImplicit false
namespace PricingABD.ABPosition
open PricingABD.ABLayout

inductive Position (l : Layout) where
  | free : Fin (freeSize l) → Position l
  | left : Fin (leftSize l) → Position l
  | right : Fin (rightSize l) → Position l
  | marked : Fin 16 → Position l
  deriving DecidableEq

def encode {l : Layout} : Position l → Fin (vertexCount l)
  | .free i => ABLayout.free l i
  | .left i => ABLayout.left l i
  | .right i => ABLayout.right l i
  | .marked i => ABLayout.marked l i

def decode (l : Layout) (i : Fin (vertexCount l)) : Position l :=
  if hf : i.val < freeSize l then .free ⟨i.val,hf⟩ else
  if hl : i.val < rightStart l then .left ⟨i.val-freeSize l,by unfold rightStart at hl;omega⟩ else
  if hr : i.val < markedStart l then .right ⟨i.val-rightStart l,by unfold rightStart markedStart at *;omega⟩ else
  .marked ⟨i.val-markedStart l,by have hi:=i.isLt;unfold vertexCount tailSize markedStart rightStart at *;omega⟩

@[simp] theorem encode_decode (l : Layout) (i : Fin (vertexCount l)) : encode (decode l i)=i := by
  unfold decode
  split_ifs <;> apply Fin.ext <;> dsimp [encode,ABLayout.free,ABLayout.left,ABLayout.right,ABLayout.marked,leftStart] <;> omega

@[simp] theorem decode_encode {l : Layout} (p : Position l) : decode l (encode p)=p := by
  have hs:=sizes l
  cases p with
  | free i => simp [encode,decode,ABLayout.free,i.isLt]
  | left i =>
    simp only [encode,ABLayout.left,decode,leftStart,rightStart,markedStart]
    split_ifs <;> try omega
    congr 1
    apply Fin.ext
    simp
  | right i =>
    simp only [encode,ABLayout.right,decode,rightStart,markedStart]
    split_ifs <;> try omega
    congr 1
    apply Fin.ext
    simp
  | marked i =>
    simp only [encode,ABLayout.marked,decode,rightStart,markedStart]
    split_ifs <;> try omega
    congr 1
    apply Fin.ext
    simp

theorem encode_injective {l : Layout} : Function.Injective (@encode l) := by
  intro p q h
  have := congrArg (decode l) h
  simpa using this

def equivalence (l : Layout) : Position l ≃ Fin (vertexCount l) where
  toFun:=encode
  invFun:=decode l
  left_inv:=decode_encode
  right_inv:=encode_decode l

end PricingABD.ABPosition
