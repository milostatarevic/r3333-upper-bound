import UniformK61.CEntranceFormula
set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices

def supportIndex {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (s : Shape) (hf : freeSize five=s.free) (p : Fin 737) (hp : retained p=sourceRecord b s)
    (a : Fin s.dimension) : Vertex :=
  if h0 : a.val<s.free then lowVertex ⟨a.val,by have := freeSize_le_five five;omega⟩
  else if h1 : a.val<s.free+s.left then leftVertex
    ⟨digit leftOrders[p.val]! (a.val-s.free),left_label_bound b s p hp _ (by omega)⟩
  else rightVertex ⟨digit rightOrders[p.val]! (a.val-s.free-s.left),right_label_bound b s p hp _
    (by have h := Shape.dimension_sum s;have ha := a.isLt;omega)⟩

theorem supportIndex_physical {c d : Host} {five lt rt lt' rt' : Bool}
    (b : Blocks c five lt rt) (s : Shape) (hf : freeSize five=s.free)
    (p : Fin 737) (hp : retained p=sourceRecord b s) (z : Blocks d five lt' rt')
    (a : Fin s.dimension) :
    fullMap z (supportIndex b s hf p hp a)=supportVertex b s hf p hp z a := by
  unfold supportIndex supportVertex
  by_cases h0 : a.val<s.free
  · simp only [dif_pos h0,fullMap_low]
    exact low_initial z ⟨a.val,by rw [hf];exact h0⟩
  · simp only [dif_neg h0]
    by_cases h1 : a.val<s.free+s.left
    · simp only [dif_pos h1,fullMap_left]
    · simp only [dif_neg h1,fullMap_right]

theorem supportVertex_original {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (s : Shape) (hf : freeSize five=s.free) (p : Fin 737) (hp : retained p=sourceRecord b s)
    (a : Fin s.dimension) :
    supportVertex b s hf p hp b a=originalVertex b s hf p hp (Equiv.refl _) a := rfl

theorem supportIndex_injective {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (s : Shape) (hf : freeSize five=s.free) (p : Fin 737) (hp : retained p=sourceRecord b s) :
    Function.Injective (supportIndex b s hf p hp) := by
  intro a d h
  apply originalVertex_injective b s hf p hp (Equiv.refl _)
  rw [←supportVertex_original,←supportVertex_original,←supportIndex_physical,←supportIndex_physical,h]

theorem label61_eq {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (p : Fin 737) (hf : freeSize five=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape)
    (a : Fin (pairTable p).shape.dimension) :
    Formula.label61 p a.val=supportIndex b (pairTable p).shape hf p hp a := by
  have he : Formula.label p a.val=(supportIndex b (pairTable p).shape hf p hp a).val := by
    unfold Formula.label supportIndex
    by_cases h0 : a.val<(pairTable p).shape.free
    · simp only [if_pos h0,dif_pos h0];rfl
    · simp only [if_neg h0,dif_neg h0]
      by_cases h1 : a.val<(pairTable p).shape.free+(pairTable p).shape.left
      · simp only [if_pos h1,dif_pos h1];rfl
      · simp only [if_neg h1,dif_neg h1];rfl
  apply Fin.ext
  dsimp [Formula.label61]
  rw [he]
  exact Nat.mod_eq_of_lt (supportIndex b (pairTable p).shape hf p hp a).isLt

#print axioms supportIndex_injective
end UniformK61.CEntrance
