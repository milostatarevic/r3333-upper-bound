import CompletionC.NativeShapeCoordinates
set_option autoImplicit false
namespace CompletionC.NativeSupportIndex
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativePairCoordinates CompletionC.NativeShapeCoordinates

/-- Literal native matrix endpoint numbers, in the archived free/left/right
order. Bounds are obtained from the admitted physical pair rather than modulo. -/
def supportIndex {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (a:Fin s.dimension):Fin (vertexCount l):=
 if h0:a.val<s.free then ABLayout.free l ⟨a.val,by rw[hf];exact h0⟩
 else if h1:a.val<s.free+s.left then ABLayout.left l
  ⟨digit leftOrders[p.val]! (a.val-s.free),left_label_bound b s p hp _ (by omega)⟩
 else ABLayout.right l ⟨digit rightOrders[p.val]! (a.val-s.free-s.left),right_label_bound b s p hp _
  (by have h:=Shape.dimension_sum s;have ha:=a.isLt;omega)⟩

theorem supportIndex_physical {c d:Host} {l:Layout} {t u:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (z:Blocks d l u) (a:Fin s.dimension):
 (frame z).vertex (supportIndex b s hf p hp a)=
 if h0:a.val<s.free then z.free ⟨a.val,by rw[hf];exact h0⟩
 else if h1:a.val<s.free+s.left then z.left.vertex
  ⟨digit leftOrders[p.val]! (a.val-s.free),left_label_bound b s p hp _ (by omega)⟩
 else z.right.vertex ⟨digit rightOrders[p.val]! (a.val-s.free-s.left),right_label_bound b s p hp _
  (by have h:=Shape.dimension_sum s;have ha:=a.isLt;omega)⟩:=by
 change physical z (supportIndex b s hf p hp a)=_
 unfold supportIndex
 by_cases h0:a.val<s.free
 · simp only[dif_pos h0,physical_free]
 · simp only[dif_neg h0]
   by_cases h1:a.val<s.free+s.left
   · simp only[dif_pos h1,physical_left];rfl
   · simp only[dif_neg h1,physical_right];rfl

theorem supportIndex_original {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (a:Fin s.dimension):
 (frame b).vertex (supportIndex b s hf p hp a)=originalVertex b s hf p hp (Equiv.refl _) a:=by
 rw[supportIndex_physical]
 rfl

theorem supportIndex_injective {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s):
 Function.Injective (supportIndex b s hf p hp):=by
 intro a d h
 apply originalVertex_injective b s hf p hp (Equiv.refl _)
 exact (supportIndex_original b s hf p hp a).symm.trans
  ((congrArg (frame b).vertex h).trans (supportIndex_original b s hf p hp d))
#print axioms supportIndex_injective
end CompletionC.NativeSupportIndex
