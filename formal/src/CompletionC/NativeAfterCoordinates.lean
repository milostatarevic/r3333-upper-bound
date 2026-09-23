import CompletionC.NativeActionVertices
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeAfterCoordinates
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativeRoleGeometry CompletionC.NativePairRoleFrame CompletionC.NativePairCoordinates
open CompletionC.NativeWholeReindex CompletionC.NativeShapeCoordinates CompletionC.NativeSelectedBlocks
open CompletionC.NativeSupportIndex CompletionC.NativeActionVertices
attribute [local irreducible] PricingC.NativePairActions.leftOrders PricingC.NativePairActions.rightOrders
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeActionFactors.leftIdsAt PricingC.NativeActionFactors.rightIdsAt

theorem after_native {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600)
 (a:Fin (pairTable p).shape.dimension):
 (frame (selectedBlocks b p hf perm i)).vertex
  (supportIndex b (pairTable p).shape hf p hp a)=
 PricingC.NativeActionPhysical.after (selectedFactor p i) (freeFunction b p hf perm)
  (leftMap b (pairTable p).shape p hp i).vertex (rightMap b (pairTable p).shape p hp i).vertex a.val:=by
 have hfs:=(selected_factor_sizes p i).1
 have hls:=(selected_factor_sizes p i).2.1
 have hrs:=(selected_factor_sizes p i).2.2
 rw[supportIndex_physical]
 unfold PricingC.NativeActionPhysical.after
 by_cases h0:a.val<(pairTable p).shape.free
 · have h0':a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i):=by rw[hfs];exact h0
   simp only[if_pos h0',dif_pos h0]
   have hb:digit (PricingC.NativeActionFactors.freeCode (selectedFactor p i)) a.val<(pairTable p).shape.free:=by
    rw[←factorFree_val p i ⟨a.val,h0⟩]
    exact (factorFree p i ⟨a.val,h0⟩).isLt
   simp only[freeFunction,dif_pos hb]
   change b.free ((finCongr hf.symm) (perm (factorFree p i ⟨a.val,h0⟩)))=
    b.free ((finCongr hf.symm) (perm ⟨digit (PricingC.NativeActionFactors.freeCode (selectedFactor p i)) a.val,hb⟩))
   exact congrArg (fun v=>b.free ((finCongr hf.symm) (perm v))) (Fin.ext (factorFree_val p i ⟨a.val,h0⟩))
 · have h0':¬a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i):=by rw[hfs];exact h0
   simp only[if_neg h0',dif_neg h0]
   by_cases h1:a.val<(pairTable p).shape.free+(pairTable p).shape.left
   · have h1':a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i)+size (leftRole p i):=by rw[hfs,hls];exact h1
     simp only[if_pos h1',dif_pos h1]
     change b.left.vertex (modelAuto (leftLarge l) t.left (autoIndex (leftRole p i)) _) =
      (leftMap b (pairTable p).shape p hp i).vertex (auto (kind (leftRole p i)) (autoIndex (leftRole p i)) (orderVertex (leftRole p i) _))
     symm
     apply left_auto_vertex b p hp i
     let j:Fin (size (leftRole p i)):=⟨a.val-(pairTable p).shape.free,by rw[hls];omega⟩
     have he: (roleOrder (leftRole p i) j).val=digit leftOrders[p.val]! j.val:=
      (roleOrder_val _ j).trans (congrArg (fun code=>digit code j.val) (left_order_code p i))
     simpa only [roleOrder,Function.Embedding.coeFn_mk,j,hfs] using he
   · have h1':¬a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i)+size (leftRole p i):=by rw[hfs,hls];exact h1
     simp only[if_neg h1',dif_neg h1]
     change b.right.vertex (modelAuto (rightLarge l) t.right (autoIndex (rightRole p i)) _) =
      (rightMap b (pairTable p).shape p hp i).vertex (auto (kind (rightRole p i)) (autoIndex (rightRole p i)) (orderVertex (rightRole p i) _))
     symm
     apply right_auto_vertex b p hp i
     let j:Fin (size (rightRole p i)):=⟨a.val-(pairTable p).shape.free-(pairTable p).shape.left,by
      rw[hrs];have h:=Shape.dimension_sum (pairTable p).shape;have ha:=a.isLt;omega⟩
     have he: (roleOrder (rightRole p i) j).val=digit rightOrders[p.val]! j.val:=
      (roleOrder_val _ j).trans (congrArg (fun code=>digit code j.val) (right_order_code p i))
     simpa only [roleOrder,Function.Embedding.coeFn_mk,j,hfs,hls] using he
#print axioms after_native
end CompletionC.NativeAfterCoordinates
