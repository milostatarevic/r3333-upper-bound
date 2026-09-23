import CompletionC.NativeSelectedBlocks
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeActionVertices
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativeRoleGeometry CompletionC.NativePairRoleFrame CompletionC.NativePairCoordinates
open CompletionC.NativeWholeReindex CompletionC.NativeShapeCoordinates CompletionC.NativeSelectedBlocks
attribute [local irreducible] PricingC.NativePairActions.leftOrders PricingC.NativePairActions.rightOrders
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeActionFactors.leftIdsAt PricingC.NativeActionFactors.rightIdsAt

theorem left_auto_vertex {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hp:retained p=sourceRecord b (pairTable p).shape) (i:Fin 600)
 (a:Fin (order (kind (leftRole p i)))) (v:Fin (leftSize l)) (hv:a.val=v.val):
 (leftMap b (pairTable p).shape p hp i).vertex (auto (kind (leftRole p i)) (autoIndex (leftRole p i)) a)=
 b.left.vertex (modelAuto (leftLarge l) t.left (autoIndex (leftRole p i)) v):=by
 let k:=modelKind (leftLarge l) t.left
 let w:Fin (order k):=⟨v.val,by rw[modelKind_order];exact v.isLt⟩
 apply leftMap_vertex b (pairTable p).shape p hp i
 exact (auto_cast_val (role_bindings b (pairTable p).shape p hp i).1 _ a w hv).trans
  (modelAuto_val _ _ _ w v rfl)

theorem right_auto_vertex {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hp:retained p=sourceRecord b (pairTable p).shape) (i:Fin 600)
 (a:Fin (order (kind (rightRole p i)))) (v:Fin (rightSize l)) (hv:a.val=v.val):
 (rightMap b (pairTable p).shape p hp i).vertex (auto (kind (rightRole p i)) (autoIndex (rightRole p i)) a)=
 b.right.vertex (modelAuto (rightLarge l) t.right (autoIndex (rightRole p i)) v):=by
 let k:=modelKind (rightLarge l) t.right
 let w:Fin (order k):=⟨v.val,by rw[modelKind_order];exact v.isLt⟩
 apply rightMap_vertex b (pairTable p).shape p hp i
 exact (auto_cast_val (role_bindings b (pairTable p).shape p hp i).2.1 _ a w hv).trans
  (modelAuto_val _ _ _ w v rfl)

theorem before_original {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600)
 (a:Fin (pairTable p).shape.dimension):
 PricingC.NativeActionPhysical.before (selectedFactor p i) (freeFunction b p hf perm)
  (leftMap b (pairTable p).shape p hp i).vertex (rightMap b (pairTable p).shape p hp i).vertex a.val=
 originalVertex b (pairTable p).shape hf p hp perm a:=by
 have hfs:=(selected_factor_sizes p i).1
 have hls:=(selected_factor_sizes p i).2.1
 have hrs:=(selected_factor_sizes p i).2.2
 unfold PricingC.NativeActionPhysical.before originalVertex
 by_cases h0:a.val<(pairTable p).shape.free
 · have h0':a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i):=by rw[hfs];exact h0
   simp only[if_pos h0',dif_pos h0,freeFunction]
   rfl
 · have h0':¬a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i):=by rw[hfs];exact h0
   simp only[if_neg h0',dif_neg h0]
   by_cases h1:a.val<(pairTable p).shape.free+(pairTable p).shape.left
   · have h1':a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i)+size (leftRole p i):=by rw[hfs,hls];exact h1
     simp only[if_pos h1',dif_pos h1]
     let j:Fin (size (leftRole p i)):=⟨a.val-(pairTable p).shape.free,by rw[hls];omega⟩
     have hj:=role_left_vertex b (pairTable p).shape p hp i j
     simpa only[hfs,NativeRoleGeometry.roleOrder,Function.Embedding.coeFn_mk,j] using hj
   · have h1':¬a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i)+size (leftRole p i):=by rw[hfs,hls];exact h1
     simp only[if_neg h1',dif_neg h1]
     let j:Fin (size (rightRole p i)):=⟨a.val-(pairTable p).shape.free-(pairTable p).shape.left,by
      rw[hrs];have h:=Shape.dimension_sum (pairTable p).shape;have ha:=a.isLt;omega⟩
     have hj:=role_right_vertex b (pairTable p).shape p hp i j
     simpa only[hfs,hls,NativeRoleGeometry.roleOrder,Function.Embedding.coeFn_mk,j] using hj
#print axioms before_original
#print axioms left_auto_vertex
end CompletionC.NativeActionVertices
