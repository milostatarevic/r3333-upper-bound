import UniformK61.CEntranceSelected
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices
open CompletionC.NativeRoleGeometry
open CompletionC.NativeWholeReindex
attribute [local irreducible] PricingC.NativePairActions.leftOrders PricingC.NativePairActions.rightOrders
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeActionFactors.leftIdsAt PricingC.NativeActionFactors.rightIdsAt

theorem left_auto_vertex {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hp:retained p=sourceRecord b (pairTable p).shape) (i:Fin 600)
 (a:Fin (order (kind (leftRole p i)))) (v:Fin (16)) (hv:a.val=v.val):
 (leftMap b (pairTable p).shape p hp i).vertex (auto (kind (leftRole p i)) (autoIndex (leftRole p i)) a)=
 b.left.vertex (modelAuto true lt (autoIndex (leftRole p i)) v):=by
 let k:=modelKind true lt
 let w:Fin (order k):=⟨v.val,by rw[modelKind_order];exact v.isLt⟩
 apply leftMap_vertex b (pairTable p).shape p hp i
 exact (auto_cast_val (role_bindings b (pairTable p).shape p hp i).1 _ a w hv).trans
  (modelAuto_val _ _ _ w v rfl)

theorem right_auto_vertex {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hp:retained p=sourceRecord b (pairTable p).shape) (i:Fin 600)
 (a:Fin (order (kind (rightRole p i)))) (v:Fin (16)) (hv:a.val=v.val):
 (rightMap b (pairTable p).shape p hp i).vertex (auto (kind (rightRole p i)) (autoIndex (rightRole p i)) a)=
 b.right.vertex (modelAuto true rt (autoIndex (rightRole p i)) v):=by
 let k:=modelKind true rt
 let w:Fin (order k):=⟨v.val,by rw[modelKind_order];exact v.isLt⟩
 apply rightMap_vertex b (pairTable p).shape p hp i
 exact (auto_cast_val (role_bindings b (pairTable p).shape p hp i).2.1 _ a w hv).trans
  (modelAuto_val _ _ _ w v rfl)

theorem before_original {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hf:freeSize five=(pairTable p).shape.free)
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
     simpa only[hfs,CompletionC.NativeRoleGeometry.roleOrder,Function.Embedding.coeFn_mk,j] using hj
   · have h1':¬a.val<PricingC.NativeActionFactors.freeSize (selectedFactor p i)+size (leftRole p i):=by rw[hfs,hls];exact h1
     simp only[if_neg h1',dif_neg h1]
     let j:Fin (size (rightRole p i)):=⟨a.val-(pairTable p).shape.free-(pairTable p).shape.left,by
      rw[hrs];have h:=Shape.dimension_sum (pairTable p).shape;have ha:=a.isLt;omega⟩
     have hj:=role_right_vertex b (pairTable p).shape p hp i j
     simpa only[hfs,hls,CompletionC.NativeRoleGeometry.roleOrder,Function.Embedding.coeFn_mk,j] using hj
#print axioms before_original
#print axioms left_auto_vertex
end UniformK61.CEntrance
