import UniformK61.CEntranceAction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission PricingIntegration.PhysicalForeignSupport
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions PricingC.NativePairActions
open PricingG.NativeNegativeSupportTransport
open CompletionC.NativeMatrices
open CompletionC.NativeRoleGeometry
open CompletionC.NativeWholeReindex
attribute [local irreducible] PricingC.NativePairActions.leftOrders PricingC.NativePairActions.rightOrders
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeActionFactors.leftIdsAt PricingC.NativeActionFactors.rightIdsAt

private theorem role_membership {c:Host} {r mark:Vertex} {side:Bool} (role:Fin 98)
 (m:Ramsey61.ClassificationAdapter.PhysicalNeighborhoodMap c r (palette (owner side)) (template (kind role)))
 (hs:support m mark=canonicalSupport role):
 ∀v,c mark (m.vertex v)=palette 3 ↔v∈canonicalSupport role:=by
 intro v
 have he:v∈support m mark↔v∈canonicalSupport role:=by rw[hs]
 simpa only[support,Finset.mem_filter,Finset.mem_univ,true_and] using he

theorem left_preserves_support {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hf:freeSize five=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600) (v:Fin (16)):
 c ((selectedBlocks b p hf perm i).entrance.mark) ((selectedBlocks b p hf perm i).left.vertex v)=palette 3 ↔
 c (b.entrance.mark) (b.left.vertex v)=palette 3:=by
 let role:=leftRole p i
 let m:=leftMap b (pairTable p).shape p hp i
 have hk:= (role_bindings b (pairTable p).shape p hp i).1
 let a:Fin (order (kind role)):=⟨v.val,by rw[hk,modelKind_order];exact v.isLt⟩
 have hs:=role_support_exact (side:=false) role m (leftMap_support b (pairTable p).shape p hp i)
 have h:=(physical_marked_polarities role m.vertex (fun x y=>c x y) (b.entrance.mark) (palette 3)
  (role_membership (side:=false) (c:=c) (mark:=b.entrance.mark) role m hs) a).1
 change c (b.entrance.mark) (m.vertex (auto (kind role) (autoIndex role) a))=palette 3 ↔
  c (b.entrance.mark) (m.vertex a)=palette 3 at h
 rw[left_auto_vertex b p hp i a v rfl,leftMap_vertex b (pairTable p).shape p hp i a v rfl] at h
 exact h

theorem right_preserves_support {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hf:freeSize five=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600) (v:Fin (16)):
 c ((selectedBlocks b p hf perm i).entrance.mark) ((selectedBlocks b p hf perm i).right.vertex v)=palette 3 ↔
 c (b.entrance.mark) (b.right.vertex v)=palette 3:=by
 let role:=rightRole p i
 let m:=rightMap b (pairTable p).shape p hp i
 have hk:= (role_bindings b (pairTable p).shape p hp i).2.1
 let a:Fin (order (kind role)):=⟨v.val,by rw[hk,modelKind_order];exact v.isLt⟩
 have hs:=role_support_exact (side:=true) role m (rightMap_support b (pairTable p).shape p hp i)
 have h:=(physical_marked_polarities role m.vertex (fun x y=>c x y) (b.entrance.mark) (palette 3)
  (role_membership (side:=true) (c:=c) (mark:=b.entrance.mark) role m hs) a).1
 change c (b.entrance.mark) (m.vertex (auto (kind role) (autoIndex role) a))=palette 3 ↔
  c (b.entrance.mark) (m.vertex a)=palette 3 at h
 rw[right_auto_vertex b p hp i a v rfl,rightMap_vertex b (pairTable p).shape p hp i a v rfl] at h
 exact h

theorem naturalSet_mem {n:Nat} (S:Finset (Fin n)) (v:Fin n):v.val∈naturalSet S↔v∈S:=by
 simp only[naturalSet,Finset.mem_image,Fin.val_inj]
 simp

theorem left_native_membership {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hf:freeSize five=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600) (v:Fin (16)):
 c ((selectedBlocks b p hf perm i).entrance.mark) ((selectedBlocks b p hf perm i).left.vertex v)=palette 3 ↔
 v.val∈(retained p).left:=by
 have he:=congrArg Record.left hp
 change (retained p).left=naturalSet (support (side:=false) b.left (b.entrance.mark)) at he
 exact (left_preserves_support b p hf hp perm i v).trans (by
  rw[he,naturalSet_mem]
  simp only[support,Finset.mem_filter,Finset.mem_univ,true_and])

theorem right_native_membership {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (p:Fin 737) (hf:freeSize five=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600) (v:Fin (16)):
 c ((selectedBlocks b p hf perm i).entrance.mark) ((selectedBlocks b p hf perm i).right.vertex v)=palette 3 ↔
 v.val∈(retained p).right:=by
 have he:=congrArg Record.right hp
 change (retained p).right=naturalSet (support (side:=true) b.right (b.entrance.mark)) at he
 exact (right_preserves_support b p hf hp perm i v).trans (by
  rw[he,naturalSet_mem]
  simp only[support,Finset.mem_filter,Finset.mem_univ,true_and])
#print axioms left_native_membership
#print axioms right_native_membership
end UniformK61.CEntrance
