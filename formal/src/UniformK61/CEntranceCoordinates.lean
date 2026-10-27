import UniformK61.CEntranceRoleFrame
import CompletionC.NativeCatalogue
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open PricingABD.ABLayout
open PricingIntegration.PairAdmission
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices
open CompletionC.NativeRoleGeometry
attribute [local irreducible] PricingC.NativePairActions.leftOrders PricingC.NativePairActions.rightOrders
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeActionFactors.leftIdsAt PricingC.NativeActionFactors.rightIdsAt

theorem leftMap_vertex {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600)
 (a:Fin (order (kind (leftRole p i)))) (v:Fin (16)) (hv:a.val=v.val):
 (leftMap b s p hp i).vertex a=b.left.vertex v:=by
 have hn:order (modelKind true lt)=16:=modelKind_order _ _
 let w:Fin (order (modelKind true lt)):=⟨v.val,by rw[hn];exact v.isLt⟩
 exact (castKind_vertex _ _ a w hv).trans (ofModel_vertex _ _ _ w v rfl)

theorem rightMap_vertex {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600)
 (a:Fin (order (kind (rightRole p i)))) (v:Fin (16)) (hv:a.val=v.val):
 (rightMap b s p hp i).vertex a=b.right.vertex v:=by
 have hn:order (modelKind true rt)=16:=modelKind_order _ _
 let w:Fin (order (modelKind true rt)):=⟨v.val,by rw[hn];exact v.isLt⟩
 exact (castKind_vertex _ _ a w hv).trans (ofModel_vertex _ _ _ w v rfl)

theorem left_order_code (p:Fin 737) (i:Fin 600):orderCodes[(leftRole p i).val]! = leftOrders[p.val]!:=
 (selected_factor_witness p i).2.2.2.2.2.1
theorem right_order_code (p:Fin 737) (i:Fin 600):orderCodes[(rightRole p i).val]! = rightOrders[p.val]!:=
 (selected_factor_witness p i).2.2.2.2.2.2.1

theorem left_label_bound {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (j:Nat) (hj:j<s.left):
 digit leftOrders[p.val]! j<16:=by
 have hs:=(role_bindings b s p hp 0).2.2.1
 have h5:s.left≤5:=by cases s <;> decide
 have hh:=(all_role_bounds (leftRole p 0) ⟨j,by omega⟩ (by rw[hs];exact hj)).1
 change digit orderCodes[(leftRole p 0).val]! j<_ at hh
 rw[left_order_code,(role_bindings b s p hp 0).1,modelKind_order] at hh
 exact hh

theorem right_label_bound {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (j:Nat) (hj:j<s.right):
 digit rightOrders[p.val]! j<16:=by
 have hs:=(role_bindings b s p hp 0).2.2.2.1
 have h5:s.right≤5:=by cases s <;> decide
 have hh:=(all_role_bounds (rightRole p 0) ⟨j,by omega⟩ (by rw[hs];exact hj)).1
 change digit orderCodes[(rightRole p 0).val]! j<_ at hh
 rw[right_order_code,(role_bindings b s p hp 0).2.1,modelKind_order] at hh
 exact hh

theorem role_left_vertex {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600)
 (j:Fin (size (leftRole p i))):
 (leftMap b s p hp i).vertex (roleOrder (leftRole p i) j)=
 b.left.vertex ⟨digit leftOrders[p.val]! j.val,left_label_bound b s p hp _ (by rw[←(role_bindings b s p hp i).2.2.1];exact j.isLt)⟩:=by
 apply leftMap_vertex b s p hp i
 exact (roleOrder_val (leftRole p i) j).trans (congrArg (fun code=>digit code j.val) (left_order_code p i))

theorem role_right_vertex {c:Host} {five lt rt:Bool} (b:Blocks c five lt rt)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600)
 (j:Fin (size (rightRole p i))):
 (rightMap b s p hp i).vertex (roleOrder (rightRole p i) j)=
 b.right.vertex ⟨digit rightOrders[p.val]! j.val,right_label_bound b s p hp _ (by rw[←(role_bindings b s p hp i).2.2.2.1];exact j.isLt)⟩:=by
 apply rightMap_vertex b s p hp i
 exact (roleOrder_val (rightRole p i) j).trans (congrArg (fun code=>digit code j.val) (right_order_code p i))
#print axioms role_left_vertex
#print axioms role_right_vertex
end UniformK61.CEntrance
