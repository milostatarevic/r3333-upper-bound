import CompletionC.NativeRoleGeometry
import CompletionC.NativeSelectedCoordinates
import CompletionC.CommonPairAdmission
import PricingC.ThreeSupportUnbalanced
set_option autoImplicit false
namespace CompletionC.NativePairRoleFrame
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.BActualFrame PricingIntegration.PhysicalForeignSupport PricingIntegration.PairAdmission
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions PricingC.NativeActionFactors
open PricingC.NativePairActions
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.CommonSupportNormalization
open CompletionC.NativeMatrices CompletionC.NativeRoleGeometry
attribute [local irreducible] PricingC.NativePairActions.leftKinds PricingC.NativePairActions.rightKinds
 PricingC.NativePairActions.leftOrders PricingC.NativePairActions.rightOrders
 PricingC.NativePairActions.freeSizes PricingC.NativePairActions.leftSizes PricingC.NativePairActions.rightSizes
 PricingC.NativeBlockActions.orderCodes PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.kinds
 PricingC.NativeActionFactors.leftIdsAt PricingC.NativeActionFactors.rightIdsAt

abbrev leftRole (p:Fin 737) (i:Fin 600):Fin 98:=PricingC.NativeActionFactors.left (selectedFactor p i)
abbrev rightRole (p:Fin 737) (i:Fin 600):Fin 98:=PricingC.NativeActionFactors.right (selectedFactor p i)

theorem role_bindings {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 kind (leftRole p i)=modelKind (leftLarge l) t.left ∧
 kind (rightRole p i)=modelKind (rightLarge l) t.right ∧
 size (leftRole p i)=s.left ∧ size (rightRole p i)=s.right ∧
 naturalSet (support (side:=false) b.left (b.marked.vertex 15))=orderSet orderCodes[(leftRole p i).val]! (size (leftRole p i)) ∧
 naturalSet (support (side:=true) b.right (b.marked.vertex 15))=orderSet orderCodes[(rightRole p i).val]! (size (rightRole p i)):=by
 have hn:=all_native_bindings p
 unfold NativeBinding at hn
 rw[hp] at hn
 change leftKinds[p.val]! = kindCode (leftLarge l) t.left ∧
  rightKinds[p.val]! = kindCode (rightLarge l) t.right ∧
  PricingC.NativePairActions.freeSizes[p.val]! = (if s.code=0 then 4 else 5) ∧
  leftSizes[p.val]! = (if s.code=1 then 4 else 5) ∧
  rightSizes[p.val]! = (if s.code=2 then 4 else 5) ∧
  orderSet leftOrders[p.val]! leftSizes[p.val]! = naturalSet (support (side:=false) b.left (b.marked.vertex 15)) ∧
  orderSet rightOrders[p.val]! rightSizes[p.val]! = naturalSet (support (side:=true) b.right (b.marked.vertex 15)) at hn
 obtain ⟨hk1,hk2,_,hs1,hs2,ho1,ho2⟩:=hn
 have hw:=selected_factor_witness p i
 unfold PairWitness at hw
 obtain ⟨_,_,_,h1,h2,hord1,hord2,hsize1,hsize2⟩:=hw
 have hs1':(if s.code=1 then 4 else 5)=s.left:=by cases s <;> rfl
 have hs2':(if s.code=2 then 4 else 5)=s.right:=by cases s <;> rfl
 refine ⟨?_,?_,hsize1.trans (hs1.trans hs1'),hsize2.trans (hs2.trans hs2'),?_,?_⟩
 · exact h1.trans (congrArg PricingC.NativePairActions.decodeKind hk1)
 · exact h2.trans (congrArg PricingC.NativePairActions.decodeKind hk2)
 · exact ho1.symm.trans (congrArg₂ orderSet hord1.symm hsize1.symm)
 · exact ho2.symm.trans (congrArg₂ orderSet hord2.symm hsize2.symm)

noncomputable def leftMap {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 PhysicalNeighborhoodMap c b.root (palette 1) (template (kind (leftRole p i))):=
 castKind (role_bindings b s p hp i).1.symm (ofModel (leftLarge l) t.left b.left)
noncomputable def rightMap {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 PhysicalNeighborhoodMap c b.root (palette 2) (template (kind (rightRole p i))):=
 castKind (role_bindings b s p hp i).2.1.symm (ofModel (rightLarge l) t.right b.right)

theorem leftMap_palette {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 (leftMap b s p hp i).colors=foreignEquiv 1:=
 (castKind_palette _ _).trans ((ofModel_palette _ _ _).trans b.left_palette)
theorem rightMap_palette {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 (rightMap b s p hp i).colors=foreignEquiv 2:=
 (castKind_palette _ _).trans ((ofModel_palette _ _ _).trans b.right_palette)

theorem leftMap_support {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 naturalSet (support (side:=false) (leftMap b s p hp i) (b.marked.vertex 15))=
 orderSet orderCodes[(leftRole p i).val]! (size (leftRole p i)):=
 (castKind_naturalSupport _ _).trans ((ofModel_naturalSupport _ _ false _).trans (role_bindings b s p hp i).2.2.2.2.1)
theorem rightMap_support {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 naturalSet (support (side:=true) (rightMap b s p hp i) (b.marked.vertex 15))=
 orderSet orderCodes[(rightRole p i).val]! (size (rightRole p i)):=
 (castKind_naturalSupport _ _).trans ((ofModel_naturalSupport _ _ true _).trans (role_bindings b s p hp i).2.2.2.2.2)

/-- The exact retained physical orders produce the actual three-support
frame consumed by all four600-word classification theorems. -/
noncomputable def roleFrame {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (p:Fin 737) (hp:retained p=sourceRecord b s) (i:Fin 600):
 PricingC.ThreeSupportFrame.Frame c (freeSize l) (size (leftRole p i)) (size (rightRole p i)) where
 root:=b.root
 mark:=b.marked.vertex 15
 free:=b.free
 left:=(roleOrder (leftRole p i)).trans (leftMap b s p hp i).vertex
 right:=(roleOrder (rightRole p i)).trans (rightMap b s p hp i).vertex
 mark_mem:=b.marked.mem_neighborhood 15
 free_mem:=b.free_mem
 left_mem j:=(leftMap b s p hp i).mem_neighborhood _
 right_mem j:=(rightMap b s p hp i).mem_neighborhood _
 marked_free:=b.free_own
 marked_left:=role_support_edge (side:=false) _ _ (leftMap_support b s p hp i)
 marked_right:=role_support_edge (side:=true) _ _ (rightMap_support b s p hp i)
 left_edges:=role_pattern (side:=false) _ _ (leftMap_palette b s p hp i)
 right_edges:=role_pattern (side:=true) _ _ (rightMap_palette b s p hp i)

noncomputable def shapeFrame {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s):
 PricingC.ThreeSupportFrame.Frame c s.free s.left s.right:=by
 have hl:=(role_bindings b s p hp 0).2.2.1
 have hr:=(role_bindings b s p hp 0).2.2.2.1
 rw[←hf,←hl,←hr]
 exact roleFrame b s p hp 0
#print axioms role_bindings
#print axioms shapeFrame
end CompletionC.NativePairRoleFrame
