import CompletionC.NativePairCoordinates
import CompletionC.NativeFrameCast
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeShapeCoordinates
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativePairRoleFrame CompletionC.NativePairCoordinates CompletionC.NativeCatalogue

noncomputable def nativeFrame {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s):
 PricingC.ThreeSupportFrame.Frame c s.free s.left s.right:=
 CompletionC.NativeFrameCast.castFrame (roleFrame b s p hp 0) hf
 (role_bindings b s p hp 0).2.2.1 (role_bindings b s p hp 0).2.2.2.1

theorem nativeFrame_free {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s) (a:Fin s.free):
 (nativeFrame b s hf p hp).free a=b.free ⟨a.val,by rw[hf];exact a.isLt⟩:=
 CompletionC.NativeFrameCast.free_value _ _ _ _ _ _ rfl

theorem nativeFrame_left {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s) (a:Fin s.left):
 (nativeFrame b s hf p hp).left a=b.left.vertex ⟨digit leftOrders[p.val]! a.val,left_label_bound b s p hp _ a.isLt⟩:=by
 let j:Fin (size (leftRole p 0)):=⟨a.val,by rw[(role_bindings b s p hp 0).2.2.1];exact a.isLt⟩
 have h:=CompletionC.NativeFrameCast.left_value (roleFrame b s p hp 0) hf
  (role_bindings b s p hp 0).2.2.1 (role_bindings b s p hp 0).2.2.2.1 a j rfl
 exact h.trans (role_left_vertex b s p hp 0 j)

theorem nativeFrame_right {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s) (a:Fin s.right):
 (nativeFrame b s hf p hp).right a=b.right.vertex ⟨digit rightOrders[p.val]! a.val,right_label_bound b s p hp _ a.isLt⟩:=by
 let j:Fin (size (rightRole p 0)):=⟨a.val,by rw[(role_bindings b s p hp 0).2.2.2.1];exact a.isLt⟩
 have h:=CompletionC.NativeFrameCast.right_value (roleFrame b s p hp 0) hf
  (role_bindings b s p hp 0).2.2.1 (role_bindings b s p hp 0).2.2.2.1 a j rfl
 exact h.trans (role_right_vertex b s p hp 0 j)

/-- Explicit native matrix-coordinate vertex: free block, followed by the
original retained physical_order of the two complete foreign cells. -/
noncomputable def originalVertex {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (perm:Equiv.Perm (Fin s.free)) (a:Fin s.dimension):Vertex:=
 if h0:a.val<s.free then b.free ⟨(perm ⟨a.val,h0⟩).val,by rw[hf];exact (perm ⟨a.val,h0⟩).isLt⟩
 else if h1:a.val<s.free+s.left then b.left.vertex
  ⟨digit leftOrders[p.val]! (a.val-s.free),left_label_bound b s p hp _ (by omega)⟩
 else b.right.vertex ⟨digit rightOrders[p.val]! (a.val-s.free-s.left),right_label_bound b s p hp _
  (by have h:=Shape.dimension_sum s;have ha:=a.isLt;omega)⟩

theorem originalVertex_eq {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (perm:Equiv.Perm (Fin s.free)) (a:Fin s.dimension):
 originalVertex b s hf p hp perm a=reorderedVertex s (nativeFrame b s hf p hp) perm a:=by
 rw[reorderedVertex_formula]
 unfold originalVertex
 by_cases h0:a.val<s.free
 · simp only [dif_pos h0]
   exact (nativeFrame_free b s hf p hp (perm ⟨a.val,h0⟩)).symm
 · simp only [dif_neg h0]
   by_cases h1:a.val<s.free+s.left
   · simp only [dif_pos h1]
     exact (nativeFrame_left b s hf p hp ⟨a.val-s.free,by omega⟩).symm
   · simp only [dif_neg h1]
     exact (nativeFrame_right b s hf p hp ⟨a.val-s.free-s.left,by have h:=Shape.dimension_sum s;have ha:=a.isLt;omega⟩).symm

theorem originalVertex_injective {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (perm:Equiv.Perm (Fin s.free)):
 Function.Injective (originalVertex b s hf p hp perm):=by
 intro a d h
 rw[originalVertex_eq,originalVertex_eq] at h
 exact (reorderedVertex s (nativeFrame b s hf p hp) perm).injective h

theorem actual_native_catalogue {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (hc:NoMonochromaticTriangle c) (s:Shape) (hf:freeSize l=s.free)
 (p:Fin 737) (hp:retained p=sourceRecord b s):
 ∃perm:Equiv.Perm (Fin s.free),∃i:Fin 600,∀a d:Fin s.dimension,a≠d→
 c (originalVertex b s hf p hp perm a) (originalVertex b s hf p hp perm d)=
 palette (matrix s (candidate s i) a d):=by
 obtain ⟨perm,i,hi⟩:=actual_catalogue s (nativeFrame b s hf p hp) hc
 refine ⟨perm,i,?_⟩
 intro a d had
 exact ((congrArg₂ (fun x y=>c x y) (originalVertex_eq b s hf p hp perm a)
  (originalVertex_eq b s hf p hp perm d))).trans (hi a d had)
#print axioms actual_native_catalogue
end CompletionC.NativeShapeCoordinates
