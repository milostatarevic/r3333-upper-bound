import CompletionC.NativePhysicalRepresentative
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace CompletionC.NativeFreeGeometry
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry PricingIntegration.PairAdmission
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativeSupportIndex

def freeIndex (s:Shape) (a:Fin s.free):Fin s.dimension:=
 ⟨a.val,by have h:=Shape.dimension_sum s;have ha:=a.isLt;omega⟩
def freePattern (s:Shape) (a b:Fin s.free):Fin 4:=
 if max a.val b.val=min a.val b.val+1 ∨
  (s.free=5 ∧ min a.val b.val=0 ∧ max a.val b.val=4) then 1 else 2

theorem matrix_free (s:Shape) (w:Nat) (a b:Fin s.free) (hab:a≠b):
 matrix s w (freeIndex s a) (freeIndex s b)=freePattern s a b:=by
 cases s <;> fin_cases a <;> fin_cases b <;>
 simp_all [matrix,freeIndex,freePattern,Shape.free,Shape.dimension,
  PricingABD.P15MatrixTransport.matrix,PricingABD.P15MatrixTransport.orderedMatrix,
  PricingC.Rooted45Orientation.matrix,PricingC.Rooted45Orientation.orderedMatrix,
  PricingC.Rooted45Orientation.Cycle,PricingC.Rooted555.matrix,PricingC.Rooted555.orderedMatrix]

theorem freePattern_native (l:Layout) (s:Shape) (hf:freeSize l=s.free)
 (a b:Fin (freeSize l)):
 freePattern s ((finCongr hf) a) ((finCongr hf) b)=freeColor l a b:=by
 have he:(s.free=5)↔l.five=true:=by
  rw[←hf]
  cases h:l.five <;> simp[freeSize,h]
 simp only[freePattern,freeColor,finCongr_apply_coe,he]

theorem supportIndex_free {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (a:Fin (freeSize l)):
 supportIndex b s hf p hp (freeIndex s ((finCongr hf) a))=ABLayout.free l a:=by
 have ha:a.val<s.free:=by rw[←hf];exact a.isLt
 simp only[supportIndex,freeIndex,finCongr_apply_coe,dif_pos ha]

/-- The representative's fixed internal free edges supply the prefix's exact
P4/C5 geometry. This is recovered from the full matrix, not assumed anew. -/
theorem geometry_of_matrix {c:Host} {l:Layout} {t:Types} (b z:Blocks c l t)
 (s:Shape) (hf:freeSize l=s.free) (p:Fin 737) (hp:retained p=sourceRecord b s)
 (w:Nat) (hmat:∀a d:Fin s.dimension,a≠d→
 c ((frame z).vertex (supportIndex b s hf p hp a)) ((frame z).vertex (supportIndex b s hf p hp d))=
 palette (matrix s w a d)):Geometry t (frame z):=by
 refine ⟨left_edges z,right_edges z,marked_edges z,?_,?_⟩
 · intro a d had
   have hindex:freeIndex s ((finCongr hf) a)≠freeIndex s ((finCongr hf) d):=by
    intro h;apply had;exact Fin.ext (congrArg (fun x:Fin s.dimension=>x.val) h)
   have he:=hmat _ _ hindex
   rw[supportIndex_free,supportIndex_free,matrix_free _ _ _ _ ((finCongr hf).injective.ne had),freePattern_native] at he
   exact he
 · intro a
   change c (physical z (ABLayout.marked l 15)) (physical z (ABLayout.free l a))=palette 3
   rw[physical_marked,physical_free]
   exact z.free_own a
#print axioms geometry_of_matrix
end CompletionC.NativeFreeGeometry
