import CompletionC.NativeMatrices
import PricingC.ThreeSupportUnbalanced
set_option autoImplicit false
namespace CompletionC.NativeCatalogue
open Ramsey61 Ramsey61.CEncodingCore
open CompletionC.NativeMatrices
open PricingC.ThreeSupportFrame

def liftedFree (s:Shape) (p:Equiv.Perm (Fin s.free)):
 Equiv.Perm (Fin (order s.free s.left s.right)):=by
 cases s
 · exact PricingABD.Rooted455Free.freeLift p
 · exact PricingC.OwnFive15.freeLift p
 · exact PricingC.OwnFive15.freeLift p
 · exact PricingC.Rooted555.freeLift p

def includeSupport (s:Shape) (a:Fin s.dimension):Fin (order s.free s.left s.right):=
 ⟨a.val,by have h:=Shape.dimension_sum s;have ha:=a.isLt;unfold order;omega⟩

noncomputable def reorderedVertex {c:Host} (s:Shape) (f:Frame c s.free s.left s.right)
 (p:Equiv.Perm (Fin s.free)):Fin s.dimension↪Vertex:=
 ⟨fun a=>physical f (liftedFree s p (includeSupport s a)),by
  intro a b he
  exact Fin.ext (congrArg (fun x:Fin (order s.free s.left s.right)=>x.val) ((liftedFree s p).injective ((physical f).injective he)))⟩

/-- The complete four-shape native catalogue follows from one actual host.
The only variable change is a permutation of its entire free support. -/
theorem actual_catalogue {c:Host} (s:Shape) (f:Frame c s.free s.left s.right)
 (hc:NoMonochromaticTriangle c):
 ∃p:Equiv.Perm (Fin s.free),∃i:Fin 600,∀a b:Fin s.dimension,a≠b→
 c (reorderedVertex s f p a) (reorderedVertex s f p b)=palette (matrix s (candidate s i) a b):=by
 cases s
 · exact actual_455_to_catalogue f hc
 · exact actual_545_to_catalogue f hc
 · exact actual_554_to_catalogue f hc
 · exact actual_555_to_catalogue f hc

theorem liftedFree_free (s:Shape) (p:Equiv.Perm (Fin s.free)) (i:Fin s.free):
 liftedFree s p (label0 (nl:=s.left) (nr:=s.right) i)=label0 (p i):=by
 cases s
 · exact PricingABD.Rooted455Free.freeLift_label0 p i
 · exact PricingC.OwnFive15.freeLift_label p i
 · exact PricingC.OwnFive15.freeLift_label p i
 · exact PricingC.Rooted555.freeLift_label0 p i

theorem liftedFree_after (s:Shape) (p:Equiv.Perm (Fin s.free))
 (a:Fin (order s.free s.left s.right)) (ha:s.free≤a.val):liftedFree s p a=a:=by
 cases s
 · exact PricingABD.Rooted455Free.freeLift_ge4 p a ha
 · exact PricingC.OwnFive15.freeLift_ge5 p a ha
 · exact PricingC.OwnFive15.freeLift_ge5 p a ha
 · exact PricingC.Rooted555.freeLift_ge5 p a ha

/-- Pointwise physical coordinates of the catalogue normalization. -/
theorem reorderedVertex_formula {c:Host} (s:Shape) (f:Frame c s.free s.left s.right)
 (p:Equiv.Perm (Fin s.free)) (a:Fin s.dimension):
 reorderedVertex s f p a=
 if h0:a.val<s.free then f.free (p ⟨a.val,h0⟩)
 else if h1:a.val<s.free+s.left then f.left ⟨a.val-s.free,by omega⟩
 else f.right ⟨a.val-s.free-s.left,by have hh:=Shape.dimension_sum s;have ha:=a.isLt;omega⟩:=by
 change physical f (liftedFree s p (includeSupport s a))=_
 split_ifs with h0 h1
 · have he:includeSupport s a=label0 (nl:=s.left) (nr:=s.right) ⟨a.val,h0⟩:=rfl
   rw[he,liftedFree_free,physical_free]
 · rw[liftedFree_after s p _ (by exact Nat.le_of_not_gt h0)]
   have he:includeSupport s a=label1 (nf:=s.free) (nr:=s.right) ⟨a.val-s.free,by omega⟩:=by
    apply Fin.ext;dsimp[includeSupport,label1];omega
   rw[he,physical_left]
 · rw[liftedFree_after s p _ (by exact Nat.le_of_not_gt h0)]
   have he:includeSupport s a=label2 (nf:=s.free) (nl:=s.left) ⟨a.val-s.free-s.left,by have hh:=Shape.dimension_sum s;have ha:=a.isLt;omega⟩:=by
    apply Fin.ext;dsimp[includeSupport,label2];omega
   rw[he,physical_right]
#print axioms actual_catalogue
#print axioms reorderedVertex_formula
end CompletionC.NativeCatalogue
