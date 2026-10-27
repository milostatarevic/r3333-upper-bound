import CompletionC.NativeSupportIndex

set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.SupportEdges
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices CompletionC.CommonBlocks CompletionC.CommonPairAdmission
open CompletionC.NativeSupportIndex

/-- Support-matrix coordinates in the retained block indexing. -/
def label (l:Layout) (p:Fin 737) (a:Nat):Nat:=
 if a<(pairTable p).shape.free then a
 else if a<(pairTable p).shape.free+(pairTable p).shape.left then
  freeSize l+digit leftOrders[p.val]! (a-(pairTable p).shape.free)
 else freeSize l+leftSize l+digit rightOrders[p.val]! (a-(pairTable p).shape.free-(pairTable p).shape.left)

def group (s:Shape) (a:Fin s.dimension):Fin 3:=
 if a.val<s.free then 0 else if a.val<s.free+s.left then 1 else 2

def groupList (s:Shape) (q:Fin 3):List (Fin s.dimension):=(List.finRange s.dimension).filter (fun a=>group s a==q)
def crossPairs (s:Shape):List (Fin s.dimension×Fin s.dimension):=
 (groupList s 0).product (groupList s 1) ++
 (groupList s 0).product (groupList s 2) ++
 (groupList s 1).product (groupList s 2)

theorem groupList_group (s:Shape) (q:Fin 3) (a:Fin s.dimension) (ha:a∈groupList s q):group s a=q:=by
 exact beq_iff_eq.mp (List.mem_filter.mp ha).2

theorem product_ne (s:Shape) (q r:Fin 3) (hqr:q≠r) (ab:Fin s.dimension×Fin s.dimension)
 (h:ab∈(groupList s q).product (groupList s r)):ab.1≠ab.2:=by
 obtain ⟨ha,hb⟩:=List.mem_product.mp h
 intro he
 exact hqr ((groupList_group s q ab.1 ha).symm.trans
  ((congrArg (group s) he).trans (groupList_group s r ab.2 hb)))


theorem label_supportIndex {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (hp:retained p=sourceRecord b (pairTable p).shape) (a:Fin (pairTable p).shape.dimension):
 label l p a.val=(supportIndex b (pairTable p).shape hf p hp a).val:=by
 unfold label supportIndex
 by_cases h0:a.val<(pairTable p).shape.free
 · simp only[if_pos h0,dif_pos h0];rfl
 · simp only[if_neg h0,dif_neg h0]
   by_cases h1:a.val<(pairTable p).shape.free+(pairTable p).shape.left
   · simp only[if_pos h1,dif_pos h1];rfl
   · simp only[if_neg h1,dif_neg h1];rfl

#print axioms label_supportIndex
end CompletionC.SupportEdges
