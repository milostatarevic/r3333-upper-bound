import CompletionC.NativeSupportIndex
import PricingIntegration.NativePrimaryCore
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeSuffix
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices CompletionC.CommonBlocks CompletionC.CommonPairAdmission
open CompletionC.NativeSupportIndex

/-- Exact one-based native edge numbering, executable without a physical host. -/
def edgeNat (n u v:Nat) (q:Fin 4):Nat:=
 if u<v then 4*(PricingIntegration.NativePrimaryCore.rowStart n u+(v-u-1))+q.val+1
 else 4*(PricingIntegration.NativePrimaryCore.rowStart n v+(u-v-1))+q.val+1

theorem edgeNat_fin {n:Nat} (u v:Fin n) (q:Fin 4):
 edgeNat n u.val v.val q=PricingIntegration.NativePrimaryCore.edgeVar u v q:=rfl

/-- Original matrix coordinate to native block numbering. -/
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
def fullPairs (s:Shape):List (Fin s.dimension×Fin s.dimension):=
 (List.finRange s.dimension).flatMap fun a=>(List.finRange s.dimension).filterMap fun b=>
 if a<b then some (a,b) else none

def fullMatrix (l:Layout):Prop:=l.profile=.D ∧ l.five=false
instance (l:Layout):Decidable (fullMatrix l):=inferInstanceAs (Decidable (_∧_))
def pairs (l:Layout) (p:Fin 737):List (Fin (pairTable p).shape.dimension×Fin (pairTable p).shape.dimension):=
 if fullMatrix l then fullPairs (pairTable p).shape else crossPairs (pairTable p).shape

def signedUnits (l:Layout) (p:Fin 737):List Literal:=
 ((List.finRange (leftSize l)).map fun v=>(decide (v.val∈(retained p).left),
  edgeNat (vertexCount l) (mark l).val (left l v).val 3)) ++
 ((List.finRange (rightSize l)).map fun v=>(decide (v.val∈(retained p).right),
  edgeNat (vertexCount l) (mark l).val (right l v).val 3))
def matrixUnits (l:Layout) (p:Fin 737) (j:Fin (pairTable p).count):List Literal:=
 (pairs l p).map fun ab=>(true,edgeNat (vertexCount l) (label l p ab.1.val) (label l p ab.2.val)
  (matrix (pairTable p).shape ((pairTable p).representative j) ab.1 ab.2))
def literals (l:Layout) (p:Fin 737) (j:Fin (pairTable p).count):List Literal:=
 (if fullMatrix l then [] else signedUnits l p) ++matrixUnits l p j
def formula (l:Layout) (p:Fin 737) (j:Fin (pairTable p).count):CNF:=
 (literals l p j).map (fun lit=>[lit])

theorem groupList_group (s:Shape) (q:Fin 3) (a:Fin s.dimension) (ha:a∈groupList s q):group s a=q:=by
 exact beq_iff_eq.mp (List.mem_filter.mp ha).2

theorem product_ne (s:Shape) (q r:Fin 3) (hqr:q≠r) (ab:Fin s.dimension×Fin s.dimension)
 (h:ab∈(groupList s q).product (groupList s r)):ab.1≠ab.2:=by
 obtain ⟨ha,hb⟩:=List.mem_product.mp h
 intro he
 exact hqr ((groupList_group s q ab.1 ha).symm.trans
  ((congrArg (group s) he).trans (groupList_group s r ab.2 hb)))

theorem pair_ne (l:Layout) (p:Fin 737) (ab:Fin (pairTable p).shape.dimension×Fin (pairTable p).shape.dimension)
 (h:ab∈pairs l p):ab.1≠ab.2:=by
 unfold pairs at h
 split_ifs at h
 · obtain ⟨a,_,hb⟩:=List.mem_flatMap.mp h
   obtain ⟨b,_,he⟩:=List.mem_filterMap.mp hb
   split_ifs at he with hab
   · cases Option.some.inj he
     exact ne_of_lt hab
 · rcases List.mem_append.mp h with h|h
   · rcases List.mem_append.mp h with h|h
     · exact product_ne _ 0 1 (by decide) ab h
     · exact product_ne _ 0 2 (by decide) ab h
   · exact product_ne _ 1 2 (by decide) ab h

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
#print axioms pair_ne
#print axioms label_supportIndex
end CompletionC.NativeSuffix
