import UniformK61.CEntranceHost
import UniformK61.CEntranceSigned
import CompletionC.SupportEdges
import CompletionC.NativeFreeGeometry

set_option autoImplicit false
namespace UniformK61.CEntrance.Formula
open Ramsey61 Ramsey61.CEncodingCore
open PricingIntegration.BActualFrame PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices CompletionC.SupportEdges

def spokes : List Core.PhysicalUnit :=
  ((List.finRange 14).map fun i => ⟨true,0,lowVertex i,0⟩) ++
  ((List.finRange 16).map fun i => ⟨true,0,leftVertex i,1⟩) ++
  ((List.finRange 16).map fun i => ⟨true,0,rightVertex i,2⟩) ++
  ((List.finRange 14).map fun i => ⟨true,0,markedVertex i,3⟩)

def templates (lt rt : Bool) : List Core.PhysicalUnit :=
  ((PricingABD.ABGeometry.orderedPairs 16).map fun ab =>
    ⟨true,leftVertex ab.1,leftVertex ab.2,foreign 1 (R4333.k16Template lt ab.1 ab.2)⟩) ++
  ((PricingABD.ABGeometry.orderedPairs 16).map fun ab =>
    ⟨true,rightVertex ab.1,rightVertex ab.2,foreign 2 (R4333.k16Template rt ab.1 ab.2)⟩)

def freeColor (five : Bool) (a b : Fin (freeSize five)) : Color :=
  if max a.val b.val = min a.val b.val+1 ∨
    (five=true ∧ min a.val b.val=0 ∧ max a.val b.val=4) then 1 else 2

def freeShape (five : Bool) : List Core.PhysicalUnit :=
  (PricingABD.ABGeometry.orderedPairs (freeSize five)).map fun ab =>
    ⟨true,lowVertex ⟨ab.1.val,by have := freeSize_le_five five;omega⟩,
      lowVertex ⟨ab.2.val,by have := freeSize_le_five five;omega⟩,freeColor five ab.1 ab.2⟩

/-- Physical label of a native support coordinate. Modulo totalizes malformed
indices only; admitted instances prove the unreduced label is below61. -/
def label (p : Fin 737) (a : Nat) : Nat :=
  if a < (pairTable p).shape.free then 1+a
  else if a < (pairTable p).shape.free+(pairTable p).shape.left then
    15+digit leftOrders[p.val]! (a-(pairTable p).shape.free)
  else 31+digit rightOrders[p.val]! (a-(pairTable p).shape.free-(pairTable p).shape.left)

def label61 (p : Fin 737) (a : Nat) : Vertex := ⟨label p a % 61,Nat.mod_lt _ (by decide)⟩

def word (p : Fin 737) (j : Fin (pairTable p).count) : List Core.PhysicalUnit :=
  (crossPairs (pairTable p).shape).map fun ab =>
    ⟨true,label61 p ab.1.val,label61 p ab.2.val,
      matrix (pairTable p).shape ((pairTable p).representative j) ab.1 ab.2⟩

/-- Every nonroot vertex other than the mark gets its exact membership sign. -/
def membershipFor (five : Bool) (ls rs : Finset Nat) : List Core.PhysicalUnit :=
  ((List.finRange 14).map fun i => ⟨decide (i.val<freeSize five),60,lowVertex i,3⟩) ++
  ((List.finRange 16).map fun i => ⟨decide (i.val∈ls),60,leftVertex i,3⟩) ++
  ((List.finRange 16).map fun i => ⟨decide (i.val∈rs),60,rightVertex i,3⟩) ++
  ((List.finRange 13).map fun i => ⟨false,60,markedVertex ⟨i.val,by omega⟩,3⟩)

def membership (five : Bool) (p : Fin 737) : List Core.PhysicalUnit :=
  membershipFor five (retained p).left (retained p).right

def units (five lt rt : Bool) (p : Fin 737) (j : Fin (pairTable p).count) : List Core.PhysicalUnit :=
  spokes ++ templates lt rt ++ freeShape five ++ word p j ++ membership five p

def formula (five lt rt : Bool) (p : Fin 737) (j : Fin (pairTable p).count) : Ramsey61.DenseCounter.CNF :=
  Core.formula (units five lt rt p j)
end UniformK61.CEntrance.Formula
