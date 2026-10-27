import UniformK61.Core
import UniformK61.CommonHost
import CompletionC.SupportEdges

set_option autoImplicit false
namespace UniformK61.CommonFormula
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open CompletionC.NativeMatrices CompletionC.SupportEdges
open PricingIntegration.PairAdmission
open UniformK61.CommonHost

/-- Complete root spokes, in increasing physical vertex order. -/
def spokes (l : Layout) : List Core.PhysicalUnit :=
  ((List.finRange (lowSize l)).map fun i => ⟨true,0,lowVertex l i,0⟩) ++
  ((List.finRange (leftSize l)).map fun i => ⟨true,0,leftVertex l i,1⟩) ++
  ((List.finRange (rightSize l)).map fun i => ⟨true,0,rightVertex l i,2⟩) ++
  ((List.finRange 16).map fun i => ⟨true,0,markedVertex l i,3⟩)

def edgeUnit (l : Layout) (e : ABGeometry.Edge l) : Core.PhysicalUnit :=
  ⟨true,retain l e.1,retain l e.2.1,e.2.2⟩

def templates (l : Layout) (t : Types) : List Core.PhysicalUnit :=
  (templateEdges l t).map (edgeUnit l)
def freeShape (l : Layout) : List Core.PhysicalUnit :=
  (freeEdges l).map (edgeUnit l)

/-- Reduction modulo 61 only totalizes inadmissible metadata coordinates.
Admitted physical cases prove these coordinates are strictly below 61. -/
def label61 (l : Layout) (p : Fin 737) (a : Nat) : Vertex :=
  ⟨retainNat l (label l p a) % 61,Nat.mod_lt _ (by decide)⟩

def rawWord (l : Layout) (p : Fin 737) (j : Fin (pairTable p).count) : List Core.PhysicalUnit :=
  (crossPairs (pairTable p).shape).map fun ab =>
    ⟨true,label61 l p ab.1.val,label61 l p ab.2.val,
      matrix (pairTable p).shape ((pairTable p).representative j) ab.1 ab.2⟩

def physicalOrder (a b : Core.PhysicalUnit) : Bool :=
  decide (a.u.val < b.u.val ∨ (a.u.val=b.u.val ∧ a.v.val≤b.v.val))

/-- A/B words use support-coordinate order; D words use physical-edge order.
The ordering determines serialization and leaves the signed facts unchanged. -/
def word (l : Layout) (p : Fin 737) (j : Fin (pairTable p).count) : List Core.PhysicalUnit :=
  if l.profile=.D then (rawWord l p j).mergeSort physicalOrder else rawWord l p j

/-- Membership on all 59 nonroot vertices other than the mark. The remaining
root-mark positive unit already occurs among the spokes. -/
def membershipFor (l : Layout) (ls rs : Finset Nat) : List Core.PhysicalUnit :=
  ((List.finRange (lowSize l)).map fun i => ⟨decide (i.val<freeSize l),60,lowVertex l i,3⟩) ++
  ((List.finRange (leftSize l)).map fun i => ⟨decide (i.val∈ls),60,leftVertex l i,3⟩) ++
  ((List.finRange (rightSize l)).map fun i => ⟨decide (i.val∈rs),60,rightVertex l i,3⟩) ++
  ((List.finRange 15).map fun i => ⟨false,60,markedVertex l ⟨i.val,by omega⟩,3⟩)

def membership (l : Layout) (p : Fin 737) : List Core.PhysicalUnit :=
  membershipFor l (retained p).left (retained p).right

def units (l : Layout) (t : Types) (p : Fin 737) (j : Fin (pairTable p).count) : List Core.PhysicalUnit :=
  spokes l ++ templates l t ++ freeShape l ++ word l p j ++ membership l p

def formula (l : Layout) (t : Types) (p : Fin 737) (j : Fin (pairTable p).count) : Ramsey61.DenseCounter.CNF :=
  Core.formula (units l t p j)

end UniformK61.CommonFormula
