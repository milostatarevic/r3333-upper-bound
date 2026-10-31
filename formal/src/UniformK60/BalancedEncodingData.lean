import UniformK60.BalancedAnchorSupport
import UniformK60.BalancedEncodingGuard
import UniformK60.SequentialCounter
import UniformK60.Core
import UniformK60.BalancedEncodingAuxData

/-! Executable mixed-C1/C2 compatibility prefix. Its order and auxiliary
allocation are those of the separately audited four pentagon-only prefixes. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedHost UniformK60.BalancedEncoding

abbrev Owner := BalancedHost.Owner
abbrev Scope := Fin 31

def x (i : Fin 15) : Vertex := BalancedHost.xVertex false i
def y (i : Fin 16) : Vertex := BalancedHost.yVertex false i

def scope (s : Scope) : BalancedHost.Scope false :=
  if h : s.val < 15 then .inl ⟨s.val,h⟩ else .inr ⟨s.val-15,by omega⟩

def rootColor (v : Vertex) : Color :=
  if v.val ≤ 15 then 0 else if v.val ≤ 31 then 1 else if v.val ≤ 45 then 2 else 3

def inX (v : Vertex) : Bool := decide (1 ≤ v.val ∧ v.val ≤ 15)
def inY (v : Vertex) : Bool := decide (16 ≤ v.val ∧ v.val ≤ 31)

def localX (v : Vertex) : Fin 16 := ⟨(v.val-1)%16,Nat.mod_lt _ (by decide)⟩
def localY (v : Vertex) : Fin 16 := ⟨(v.val-16)%16,Nat.mod_lt _ (by decide)⟩

def fixedColor (o : Owner) (a b : Vertex) : Option Color :=
  if a = 0 then some (rootColor b) else if b = 0 then some (rootColor a)
  else if inX a && inX b then some (foreign 0 (R4333.k16Template o.1 (localX a) (localX b)))
  else if inY a && inY b then some (foreign 1 (R4333.k16Template o.2 (localY a) (localY b)))
  else none

def rootClauses : CNF := ((List.finRange 60).filter fun v => v ≠ 0).map fun v =>
  [positive (edgeVar 0 v (rootColor v))]

def templateClauses (o : Owner) : CNF :=
  (pairs 15).map (fun (a,b) =>
    [positive (edgeVar (x a) (x b) (foreign 0 (R4333.k16Template o.1 a.castSucc b.castSucc)))]) ++
  (pairs 16).map (fun (a,b) =>
    [positive (edgeVar (y a) (y b) (foreign 1 (R4333.k16Template o.2 a b)))])

def cap (q : Color) : Nat := if q.val < 2 then 16 else 14

def unknownNeighbors (o : Owner) (v : Vertex) : List Vertex :=
  (List.finRange 60).filter fun u => u ≠ v ∧ fixedColor o v u = none

def knownTrue (o : Owner) (v : Vertex) (q : Color) : Nat :=
  ((List.finRange 60).filter fun u => u ≠ v ∧ fixedColor o v u = some q).length

def degreeInput (o : Owner) (v : Vertex) (q : Color) (i : Nat) : Nat :=
  edgeVar v ((unknownNeighbors o v).getD i 0) q

def degreeBound (o : Owner) (v : Vertex) (q : Color) : Nat := cap q - knownTrue o v q

abbrev DegreeSlot := Vertex × Color

def degreeSlots : List DegreeSlot :=
  (List.finRange 60).flatMap fun v => (List.finRange 4).map fun q => (v,q)

def degreeNext (o : Owner) (top : Nat) (d : DegreeSlot) : Nat :=
  SequentialCounter.finalTop (unknownNeighbors o d.1).length (degreeBound o d.1 d.2) top

def degreeStart (o : Owner) (d : DegreeSlot) : Nat := BalancedAuxData.degreeStart o d.1 d.2

def degreeEnd (o : Owner) (d : DegreeSlot) : Nat := BalancedAuxData.degreeEnd o d.1 d.2

def degreeTop (_o : Owner) : Nat := 122259

def degreeClauses (o : Owner) : CNF := degreeSlots.flatMap fun (v,q) =>
  SequentialCounter.counter (degreeInput o v q) (unknownNeighbors o v).length
    (degreeBound o v q) (degreeStart o (v,q))

def otherMinor (s : Scope) : Bool := decide (15 ≤ s.val)
abbrev guardKind (o : Owner) (s : Scope) : Bool := BalancedHost.otherKind o (scope s)
abbrev guardCount (o : Owner) (s : Scope) : Nat :=
  (BalancedAnchor.masks (otherMinor s) (guardKind o s)).size

def guardStart (o : Owner) (s : Scope) : Nat := degreeTop o +
  (((List.finRange 31).take s.val).map (guardCount o)).sum

def guardTop (o : Owner) : Nat := degreeTop o + ((List.finRange 31).map (guardCount o)).sum

def guardGeometry (o : Owner) (s : Scope) :
    GuardGeometry (otherSize (scope s)) (guardCount o s) :=
  let start := guardStart o s
  {
  center := centerVertex (scope s)
  member := otherVertex (scope s)
  color := ownColor (scope s)
  pattern := fun i => Finset.univ.filter fun v =>
    Fin.castLE (other_le (scope s)) v ∈ BalancedAnchor.pattern (otherMinor s) (guardKind o s) i
  selector := fun i => start + i.val + 1
  distinct := fun m => own_other_ne (scope s) _ m
  }

def guards (o : Owner) : CNF := (List.finRange 31).flatMap fun s => guardClauses (guardGeometry o s)

/-- IDs of the omitted P4 blocks remain reserved, exactly as in the audited
projection of the original31-scope encoder. -/
def embeddingWidth (o : Owner) (s : Scope) : Nat :=
  if AnchorReady o (scope s) then 11*otherSize (scope s)+6 else 12*otherSize (scope s)+7

def embeddingStart (o : Owner) (s : Scope) : Nat := guardTop o +
  (((List.finRange 31).take s.val).map (embeddingWidth o)).sum

def finalTop (o : Owner) : Nat := guardTop o + ((List.finRange 31).map (embeddingWidth o)).sum

def embeddingGeometry (o : Owner) (s : Scope) (h : AnchorReady o (scope s)) :
    Geometry (otherSize (scope s)) :=
  let start := embeddingStart o s
  let n := otherSize (scope s)
  BalancedHost.geometry o (scope s) h
    (fun m t => start + 11*m.val+t.val+1)
    (fun k => start + 11*n+k.val+1)

def embeddings (o : Owner) : CNF := (List.finRange 31).flatMap fun s =>
  if h : AnchorReady o (scope s) then embeddingClauses (embeddingGeometry o s h) else []

def extra (o : Owner) : CNF :=
  rootClauses ++ templateClauses o ++ degreeClauses o ++ guards o ++ embeddings o

def formula (o : Owner) : CNF := Core.baseCNF ++ extra o

end UniformK60.BalancedEncodingData
