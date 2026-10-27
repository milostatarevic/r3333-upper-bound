import UniformK61.BalancedEncodingData
import UniformK61.Core

/-! Exact ordered balanced CNF and its finite local witness interface. -/

set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

abbrev Scope := Fin 32

def side (s : Scope) : Fin 2 := ⟨s.val / 16, by omega⟩
def center (s : Scope) : Fin 16 := ⟨s.val % 16, Nat.mod_lt _ (by decide)⟩
def ownKind (o : Owner) (s : Scope) : Bool := if side s = 0 then o.left else o.right
def otherKind (o : Owner) (s : Scope) : Bool := if side s = 0 then o.right else o.left
def ownVertex (s : Scope) (v : Fin 16) : Vertex := if side s = 0 then xVertex v else yVertex v
def otherVertex (s : Scope) (v : Fin 16) : Vertex := if side s = 0 then yVertex v else xVertex v
def scopeColor (s : Scope) : Color := if side s = 0 then 1 else 0
def guardColor (s : Scope) : Color := if side s = 0 then 0 else 1
def activeAtom (s : Scope) (m : Fin 16) : Nat := edgeVar (ownVertex s (center s)) (otherVertex s m) (scopeColor s)
def guardAtom (s : Scope) (m : Fin 16) : Nat := edgeVar (ownVertex s (center s)) (otherVertex s m) (guardColor s)
def anchorVertex (o : Owner) (s : Scope) (a : Fin 5) : Vertex := ownVertex s (anchor (ownKind o s) (center s) a)
def anchorAtom (o : Owner) (s : Scope) (m : Fin 16) (a : Fin 5) (q : Color) : Nat :=
  edgeVar (anchorVertex o s a) (otherVertex s m) q

def patternAtom (s : Scope) (i : Fin 16) : Nat := 7321 + 16*s.val+i.val
def firstAtom (s : Scope) : Nat := 7833 + 182*s.val
def roleAtom (s : Scope) (m : Fin 16) (t : Fin 11) : Nat := firstAtom s + 11*m.val+t.val
def stateAtom (s : Scope) (t : Fin 6) : Nat := firstAtom s + 176+t.val

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => ((List.finRange n).filter fun b => a < b).map fun b => (a,b)
def positive (n : Nat) : Literal := (true,n)
def negative (n : Nat) : Literal := (false,n)
def oneHot {n : Nat} (vars : Fin n → Nat) : CNF :=
  [(List.finRange n).map fun i => positive (vars i)] ++
  (pairs n).map fun (a,b) => [negative (vars a),negative (vars b)]

def statePhysicalColor (s : Scope) (k : Fin 6) (a : Fin 5) (t : Fin 11) : Color :=
  foreign (scopeColor s) (stateColor k (anchorPosition a) (memberPosition t))
def constantAnchor (s : Scope) (a : Fin 5) (t : Fin 11) : Bool :=
  decide (∀ k : Fin 6, statePhysicalColor s k a t = statePhysicalColor s 0 a t)
def possibleAnchor (s : Scope) (a : Fin 5) (t : Fin 11) (q : Color) : Bool :=
  decide (∃ k : Fin 6, statePhysicalColor s k a t = q)
def anchorClauses (o : Owner) (s : Scope) (m : Fin 16) (t : Fin 11) (a : Fin 5) : CNF :=
  if constantAnchor s a t then
    [[negative (roleAtom s m t),positive (anchorAtom o s m a (statePhysicalColor s 0 a t))]]
  else
    (((List.finRange 3).filter fun q => !possibleAnchor s a t (foreign (scopeColor s) q)).map
      fun q => [negative (roleAtom s m t),negative (anchorAtom o s m a (foreign (scopeColor s) q))]) ++
    (List.finRange 6).map fun k =>
      [negative (roleAtom s m t),negative (stateAtom s k),positive (anchorAtom o s m a (statePhysicalColor s k a t))]

def memberSupport (k : Fin 6) (q : Fin 3) (t : Fin 11) : List (Fin 11) :=
  (List.finRange 11).filter fun u => u ≠ t ∧ stateColor k (memberPosition t) (memberPosition u) = q
def memberColor (o : Owner) (s : Scope) (a b : Fin 16) : Fin 3 :=
  R4333.k16Template (otherKind o s) a b

def constantSupport (q : Fin 3) (t : Fin 11) : Bool :=
  decide (∀ k : Fin 6, memberSupport k q t = memberSupport 0 q t)
def memberClauses (o : Owner) (s : Scope) (a b : Fin 16) (t : Fin 11) : CNF :=
  let q := memberColor o s a b
  if constantSupport q t then
    [[negative (roleAtom s a t),negative (activeAtom s b)] ++
      (memberSupport 0 q t).map fun u => positive (roleAtom s b u)]
  else (List.finRange 6).map fun k =>
    [negative (roleAtom s a t),negative (stateAtom s k),negative (activeAtom s b)] ++
      (memberSupport k q t).map fun u => positive (roleAtom s b u)

def domains (s : Scope) (m : Fin 16) : CNF :=
  [[negative (activeAtom s m)] ++ (List.finRange 11).map fun t => positive (roleAtom s m t)] ++
  (List.finRange 11).map (fun t => [negative (roleAtom s m t),positive (activeAtom s m)]) ++
  (pairs 11).map fun (t,u) => [negative (roleAtom s m t),negative (roleAtom s m u)]

def embeddingClauses (o : Owner) (s : Scope) : CNF :=
  oneHot (stateAtom s) ++
  (List.finRange 16).flatMap (domains s) ++
  (pairs 16).flatMap (fun (a,b) => (List.finRange 11).map fun t => [negative (roleAtom s a t),negative (roleAtom s b t)]) ++
  (List.finRange 16).flatMap (fun m => (List.finRange 11).flatMap fun t => (List.finRange 5).flatMap fun a => anchorClauses o s m t a) ++
  (pairs 16).flatMap (fun (a,b) => (List.finRange 11).flatMap fun t => memberClauses o s a b t)

def selectorClauses (o : Owner) (s : Scope) : CNF :=
  oneHot (patternAtom s) ++
  (List.finRange 16).flatMap fun i => (List.finRange 16).map fun m =>
    [negative (patternAtom s i),(decide (m ∈ support (otherKind o s) i),guardAtom s m)]

def spokes : CNF := (List.finRange 60).map fun v =>
  [positive (edgeVar 0 (BalancedHost.vertex v) (BalancedHost.rootColor v))]
def templates (o : Owner) : CNF :=
  (pairs 16).map (fun (a,b) => [positive (edgeVar (xVertex a) (xVertex b) (foreign 0 (R4333.k16Template o.left a b)))]) ++
  (pairs 16).map (fun (a,b) => [positive (edgeVar (yVertex a) (yVertex b) (foreign 1 (R4333.k16Template o.right a b)))])
def gridOneHot : CNF := (List.finRange 16).flatMap fun x =>
  (List.finRange 16).flatMap fun y => oneHot (edgeVar (xVertex x) (yVertex y))
def mixedTriangles (o : Owner) : CNF := (pairs 16).flatMap fun (a,b) =>
  (List.finRange 16).flatMap fun v =>
    [[negative (edgeVar (xVertex a) (yVertex v) (foreign 0 (R4333.k16Template o.left a b))),
      negative (edgeVar (xVertex b) (yVertex v) (foreign 0 (R4333.k16Template o.left a b)))],
     [negative (edgeVar (xVertex v) (yVertex a) (foreign 1 (R4333.k16Template o.right a b))),
      negative (edgeVar (xVertex v) (yVertex b) (foreign 1 (R4333.k16Template o.right a b)))]]
def extra (o : Owner) : CNF :=
  spokes ++ templates o ++ gridOneHot ++ mixedTriangles o ++
  (List.finRange 32).flatMap (selectorClauses o) ++
  (List.finRange 32).flatMap (embeddingClauses o)
def formula (o : Owner) : CNF := Core.baseCNF ++ extra o

/-- Coordinates in one of the six literal-template states for the whole
observed opposite neighborhood. Inactive members have no role. -/
structure LocalWitness (c : Host) (o : Owner) (s : Scope) where
  state : Fin 6
  role : Fin 16 → Option (Fin 11)
  active : ∀ m, (role m).isSome = decide (c (ownVertex s (center s)) (otherVertex s m) = palette (scopeColor s))
  injective : ∀ a b t, role a = some t → role b = some t → a = b
  anchors : ∀ m t, role m = some t → ∀ a,
    c (anchorVertex o s a) (otherVertex s m) = palette (statePhysicalColor s state a t)
  members : ∀ a b t u, a ≠ b → role a = some t → role b = some u →
    stateColor state (memberPosition t) (memberPosition u) = memberColor o s a b

/-- The only finite-classification interface used by the encoder. The
actual-neighborhood coverage theorem constructs these witnesses separately. -/
structure Witnesses (c : Host) (o : Owner) where
  pattern : Scope → Fin 16
  patterns : ∀ s m, (c (ownVertex s (center s)) (otherVertex s m) = palette (guardColor s)) ↔
    m ∈ support (otherKind o s) (pattern s)
  scopes : ∀ s, LocalWitness c o s

end UniformK61.BalancedEncoding
