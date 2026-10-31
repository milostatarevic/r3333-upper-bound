import UniformK60.PhysicalHelpers
import UniformK61.BalancedEncodingLocal

/-! The pentagon compatibility clauses, parametric in the actual visible
member count. Only shared physical edge variables appear in comparisons. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK61.BalancedEncodingData

abbrev Host := Physical.Coloring
abbrev pairs := UniformK61.BalancedEncoding.pairs
def positive (n : Nat) : Literal := (true,n)
def negative (n : Nat) : Literal := (false,n)
abbrev oneHot := @UniformK61.BalancedEncoding.oneHot

/-- One visible neighborhood, with auxiliary slots supplied by the ordered
encoder. The geometry contains actual host vertices, never completion slots. -/
structure Geometry (n : Nat) where
  center : Vertex
  member : Fin n → Vertex
  anchor : Fin 5 → Vertex
  scopeColor : Color
  memberColor : Fin n → Fin n → Fin 3
  roleAtom : Fin n → Fin 11 → Nat
  stateAtom : Fin 6 → Nat
  center_ne : ∀ m, center ≠ member m
  anchor_ne : ∀ a m, anchor a ≠ member m

def activeAtom {n : Nat} (g : Geometry n) (m : Fin n) : Nat :=
  edgeVar g.center (g.member m) g.scopeColor

def anchorAtom {n : Nat} (g : Geometry n) (m : Fin n) (a : Fin 5) (q : Color) : Nat :=
  edgeVar (g.anchor a) (g.member m) q

def statePhysicalColor {n : Nat} (g : Geometry n) (k : Fin 6) (a : Fin 5) (t : Fin 11) : Color :=
  foreign (g.scopeColor) (stateColor k (anchorPosition a) (memberPosition t))
def constantAnchor {n : Nat} (g : Geometry n) (a : Fin 5) (t : Fin 11) : Bool :=
  decide (∀ k : Fin 6, statePhysicalColor g k a t = statePhysicalColor g 0 a t)
def possibleAnchor {n : Nat} (g : Geometry n) (a : Fin 5) (t : Fin 11) (q : Color) : Bool :=
  decide (∃ k : Fin 6, statePhysicalColor g k a t = q)
def anchorClauses {n : Nat} (g : Geometry n) (m : Fin n) (t : Fin 11) (a : Fin 5) : CNF :=
  if constantAnchor g a t then
    [[negative (g.roleAtom m t),positive (anchorAtom g m a (statePhysicalColor g 0 a t))]]
  else
    (((List.finRange 3).filter fun q => !possibleAnchor g a t (foreign (g.scopeColor) q)).map
      fun q => [negative (g.roleAtom m t),negative (anchorAtom g m a (foreign (g.scopeColor) q))]) ++
    (List.finRange 6).map fun k =>
      [negative (g.roleAtom m t),negative (g.stateAtom k),positive (anchorAtom g m a (statePhysicalColor g k a t))]

def memberSupport (k : Fin 6) (q : Fin 3) (t : Fin 11) : List (Fin 11) :=
  (List.finRange 11).filter fun u => u ≠ t ∧ stateColor k (memberPosition t) (memberPosition u) = q

def constantSupport (q : Fin 3) (t : Fin 11) : Bool :=
  decide (∀ k : Fin 6, memberSupport k q t = memberSupport 0 q t)
def memberClauses {n : Nat} (g : Geometry n) (a b : Fin n) (t : Fin 11) : CNF :=
  let q := g.memberColor a b
  if constantSupport q t then
    [[negative (g.roleAtom a t),negative (activeAtom g b)] ++
      (memberSupport 0 q t).map fun u => positive (g.roleAtom b u)]
  else (List.finRange 6).map fun k =>
    [negative (g.roleAtom a t),negative (g.stateAtom k),negative (activeAtom g b)] ++
      (memberSupport k q t).map fun u => positive (g.roleAtom b u)

def domains {n : Nat} (g : Geometry n) (m : Fin n) : CNF :=
  [[negative (activeAtom g m)] ++ (List.finRange 11).map fun t => positive (g.roleAtom m t)] ++
  (List.finRange 11).map (fun t => [negative (g.roleAtom m t),positive (activeAtom g m)]) ++
  (pairs 11).map fun (t,u) => [negative (g.roleAtom m t),negative (g.roleAtom m u)]

def embeddingClauses {n : Nat} (g : Geometry n) : CNF :=
  oneHot (g.stateAtom) ++
  (List.finRange n).flatMap (domains g) ++
  (pairs n).flatMap (fun (a,b) => (List.finRange 11).map fun t => [negative (g.roleAtom a t),negative (g.roleAtom b t)]) ++
  (List.finRange n).flatMap (fun m => (List.finRange 11).flatMap fun t => (List.finRange 5).flatMap fun a => anchorClauses g m t a) ++
  (pairs n).flatMap (fun (a,b) => (List.finRange 11).flatMap fun t => memberClauses g a b t)

/-- A color-preserving chart of the actual visible neighborhood gives these
witnesses; no auxiliary role represents another physical host vertex. -/
structure LocalWitness {n : Nat} (c : Host) (g : Geometry n) where
  state : Fin 6
  role : Fin n → Option (Fin 11)
  active : ∀ m, (role m).isSome = decide (c g.center (g.member m) = palette g.scopeColor)
  injective : ∀ a b t, role a = some t → role b = some t → a = b
  anchors : ∀ m t, role m = some t → ∀ a,
    c (g.anchor a) (g.member m) = palette (statePhysicalColor g state a t)
  members : ∀ a b t u, a ≠ b → role a = some t → role b = some u →
    stateColor state (memberPosition t) (memberPosition u) = g.memberColor a b

end UniformK60.BalancedEncoding
