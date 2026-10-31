import UniformK60.BalancedEncodingData

/-! Cached finite lookup tables for efficient exact serialization.
All equalities preserve every ordered clause. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK61.BalancedEncodingData

def supportTable : Array (Array (Array (List (Fin 11)))) :=
  Array.ofFn fun k : Fin 6 => Array.ofFn fun q : Fin 3 => Array.ofFn fun t : Fin 11 => memberSupport k q t

def cachedSupport (k : Fin 6) (q : Fin 3) (t : Fin 11) : List (Fin 11) :=
  ((supportTable[k.val]'(by simp [supportTable]))[q.val]'(by simp [supportTable]))[t.val]'(by simp [supportTable])

theorem cachedSupport_eq (k : Fin 6) (q : Fin 3) (t : Fin 11) : cachedSupport k q t = memberSupport k q t := by
  simp [cachedSupport,supportTable]

def anchorColorTable : Array (Array (Array (Fin 3))) :=
  Array.ofFn fun k : Fin 6 => Array.ofFn fun a : Fin 5 => Array.ofFn fun t : Fin 11 => stateColor k (anchorPosition a) (memberPosition t)

def cachedColor {n : Nat} (g : Geometry n) (k : Fin 6) (a : Fin 5) (t : Fin 11) : Color :=
  foreign (g.scopeColor) (((anchorColorTable[k.val]'(by simp [anchorColorTable]))[a.val]'(by simp [anchorColorTable]))[t.val]'(by simp [anchorColorTable]))

theorem cachedColor_eq {n : Nat} (g : Geometry n) (k : Fin 6) (a : Fin 5) (t : Fin 11) : cachedColor g k a t = statePhysicalColor g k a t := by
  simp [cachedColor,anchorColorTable,statePhysicalColor]

def fastAnchorClauses {n : Nat} (g : Geometry n) (m : Fin n) (t : Fin 11) (a : Fin 5) : CNF :=
  if decide (∀ k : Fin 6, cachedColor g k a t = cachedColor g 0 a t) then
    [[negative (g.roleAtom m t),positive (anchorAtom g m a (cachedColor g 0 a t))]]
  else
    (((List.finRange 3).filter fun q => !decide (∃ k : Fin 6, cachedColor g k a t = foreign (g.scopeColor) q)).map
      fun q => [negative (g.roleAtom m t),negative (anchorAtom g m a (foreign (g.scopeColor) q))]) ++
    (List.finRange 6).map fun k =>
      [negative (g.roleAtom m t),negative (g.stateAtom k),positive (anchorAtom g m a (cachedColor g k a t))]

theorem fastAnchorClauses_eq {n : Nat} (g : Geometry n) (m : Fin n) (t : Fin 11) (a : Fin 5) :
    fastAnchorClauses g m t a = anchorClauses g m t a := by
  simp only [fastAnchorClauses,cachedColor_eq,anchorClauses,constantAnchor,possibleAnchor]

def fastMemberClauses {n : Nat} (g : Geometry n) (a b : Fin n) (t : Fin 11) : CNF :=
  let q := g.memberColor a b
  if decide (∀ k : Fin 6, cachedSupport k q t = cachedSupport 0 q t) then
    [[negative (g.roleAtom a t),negative (activeAtom g b)] ++
      (cachedSupport 0 q t).map fun u => positive (g.roleAtom b u)]
  else (List.finRange 6).map fun k =>
    [negative (g.roleAtom a t),negative (g.stateAtom k),negative (activeAtom g b)] ++
      (cachedSupport k q t).map fun u => positive (g.roleAtom b u)

theorem fastMemberClauses_eq {n : Nat} (g : Geometry n) (a b : Fin n) (t : Fin 11) :
    fastMemberClauses g a b t = memberClauses g a b t := by
  simp only [fastMemberClauses,cachedSupport_eq,memberClauses,constantSupport]
  rfl

def fastEmbeddingClauses {n : Nat} (g : Geometry n) : CNF :=
  oneHot (g.stateAtom) ++
  (List.finRange n).flatMap (domains g) ++
  (pairs n).flatMap (fun (a,b) => (List.finRange 11).map fun t => [negative (g.roleAtom a t),negative (g.roleAtom b t)]) ++
  (List.finRange n).flatMap (fun m => (List.finRange 11).flatMap fun t => (List.finRange 5).flatMap fun a => fastAnchorClauses g m t a) ++
  (pairs n).flatMap (fun (a,b) => (List.finRange 11).flatMap fun t => fastMemberClauses g a b t)

theorem fastEmbeddingClauses_eq {n : Nat} (g : Geometry n) : fastEmbeddingClauses g = embeddingClauses g := by
  simp only [fastEmbeddingClauses,fastAnchorClauses_eq,fastMemberClauses_eq,embeddingClauses]

end UniformK60.BalancedEncoding

namespace UniformK60.BalancedEncodingData
open UniformK60.BalancedEncoding UniformK60.BalancedHost

def fastDegreeClauses (o : Owner) : Ramsey61.DenseCounter.CNF :=
  degreeSlots.flatMap fun (v,q) =>
    let neighbors := unknownNeighbors o v
    let input := fun i => Physical.edgeVar v (neighbors.getD i 0) q
    SequentialCounter.counter input neighbors.length (degreeBound o v q) (degreeStart o (v,q))

theorem fastDegreeClauses_eq (o : Owner) : fastDegreeClauses o = degreeClauses o := rfl

def fastEmbeddings (o : Owner) : Ramsey61.DenseCounter.CNF := (List.finRange 31).flatMap fun s =>
  if h : AnchorReady o (scope s) then fastEmbeddingClauses (embeddingGeometry o s h) else []

def fastFormula (o : Owner) : Ramsey61.DenseCounter.CNF := Core.baseCNF ++
  (rootClauses ++ templateClauses o ++ fastDegreeClauses o ++ guards o ++ fastEmbeddings o)

theorem fastFormula_eq (o : Owner) : fastFormula o = formula o := by
  simp only [fastFormula,formula,extra,fastEmbeddings,embeddings,fastEmbeddingClauses_eq,fastDegreeClauses_eq]

#print axioms fastFormula_eq
end UniformK60.BalancedEncodingData
