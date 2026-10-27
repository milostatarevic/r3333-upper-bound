import UniformK61.BalancedEncodingValuation

/-! Evaluated finite tables for serialization. The equalities below preserve
all ordered clauses, rather than only their satisfying assignments. -/
set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

def supportTable : Array (Array (Array (List (Fin 11)))) :=
  Array.ofFn fun k : Fin 6 => Array.ofFn fun q : Fin 3 => Array.ofFn fun t : Fin 11 => memberSupport k q t

def cachedSupport (k : Fin 6) (q : Fin 3) (t : Fin 11) : List (Fin 11) :=
  ((supportTable[k.val]'(by simp [supportTable]))[q.val]'(by simp [supportTable]))[t.val]'(by simp [supportTable])

theorem cachedSupport_eq (k : Fin 6) (q : Fin 3) (t : Fin 11) : cachedSupport k q t = memberSupport k q t := by
  simp [cachedSupport,supportTable]

def anchorColorTable : Array (Array (Array (Fin 3))) :=
  Array.ofFn fun k : Fin 6 => Array.ofFn fun a : Fin 5 => Array.ofFn fun t : Fin 11 => stateColor k (anchorPosition a) (memberPosition t)

def cachedColor (s : Scope) (k : Fin 6) (a : Fin 5) (t : Fin 11) : Color :=
  foreign (scopeColor s) (((anchorColorTable[k.val]'(by simp [anchorColorTable]))[a.val]'(by simp [anchorColorTable]))[t.val]'(by simp [anchorColorTable]))

theorem cachedColor_eq (s : Scope) (k : Fin 6) (a : Fin 5) (t : Fin 11) : cachedColor s k a t = statePhysicalColor s k a t := by
  simp [cachedColor,anchorColorTable,statePhysicalColor]

def fastAnchorClauses (o : Owner) (s : Scope) (m : Fin 16) (t : Fin 11) (a : Fin 5) : CNF :=
  if decide (∀ k : Fin 6, cachedColor s k a t = cachedColor s 0 a t) then
    [[negative (roleAtom s m t),positive (anchorAtom o s m a (cachedColor s 0 a t))]]
  else
    (((List.finRange 3).filter fun q => !decide (∃ k : Fin 6, cachedColor s k a t = foreign (scopeColor s) q)).map
      fun q => [negative (roleAtom s m t),negative (anchorAtom o s m a (foreign (scopeColor s) q))]) ++
    (List.finRange 6).map fun k =>
      [negative (roleAtom s m t),negative (stateAtom s k),positive (anchorAtom o s m a (cachedColor s k a t))]

theorem fastAnchorClauses_eq (o : Owner) (s : Scope) (m : Fin 16) (t : Fin 11) (a : Fin 5) :
    fastAnchorClauses o s m t a = anchorClauses o s m t a := by
  simp only [fastAnchorClauses,cachedColor_eq,anchorClauses,constantAnchor,possibleAnchor]

def fastMemberClauses (o : Owner) (s : Scope) (a b : Fin 16) (t : Fin 11) : CNF :=
  let q := memberColor o s a b
  if decide (∀ k : Fin 6, cachedSupport k q t = cachedSupport 0 q t) then
    [[negative (roleAtom s a t),negative (activeAtom s b)] ++
      (cachedSupport 0 q t).map fun u => positive (roleAtom s b u)]
  else (List.finRange 6).map fun k =>
    [negative (roleAtom s a t),negative (stateAtom s k),negative (activeAtom s b)] ++
      (cachedSupport k q t).map fun u => positive (roleAtom s b u)

theorem fastMemberClauses_eq (o : Owner) (s : Scope) (a b : Fin 16) (t : Fin 11) :
    fastMemberClauses o s a b t = memberClauses o s a b t := by
  simp only [fastMemberClauses,cachedSupport_eq,memberClauses,constantSupport]
  rfl

def fastEmbeddingClauses (o : Owner) (s : Scope) : CNF :=
  oneHot (stateAtom s) ++
  (List.finRange 16).flatMap (domains s) ++
  (pairs 16).flatMap (fun (a,b) => (List.finRange 11).map fun t => [negative (roleAtom s a t),negative (roleAtom s b t)]) ++
  (List.finRange 16).flatMap (fun m => (List.finRange 11).flatMap fun t => (List.finRange 5).flatMap fun a => fastAnchorClauses o s m t a) ++
  (pairs 16).flatMap (fun (a,b) => (List.finRange 11).flatMap fun t => fastMemberClauses o s a b t)

theorem fastEmbeddingClauses_eq (o : Owner) (s : Scope) : fastEmbeddingClauses o s = embeddingClauses o s := by
  simp only [fastEmbeddingClauses,fastAnchorClauses_eq,fastMemberClauses_eq,embeddingClauses]

def fastFormula (o : Owner) : CNF :=
  Core.baseCNF ++ (spokes ++ templates o ++ gridOneHot ++ mixedTriangles o ++
  (List.finRange 32).flatMap (selectorClauses o) ++
  (List.finRange 32).flatMap (fastEmbeddingClauses o))

theorem fastFormula_eq (o : Owner) : fastFormula o = formula o := by
  have he : fastEmbeddingClauses o = embeddingClauses o := funext (fastEmbeddingClauses_eq o)
  simp only [fastFormula,he,formula,extra]

#print axioms fastFormula_eq
end UniformK61.BalancedEncoding
