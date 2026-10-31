import UniformK60.BalancedEncodingCache

/-! Exact three C1 all-five inputs: no global degree clauses, compressed
auxiliaries, and a final negative unit for each four-support selector. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingAllFive
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedHost UniformK60.BalancedEncoding

abbrev Owner := BalancedHost.Owner
abbrev Scope := Fin 32

def x (i : Fin 16) : Vertex := BalancedHost.xVertex true i
def y (i : Fin 16) : Vertex := BalancedHost.yVertex true i

def scope (s : Scope) : BalancedHost.Scope true :=
  if h : s.val < 16 then .inl ⟨s.val,h⟩ else .inr ⟨s.val-16,by omega⟩

def rootColor (v : Vertex) : Color :=
  if v.val ≤ 16 then 0 else if v.val ≤ 32 then 1 else if v.val ≤ 45 then 2 else 3

def rootClauses : CNF := ((List.finRange 60).filter fun v => v ≠ 0).map fun v =>
  [positive (edgeVar 0 v (rootColor v))]

def templateClauses (o : Owner) : CNF :=
  (pairs 16).map (fun (a,b) =>
    [positive (edgeVar (x a) (x b) (foreign 0 (R4333.k16Template o.1 a b)))]) ++
  (pairs 16).map (fun (a,b) =>
    [positive (edgeVar (y a) (y b) (foreign 1 (R4333.k16Template o.2 a b)))])

abbrev guardKind (o : Owner) (s : Scope) : Bool := BalancedHost.otherKind o (scope s)
abbrev guardCount (o : Owner) (s : Scope) : Nat := (BalancedAnchor.masks false (guardKind o s)).size

def guardStart (o : Owner) (s : Scope) : Nat := 7080 +
  (((List.finRange 32).take s.val).map (guardCount o)).sum

def guardTop (o : Owner) : Nat := 7080 + ((List.finRange 32).map (guardCount o)).sum

def guardGeometry (o : Owner) (s : Scope) : GuardGeometry (otherSize (scope s)) (guardCount o s) :=
  let start := guardStart o s
  {
  center := centerVertex (scope s)
  member := otherVertex (scope s)
  color := ownColor (scope s)
  pattern := fun i => Finset.univ.filter fun v =>
    Fin.castLE (other_le (scope s)) v ∈ BalancedAnchor.pattern false (guardKind o s) i
  selector := fun i => start + i.val + 1
  distinct := fun m => own_other_ne (scope s) _ m
  }

def guards (o : Owner) : CNF := (List.finRange 32).flatMap fun s => guardClauses (guardGeometry o s)

def ready (o : Owner) (s : Scope) : AnchorReady o (scope s) := by
  intro a
  have hsize : ownSize (scope s) = 16 := by
    cases scope s <;> rfl
  rw [hsize]
  exact (UniformK61.BalancedEncodingData.anchor (ownKind o (scope s)) (center16 (scope s)) a).isLt

def embeddingGeometry (o : Owner) (s : Scope) : Geometry (otherSize (scope s)) :=
  let start := guardTop o + 182*s.val
  BalancedHost.geometry o (scope s) (ready o s)
    (fun m t => start + 11*m.val+t.val+1)
    (fun k => start + 176+k.val+1)

def embeddings (o : Owner) : CNF := (List.finRange 32).flatMap fun s =>
  embeddingClauses (embeddingGeometry o s)

def forbidFour (o : Owner) : CNF := (List.finRange 32).flatMap fun s =>
  ((List.finRange (guardCount o s)).filter fun i =>
      (BalancedAnchor.pattern false (guardKind o s) i).card = 4).map fun i =>
    [negative (guardStart o s+i.val+1)]

def finalTop (o : Owner) : Nat := guardTop o + 5824

def formula (o : Owner) : CNF := Core.baseCNF ++
  rootClauses ++ templateClauses o ++ guards o ++ embeddings o ++ forbidFour o

def fastEmbeddings (o : Owner) : CNF := (List.finRange 32).flatMap fun s =>
  fastEmbeddingClauses (embeddingGeometry o s)

def fastFormula (o : Owner) : CNF := Core.baseCNF ++
  rootClauses ++ templateClauses o ++ guards o ++ fastEmbeddings o ++ forbidFour o

theorem fastFormula_eq (o : Owner) : fastFormula o = formula o := by
  simp only [fastFormula,formula,fastEmbeddings,embeddings,fastEmbeddingClauses_eq]

end UniformK60.BalancedEncodingAllFive
