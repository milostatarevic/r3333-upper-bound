import R4333Lean.ClebschCompletionData

/-!
# Authoritative CNF for decompositions of the Clebsch complement

After fixing one colour to the canonical Clebsch graph, the other eighty
edges receive one Boolean choice.  The first clauses forbid a monochromatic
triangle in either remaining colour.  The final clauses block the seventy-two
explicit completions one at a time.
-/

namespace R4333

open FiniteColorCNF

/-- Canonical unordered-pair code used by the finite red graph. -/
def canonicalPairCode (a b : Nat) : Nat := min a b * 16 + max a b

/-- The fixed canonical Clebsch edge predicate. -/
def canonicalClebschRed (a b : Nat) : Bool :=
  decide (canonicalPairCode a b ∈ canonicalClebschRedCodes)

/-- Zero-based Boolean variable for a non-red edge. -/
def clebschComplementIndex (a b : Nat) : Nat :=
  clebschComplementEdges.idxOf (min a b, max a b)

/-- The two NAE clauses for a triple containing no fixed red edge. -/
def clebschCompletionTripleClauses (t : Nat × Nat × Nat) : Sat.Fmla :=
  if canonicalClebschRed t.1 t.2.1 ∨
      canonicalClebschRed t.1 t.2.2 ∨
      canonicalClebschRed t.2.1 t.2.2 then
    []
  else
    [ [Sat.Literal.pos (clebschComplementIndex t.1 t.2.1),
       Sat.Literal.pos (clebschComplementIndex t.1 t.2.2),
       Sat.Literal.pos (clebschComplementIndex t.2.1 t.2.2)]
    , [Sat.Literal.neg (clebschComplementIndex t.1 t.2.1),
       Sat.Literal.neg (clebschComplementIndex t.1 t.2.2),
       Sat.Literal.neg (clebschComplementIndex t.2.1 t.2.2)]
    ]

/-- A clause excluding one complete Boolean edge vector. -/
def clebschCompletionBlocker (bits : List Bool) : Sat.Clause :=
  (List.range 80).map fun i =>
    if bits.getD i false then Sat.Literal.neg i else Sat.Literal.pos i

/-- The complete Lean-generated exhaustion formula. -/
def clebschCompletionFmla : Sat.Fmla :=
  (triples 16).flatMap clebschCompletionTripleClauses ++
    clebschDecompositions.map clebschCompletionBlocker

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

checked_lrat_proof clebschCompletion_unsat clebschCompletionFmla
  (include_str "../r4333_upper/catalogue_work_certificate/leaves/clebsch_complement_72_exhaustive.cnf")
  (include_str "../r4333_upper/catalogue_work_certificate/leaves/clebsch_complement_72_exhaustive.lrat")

#print axioms R4333.clebschCompletion_unsat

end R4333
