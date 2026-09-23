import Mathlib.Tactic.Sat.FromLRAT

/-!
# LRAT evidence tied to a Lean-defined CNF

Mathlib's `lrat_proof` command produces a kernel-checked propositional
theorem, but its public command reifies the DIMACS variables as fresh
propositions.  For the Ramsey development it is more convenient to retain
the underlying semantic statement

```text
expectedCNF.proof []
```

where `expectedCNF : Sat.Fmla` is an ordinary Lean definition.  The command
below invokes Mathlib's existing proof-term constructor and asks Lean to add
the resulting proof at exactly that type.  Declaration checking succeeds
only when the clause list parsed from the DIMACS text is definitionally equal
to the supplied Lean formula.  Thus neither a hash comparison nor the
external DIMACS writer is part of the trusted bridge.

The command is elaborator code only.  It cannot assert a false theorem: the
generated declaration and all definitional equalities are checked by Lean's
kernel.
-/

open Lean Elab Term Command Meta

namespace R4333

/-- Import LRAT evidence while fixing its theorem type to a Lean-defined
`Sat.Fmla`.  A mismatch between the supplied formula and DIMACS clause order
causes elaboration to fail. -/
elab "checked_lrat_proof " n:ident ppSpace expected:term:max
    ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let expectedExpr ←
      instantiateMVars (← elabTermEnsuringType expected (mkConst ``Sat.Fmla))
    let cnfText ← unsafe evalTerm String (mkConst ``String) cnf
    let lratText ← unsafe evalTerm String (mkConst ``String) lrat
    let (_, _, _, proofRaw) ←
      Mathlib.Tactic.Sat.fromLRATAux cnfText lratText name
    let proof ← instantiateMVars proofRaw
    let target ← instantiateMVars <|
      mkApp2 (mkConst ``Sat.Fmla.proof) expectedExpr (mkConst ``Sat.Clause.nil)
    let actual ← inferType proof
    unless ← isDefEq actual target do
      throwError "DIMACS clauses are not definitionally equal to the supplied Lean CNF"
    let proof ← instantiateMVars proof
    let target ← instantiateMVars target
    if proof.hasMVar then
      throwError "generated LRAT proof still contains metavariables"
    if target.hasMVar then
      throwError "checked LRAT theorem type still contains metavariables"
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := target
      value := proof
    }

/-! ## End-to-end regression test -/

/-- The authoritative Lean form of the four-clause two-variable toy. -/
def checkedTwoBitToyCNF : Sat.Fmla :=
  [ [Sat.Literal.pos 0, Sat.Literal.pos 1]
  , [Sat.Literal.neg 0, Sat.Literal.pos 1]
  , [Sat.Literal.pos 0, Sat.Literal.neg 1]
  , [Sat.Literal.neg 0, Sat.Literal.neg 1]
  ]

checked_lrat_proof checkedTwoBitToyUnsat checkedTwoBitToyCNF
  "p cnf 2 4
   1 2 0
   -1 2 0
   1 -2 0
   -1 -2 0"
  "5 -2 0 4 3 0
   5 d 3 4 0
   6 1 0 5 1 0
   6 d 1 0
   7 0 5 2 6 0"

/-- The raw semantic consequence needed by finite-model bridges. -/
theorem checkedTwoBitToy_noValuation
    (v : Sat.Valuation) (h : v.satisfies_fmla checkedTwoBitToyCNF) : False :=
  checkedTwoBitToyUnsat v h

#print axioms R4333.checkedTwoBitToyUnsat
#print axioms R4333.checkedTwoBitToy_noValuation

end R4333
