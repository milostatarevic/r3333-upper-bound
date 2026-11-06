import UniformK60.Core

/-! Emit the K60 base body only: no DIMACS header and no solver invocation. -/
set_option autoImplicit false

namespace UniformK60.EmitBase
open Ramsey61.DenseCounter

def literalText (literal : Literal) : String :=
  (if literal.1 then "" else "-") ++ toString literal.2

def clauseText (clause : List Literal) : String :=
  String.intercalate " " (clause.map literalText) ++ " 0\n"

end UniformK60.EmitBase

def main : IO Unit := do
  let out ← IO.getStdout
  out.putStr (String.join (UniformK60.Core.baseCNF.map UniformK60.EmitBase.clauseText))
