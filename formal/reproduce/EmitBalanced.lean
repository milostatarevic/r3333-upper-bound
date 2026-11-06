import UniformK60.BalancedEncodingAllFive

open Ramsey61.DenseCounter UniformK60.BalancedEncodingData

def literalText (l : Literal) : String := (if l.1 then "" else "-") ++ toString l.2

def clauseText (c : List Literal) : String :=
  String.intercalate " " (c.map literalText) ++ " 0\n"

def writeFormula (path : System.FilePath) (top : Nat) (clauses : CNF) : IO Unit := do
  let progress ← IO.getStdout
  let count := clauses.length
  progress.putStrLn s!"ready {path} vars={top} clauses={count}"
  progress.flush
  let out ← IO.FS.Handle.mk path .write
  out.putStr s!"p cnf {top} {count}\n"
  for clause in clauses do
    out.putStr (clauseText clause)
  out.flush
  progress.putStrLn s!"written {path}"
  progress.flush

def main (args : List String) : IO Unit := do
  let some folder := args.head? | throw (IO.userError "Expected output folder")
  IO.FS.createDirAll folder
  let selected := args.tail
  for (name,o) in [("UU",(false,false)),("UT",(false,true)),("TU",(true,false)),("TT",(true,true))] do
    let key := s!"C2_ROOT_{name}"
    if selected.isEmpty || selected.contains key then
      writeFormula (System.FilePath.mk folder / s!"{key}.cnf") (finalTop o) (fastFormula o)
  for (name,o) in [("UU",(false,false)),("UT",(false,true)),("TT",(true,true))] do
    let key := s!"C1_FIVE_{name}"
    if selected.isEmpty || selected.contains key then
      writeFormula (System.FilePath.mk folder / s!"{key}.cnf")
        (UniformK60.BalancedEncodingAllFive.finalTop o) (UniformK60.BalancedEncodingAllFive.fastFormula o)
