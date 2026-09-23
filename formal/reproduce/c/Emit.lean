import Ramsey61.CConcreteFamily
open Ramsey61.DenseCounter Ramsey61.CConcreteFamily

/-- Runtime-only emission of the exact unit suffixes in concreteFamily. -/
def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "expected one fresh output directory")
  let dir := System.FilePath.mk destination
  if ← dir.pathExists then throw (IO.userError "refusing an existing output directory")
  IO.FS.createDir dir
  let mut count := 0
  for i in List.finRange 456 do
    let out ← IO.FS.Handle.mk (dir / s!"R3_{i.val}.units") .write
    for literal in seedLiterals i do
      if literal.2 == 0 then throw (IO.userError "zero DIMACS variable")
      out.putStr ((if literal.1 then "" else "-") ++ toString literal.2 ++ " 0\n")
      count := count + 1
    out.flush
  IO.println s!"cases=456 unit_clauses={count}"
