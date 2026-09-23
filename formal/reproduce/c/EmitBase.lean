import Ramsey61.CEncodingBase
open Ramsey61.DenseCounter Ramsey61.CEncodingCore Ramsey61.CEncodingBase

def literalText (literal : Literal) : String :=
  (if literal.1 then "" else "-") ++ toString literal.2

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "expected one create-only output path")
  if ← System.FilePath.pathExists destination then
    throw (IO.userError "refusing to overwrite existing output")
  let handle ← IO.FS.Handle.mk destination IO.FS.Mode.write
  let stdout ← IO.getStdout
  -- Same definitions in precisely broaderBaseCNF concatenation order.
  let sections : List (String × (Unit → CNF)) := [
    ("core",fun _ => coreCNF), ("highness",fun _ => highnessClauses),
    ("H",fun _ => HClauses), ("profile",fun _ => profileClauses),
    ("selector",fun _ => selectorClauses), ("root",fun _ => rootClauses),
    ("fiber",fun _ => fiberClauses)]
  handle.putStr "p cnf 439723 1880888\n"
  handle.flush
  let mut count := 0
  for (name, make) in sections do
    stdout.putStr s!"starting {name}\n"
    stdout.flush
    let start ← IO.monoMsNow
    let formula := make ()
    for clause in formula do
      handle.putStr (String.intercalate " " (clause.map literalText) ++ " 0\n")
      count := count + 1
    handle.flush
    let stop ← IO.monoMsNow
    stdout.putStr s!"finished {name}, total_clauses={count}, elapsed_ms={stop-start}\n"
    stdout.flush
  if count != 1880888 then throw (IO.userError s!"unexpected count {count}")
  IO.println s!"base_clauses={count}"
