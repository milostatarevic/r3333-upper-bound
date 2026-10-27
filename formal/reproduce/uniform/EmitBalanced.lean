import UniformK61.BalancedEncodingCache

open UniformK61.BalancedEncoding UniformK61.BalancedHost

/-- Emit the three complete formulas from definitions proved equal to the
mathematical formulas. The destination must not already exist. -/
def main (args : List String) : IO UInt32 := do
  let [root] := args | throw (IO.userError "expected one fresh output directory")
  if ← System.FilePath.pathExists root then
    throw (IO.userError "output directory already exists")
  IO.FS.createDirAll root
  let err ← IO.getStderr
  for (label,owner) in [("UU",Owner.uu),("UT",Owner.ut),("TT",Owner.tt)] do
    let f := fastFormula owner
    let out ← IO.FS.Handle.mk (root ++ "/" ++ label ++ ".cnf") IO.FS.Mode.write
    out.putStrLn s!"p cnf 13656 {f.length}"
    for clause in f do
      out.putStrLn (String.intercalate " " (clause.map fun l => (if l.1 then "" else "-") ++ toString l.2) ++ " 0")
    err.putStrLn s!"{label}: {f.length} clauses"
  return 0
