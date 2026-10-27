import UniformK61.MarkedUU

/-! Direct ordered unit export for both complete 679-leaf U/U owners. -/
set_option autoImplicit false
namespace UniformK61.EmitMarkedUU

def literalText (l : Ramsey61.DenseCounter.Literal) : String :=
  (if l.1 then "" else "-") ++ toString l.2

def emit (directory : System.FilePath) (q : Bool) : IO Unit := do
  let owner := if q then "UUT" else "UUU"
  let handle ← IO.FS.Handle.mk (directory / (owner ++ ".tsv")) IO.FS.Mode.write
  handle.putStrLn ("MARKED_UU\t" ++ owner ++ "\t679")
  for i in List.finRange 679 do
    let units := MarkedUU.caseUnits q i
    handle.putStrLn ("LEAF\t" ++ toString i.val ++ "\t" ++ toString units.length ++ "\t" ++
      String.intercalate "," (units.map fun u => literalText (Core.unitLiteral u)))
  handle.flush
  IO.println ("COMPLETE " ++ owner ++ " 679")
end UniformK61.EmitMarkedUU

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "expected one fresh output directory")
  let directory := System.FilePath.mk destination
  if ←directory.pathExists then throw (IO.userError "refusing an existing output directory")
  IO.FS.createDir directory
  UniformK61.EmitMarkedUU.emit directory false
  UniformK61.EmitMarkedUU.emit directory true
