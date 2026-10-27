import UniformK61.CEntranceCatalogueData
import UniformK61.CEntranceFormula

set_option autoImplicit false
namespace UniformK61.EmitCEntrance

def literalText (l : Ramsey61.DenseCounter.Literal) : String :=
  (if l.1 then "" else "-") ++ toString l.2

def clauseText (clause : List Ramsey61.DenseCounter.Literal) : String :=
  String.intercalate " " (clause.map literalText) ++ " 0\n"

end UniformK61.EmitCEntrance

/-- Emit the shared base and every direct C entrance, in catalogue order. -/
def main (args : List String) : IO Unit := do
  let [basePath, unitsPath] := args | throw (IO.userError "expected base-body and C-unit-table paths")
  if basePath == unitsPath then throw (IO.userError "output paths must differ")
  for path in [basePath, unitsPath] do
    if ←(System.FilePath.mk path).pathExists then
      throw (IO.userError "refusing an existing output file")
  IO.FS.writeFile basePath (String.join (UniformK61.Core.baseCNF.map UniformK61.EmitCEntrance.clauseText))
  let handle ← IO.FS.Handle.mk unitsPath IO.FS.Mode.write
  for k in List.finRange 346 do
    let units := UniformK61.CEntrance.Formula.units
      (UniformK61.CEntrance.Catalogue.five k)
      (UniformK61.CEntrance.Catalogue.leftType k)
      (UniformK61.CEntrance.Catalogue.rightType k)
      (UniformK61.CEntrance.Catalogue.pair k)
      (UniformK61.CEntrance.Catalogue.rep k)
    let literals := units.map (fun u => UniformK61.EmitCEntrance.literalText (UniformK61.Core.unitLiteral u))
    handle.putStrLn (UniformK61.CEntrance.Catalogue.caseId k ++ " " ++ toString units.length ++ " " ++
      String.intercalate " " literals)
  handle.flush
