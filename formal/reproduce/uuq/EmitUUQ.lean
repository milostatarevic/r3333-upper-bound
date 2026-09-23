import PricingG.UUQEmissionIdentity

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open PricingIntegration R4333

namespace UUQReproduce

def sparseLiteral : Sat.Literal → String
  | .pos a => toString (a + 1)
  | .neg a => "-" ++ toString (a + 1)

def emitFamily {n : Nat} (dir : System.FilePath) (name : String)
    (size : Nat) (table : Std.HashMap Nat Nat) (f : Fin n → Sat.Fmla) : IO Unit := do
  let sp := dir / (name ++ "_SPARSE.tsv")
  let np := dir / (name ++ "_NATIVE.tsv")
  if (← sp.pathExists) || (← np.pathExists) then throw (IO.userError "Refusing to overwrite an emission")
  let sout ← IO.FS.Handle.mk sp .write
  let nout ← IO.FS.Handle.mk np .write
  for i in List.finRange n do
    let source := f i
    let dense := NativeRenaming.formula (NativeRenaming.encode size table) source
    let ss := source.map fun cl => String.intercalate " " (cl.map sparseLiteral)
    let ns := dense.map fun cl => String.intercalate " " (cl.map fun lit =>
      if lit.1 then toString lit.2 else "-" ++ toString lit.2)
    sout.putStr (toString i.val ++ "\t" ++ String.intercalate "\t" ss ++ "\n")
    nout.putStr (toString i.val ++ "\t" ++ String.intercalate "\t" ns ++ "\n")
  sout.flush
  nout.flush
  IO.println s!"EMITTED {name}: {n} sparse/native suffix pairs"

def emitAll (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then throw (IO.userError "Output directory must be fresh")
  if let some parent := dir.parent then IO.FS.createDirAll parent
  IO.FS.createDir dir
  let m4 := DNativeMaps.fourForward
  let m5 := DNativeMaps.fiveForward
  emitFamily dir "P15_MATRIX_ONLY_189" DNativeMaps.fourSize m4 PricingG.P15FastUnits.units
  emitFamily dir "D9_STRONG_ROOT2" DNativeMaps.fiveSize m5 PricingG.D9StrongFast.units
  emitFamily dir "D9_TWISTED_ROOT1" DNativeMaps.fiveSize m5 PricingG.D9Root1Fast.units
  emitFamily dir "D9_TWISTED_ROOT4" DNativeMaps.fiveSize m5 PricingG.D9Root4Fast.units
  emitFamily dir "D9_TWISTED_ROOT12" DNativeMaps.fiveSize m5 PricingG.D9Root12Fast.units
  emitFamily dir "D10_B2P15_82" DNativeMaps.fiveSize m5 PricingG.D10ArraySuffix.arraySuffix

end UUQReproduce

def main (args : List String) : IO UInt32 := do
  match args with
  | [output] =>
    UUQReproduce.emitAll (System.FilePath.mk output)
    return 0
  | _ =>
    IO.eprintln "Usage: lean --run EmitUUQ.lean FRESH_OUTPUT_DIRECTORY"
    return 2
