import PricingIntegration.DNativePrefix

namespace PortableDNativePrefixes
open PricingABD.ABLayout Ramsey61.DenseCounter PricingIntegration
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def cachedFour (table : Std.HashMap Nat Nat) (t : Types) : CNF :=
  NativeRenaming.formula (NativeRenaming.encode DNativeMaps.fourSize table)
    (R4333.ProfileDFourRowCNF.fmla (DFrameColoring.kind t))
def cachedFive (table : Std.HashMap Nat Nat) (t : Types) : CNF :=
  NativeRenaming.formula (NativeRenaming.encode DNativeMaps.fiveSize table)
    (R4333.ProfileDHighOwnFiveSupportC5Formula.fmla (DFrameColoring.kind t) 2 (Fin.last 15))

theorem cachedFour_eq (t : Types) :
    cachedFour DNativeMaps.fourForward t=DNativePrefix.fourFormula t := rfl
theorem cachedFive_eq (t : Types) :
    cachedFive DNativeMaps.fiveForward t=DNativePrefix.fiveFormula t := rfl

def emit (dir : System.FilePath) (name : String) (f : CNF) : IO Unit := do
  let path:=dir / (name++".body")
  if ←path.pathExists then throw (IO.userError "Refusing to overwrite an output file")
  let out←IO.FS.Handle.mk path .write
  let mut maximum:=0
  for cl in f do
    let mut parts : List String:=[]
    for lit in cl do
      if lit.2==0 then throw (IO.userError "Zero DIMACS variable")
      maximum:=max maximum lit.2
      parts:=parts++[if lit.1 then toString lit.2 else "-"++toString lit.2]
    out.putStr (String.intercalate " " parts++" 0\n")
  out.flush
  IO.println s!"{name}: clauses={f.length} maxVariable={maximum}"

def run (args : List String) : IO UInt32 := do
  let [dirString]:=args | throw (IO.userError "Usage: lean --run Emit.lean FRESH_OUTPUT_DIRECTORY")
  let dir:=System.FilePath.mk dirString
  if ←dir.pathExists then throw (IO.userError "Output directory must not already exist")
  IO.FS.createDir dir
  let m4:=DNativeMaps.fourForward
  let m5:=DNativeMaps.fiveForward
  let owners : List (String × Types):=[
    ("UUU",⟨false,false,false⟩),("UUT",⟨false,false,true⟩),
    ("UTU",⟨false,true,false⟩),("UTT",⟨false,true,true⟩),
    ("TTU",⟨true,true,false⟩),("TTT",⟨true,true,true⟩)]
  for (name,t) in owners do
    emit dir (name++"_four") (cachedFour m4 t)
    emit dir (name++"_five") (cachedFive m5 t)
  return 0
end PortableDNativePrefixes

def main := PortableDNativePrefixes.run
