import UniformK61.CommonCover
import UniformK61.CommonUnitCache

set_option autoImplicit false
namespace UniformK61.EmitCommon
open PricingABD.ABLayout CompletionC.NativeMatrices CompletionC.CommonCases
open PricingIntegration.PairAdmission

def familyText : Profile → String | .A => "A" | .B => "B" | .D => "D"
def ownerText (t : Types) : String :=
  (if t.left then "T" else "U") ++ (if t.right then "T" else "U") ++ (if t.marked then "T" else "U")
def literalText (x : Ramsey61.DenseCounter.Literal) : String :=
  (if x.1 then "" else "-") ++ toString x.2

def emit (dir : System.FilePath) : IO Unit := do
  let mut total := 0
  for p in List.finRange 737 do
    let r := retained p
    let tab := pairTable p
    let profile := if r.family==0 then Profile.A else if r.family==1 then Profile.B else Profile.D
    let l : Layout := ⟨profile,tab.shape.free==5⟩
    let coords := CommonUnitCache.coordinates l p
    let tail := CommonFormula.membership l p
    for left in [false,true] do
      for right in [false,true] do
        for marked in [false,true] do
          let t : Types := ⟨left,right,marked⟩
          if h : Admitted l t p then
            let name := toString p.val ++ "_" ++ ownerText t ++ ".tsv"
            let hfile ← IO.FS.Handle.mk (dir/name) IO.FS.Mode.write
            hfile.putStrLn ("PAIR\t" ++ toString p.val ++ "\t" ++ familyText profile ++ "\t" ++ ownerText t ++ "\t" ++
              toString r.leftKind ++ "\t" ++ toString r.rightKind ++ "\t" ++ toString r.stage ++ "\t" ++ toString tab.count)
            let head := CommonUnitCache.initial l t
            for j in List.finRange tab.count do
              let k : CommonCover.Case := ⟨l,t,⟨p,h⟩,j⟩
              let units := CommonUnitCache.cached k.1 tab.shape head tail coords (tab.representative k.2.2.2)
              hfile.putStrLn ("LEAF\t" ++ toString j.val ++ "\t" ++
                String.intercalate "," (units.map fun u => literalText (Core.unitLiteral u)))
              total := total+1
            hfile.flush
    if p.val%100==0 then IO.println ("PAIR " ++ toString p.val)
  IO.println ("COMPLETE " ++ toString total)
end UniformK61.EmitCommon

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "expected one fresh output directory")
  let dir := System.FilePath.mk destination
  if ←dir.pathExists then throw (IO.userError "refusing an existing output directory")
  IO.FS.createDir dir
  UniformK61.EmitCommon.emit dir
