import PricingABD.CommonSuffixCache
set_option autoImplicit false

namespace PortableCommon
open Ramsey61.DenseCounter PricingABD.ABLayout PricingIntegration.PairAdmission
open CompletionC.NativeMatrices CompletionC.NativeSupportIndex CompletionC.NativeFamilyJoin
open PricingABD.CommonSuffixCache

instance (l:Layout) (t:Types) (p:Fin 737) : Decidable (Admitted l t p) := by
 unfold Admitted NativeOwner Compatible
 cases l.profile <;> infer_instance

def ownerText (t:Types) : String :=
 (if t.left then "T" else "U")++(if t.right then "T" else "U")++(if t.marked then "T" else "U")
def familyText : Profile → String | .A=>"A" | .B=>"B" | .D=>"D"
def literalText (x:Literal) : String := (if x.1 then "" else "-")++toString x.2
def aOwners : List Types :=
 [⟨false,false,false⟩,⟨false,false,true⟩,⟨false,true,true⟩,⟨true,true,true⟩]
def bOwners : List Types :=
 [⟨false,false,false⟩,⟨false,false,true⟩,⟨false,true,true⟩,
  ⟨true,false,false⟩,⟨true,false,true⟩,⟨true,true,true⟩]

def emitPrefix (dir:System.FilePath) (l:Layout) (t:Types) : IO Unit := do
 let key := familyText l.profile++"_"++ownerText t++"_"++toString (freeSize l)
 let path := dir/(key++".body")
 if ←path.pathExists then throw (IO.userError "refusing to overwrite prefix")
 let h ←IO.FS.Handle.mk path IO.FS.Mode.write
 for clause in PricingABD.ABNative.exactPrefix l t do
  h.putStrLn (String.intercalate " " (clause.map literalText)++" 0")
 h.flush
 IO.println ("PREFIX "++key)

def emitSuffixes (dir:System.FilePath) : IO Unit := do
 let path := dir/"COMMON_SUFFIXES.tsv"
 if ←path.pathExists then throw (IO.userError "refusing to overwrite suffixes")
 let h ←IO.FS.Handle.mk path IO.FS.Mode.write
 for p in List.finRange 737 do
  let r := retained p
  let tab := pairTable p
  let profile := if r.family==0 then Profile.A else if r.family==1 then Profile.B else Profile.D
  let l : Layout := ⟨profile,tab.shape.free==5⟩
  let headUnits := initial l p
  let coords := coordinates l p
  let n := vertexCount l
  h.putStrLn ("PAIR\t"++toString p.val++"\t"++familyText profile++"\t"++toString r.leftKind++"\t"++toString r.rightKind++"\t"++toString r.stage++"\t"++toString tab.count)
  for left in [false,true] do
   for right in [false,true] do
    for marked in [false,true] do
     let t : Types := ⟨left,right,marked⟩
     if decide (Admitted l t p) then
      h.putStrLn ("ADMIT\t"++toString p.val++"\t"++familyText profile++"\t"++ownerText t++"\t"++toString (freeSize l)++"\t"++toString tab.count)
  for j in List.finRange tab.count do
   let word := tab.representative j
   let units := cached n tab.shape headUnits coords word
   h.putStrLn ("LEAF\t"++toString p.val++"\t"++toString j.val++"\t"++toString word++"\t"++String.intercalate "," (units.map literalText))
  if p.val%50==0 then IO.println ("PAIR "++toString p.val)
 h.flush
 IO.println "COMPLETE 737"
end PortableCommon

/-- Runtime-only emission. No output is produced by compiling this source. -/
def main (args:List String) : IO Unit := do
 let [destination] := args | throw (IO.userError "expected one fresh output directory")
 let dir := System.FilePath.mk destination
 if ←dir.pathExists then throw (IO.userError "refusing an existing output directory")
 IO.FS.createDir dir
 IO.FS.createDir (dir/"prefixes")
 for five in [false,true] do
  for t in PortableCommon.aOwners do PortableCommon.emitPrefix (dir/"prefixes") ⟨.A,five⟩ t
  for t in PortableCommon.bOwners do PortableCommon.emitPrefix (dir/"prefixes") ⟨.B,five⟩ t
 PortableCommon.emitSuffixes dir
