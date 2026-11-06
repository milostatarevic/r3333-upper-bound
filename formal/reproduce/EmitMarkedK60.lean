import UniformK60.EFormula
import UniformK60.CEntranceFormula
import UniformK61.CommonUnitCache

/-! Complete signed-unit emission. Common reference caching is justified by
UniformK61.CommonUnitCache.cached_eq; restriction and signed sorting are the
actual K60 formula constructors. The complete layout/type lists have the
published layouts_complete/types_complete proofs. No SAT solver is invoked. -/
set_option autoImplicit false
namespace UniformK60.EmitMarkedK60
open PricingABD.ABLayout CompletionC.NativeMatrices CompletionC.CommonCases
open PricingIntegration.PairAdmission

def ownerText (t : Types) : String :=
  (if t.left then "T" else "U") ++ (if t.right then "T" else "U") ++
    (if t.marked then "T" else "U")

def familyText : Profile → String | .A => "A" | .B => "B" | .D => "D"

def emitUnits (out : IO.FS.Handle) (owner key : String)
    (us : List Core.PhysicalUnit) : IO Unit :=
  out.putStrLn (owner ++ "\t" ++ key ++ "\t" ++
    String.intercalate "," (us.map (fun u => toString (UnitRestriction.signedLiteral u))))

def emitCommon (abd eout : IO.FS.Handle) : IO (Nat × Nat) := do
  let mut na := 0
  let mut ne := 0
  for l in CompletionC.CommonCaseCount.layouts do
    for t in CompletionC.CommonCaseCount.types do
      for p in List.finRange 737 do
        if _h : Admitted l t p then
          let tab := pairTable p
          let coords := UniformK61.CommonUnitCache.coordinates l p
          let tail := UniformK61.CommonFormula.membership l p
          let head := UniformK61.CommonUnitCache.initial l t
          let family := familyText l.profile
          let owner := if l.profile == .D then "D_" ++ ownerText t else family
          for j in List.finRange tab.count do
            let reference := ReferenceSource.units
              (UniformK61.CommonUnitCache.cached l tab.shape head tail coords (tab.representative j))
            let key := ownerText t ++ ":" ++ toString p.val ++ ":" ++ toString j.val
            emitUnits abd owner key (UnitRestriction.sortedRestriction (ABDFormula.commonOmission l) reference)
            na := na + 1
            if l.profile == .D && t.marked then
              for d in List.finRange 9 do
                emitUnits eout ("E_" ++ ownerText t) (key ++ ":" ++ toString d.val)
                  (UnitRestriction.sortedRestriction (EFormula.omission true d) reference)
                ne := ne + 1
  return (na,ne)

def emitUU (abd eout : IO.FS.Handle) : IO (Nat × Nat) := do
  let mut na := 0
  let mut ne := 0
  for q in [false,true] do
    let owner := if q then "UUT" else "UUU"
    for i in List.finRange 679 do
      let reference := ReferenceSource.units (UniformK61.MarkedUU.caseUnits q i)
      emitUnits abd ("D_" ++ owner) (toString i.val)
        (UnitRestriction.sortedRestriction 14 reference)
      na := na + 1
      for d in List.finRange (EFormula.omissionCount q) do
        emitUnits eout ("E_" ++ owner) (toString i.val ++ ":" ++ toString d.val)
          (UnitRestriction.sortedRestriction (EFormula.omission q d) reference)
        ne := ne + 1
  return (na,ne)

def emitEntrances (out : IO.FS.Handle) : IO Nat := do
  let mut count := 0
  for k in List.finRange 346 do
    for flag in [false,true] do
      emitUnits out "C1_ENTRANCE" (toString k.val ++ ":" ++ toString flag)
        (CEntranceFormula.c1Units (k,flag))
      count := count + 1
    for d in List.finRange 60 do
      if h : CEntranceFormula.c2Allowed k d then
        emitUnits out "C2_ENTRANCE" (toString k.val ++ ":" ++ toString d.val)
          (CEntranceFormula.c2Units ⟨k,⟨d,h⟩⟩)
        count := count + 1
  return count

end UniformK60.EmitMarkedK60

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "expected one fresh output directory")
  let dir := System.FilePath.mk destination
  if ← dir.pathExists then throw (IO.userError "refusing an existing output directory")
  IO.FS.createDir dir
  let abd ← IO.FS.Handle.mk (dir/"abd.tsv") .write
  let eout ← IO.FS.Handle.mk (dir/"e.tsv") .write
  let ent ← IO.FS.Handle.mk (dir/"entrances.tsv") .write
  let (a1,e1) ← UniformK60.EmitMarkedK60.emitCommon abd eout
  let (a2,e2) ← UniformK60.EmitMarkedK60.emitUU abd eout
  let nc ← UniformK60.EmitMarkedK60.emitEntrances ent
  abd.flush; eout.flush; ent.flush
  IO.println ("COMPLETE ABD=" ++ toString (a1+a2) ++ " E=" ++ toString (e1+e2) ++
    " entrances=" ++ toString nc)
