import UniformK61.Core
import UniformK61.UUData
import PricingABD.ABGeometry

/-! The two profile-D families with foreign U15 templates each have 679
physical cases. Every formula uses the complete K61 base and records all
positive and negative marked-neighborhood membership facts. -/
set_option autoImplicit false
namespace UniformK61.MarkedUU
open UniformK61.Core
open R4333
abbrev Leaf := UUData.Leaf
abbrev freeSize := UUData.freeSize

def digit (code i : Nat) : Color := ⟨code / 4^i % 4,Nat.mod_lt _ (by decide)⟩
def vertex (n : Nat) : Vertex := ⟨n%61,Nat.mod_lt _ (by decide)⟩
def freeUnits (i : Leaf) : List PhysicalUnit :=
 (R4333.FiniteColorCNF.edges (freeSize i)).zipIdx |>.map fun ((a,b),j)=>
  ⟨true,vertex (a+1),vertex (b+1),digit (UUData.facts i).freeCode j⟩

def leftSupport (i : Leaf) : List Nat := (List.range 15).filter ((UUData.facts i).leftMask.testBit)
def rightSupport (i : Leaf) : List Nat := (List.range 15).filter ((UUData.facts i).rightMask.testBit)
def crossPairs (i : Leaf) : List (Nat×Nat) :=
 (((List.range (freeSize i)).flatMap fun a=>
   (leftSupport i).map (fun b=>(a+1,b+15)) ++ (rightSupport i).map (fun b=>(a+1,b+30))) ++
  ((leftSupport i).flatMap fun a=>(rightSupport i).map fun b=>(a+15,b+30)))

def crossUnits (i : Leaf) : List PhysicalUnit :=
 (crossPairs i).zipIdx.map fun ((a,b),j)=>⟨true,vertex a,vertex b,digit (UUData.facts i).crossCode j⟩

def markedMember (i : Leaf) (v : Nat) : Bool :=
 if v=0 then true else if v≤freeSize i then true else
 if v<15 ∨ 45≤v then false else
 if v<30 then (UUData.facts i).leftMask.testBit (v-15)
 else (UUData.facts i).rightMask.testBit (v-30)

def spoke (v : Fin 60) : PhysicalUnit :=
 let a:=v.val+1
 ⟨true,0,⟨a,by omega⟩,if a≤14 then 0 else if a≤29 then 1 else if a≤44 then 2 else 3⟩

/-- Literal color in a critical template, totalized outside its vertex range. -/
def templateColor (size : Nat) (twisted : Bool) (a b : Nat) : Fin 3 :=
 if size = 15 then
  R4333.k15Template twisted ⟨a % 15,Nat.mod_lt _ (by decide)⟩ ⟨b % 15,Nat.mod_lt _ (by decide)⟩
 else
  R4333.k16Template twisted ⟨a % 16,Nat.mod_lt _ (by decide)⟩ ⟨b % 16,Nat.mod_lt _ (by decide)⟩

def templateUnits (twisted : Bool) : List PhysicalUnit :=
 ((List.finRange 3).flatMap fun block=>
  let order:=if block=2 then 16 else 15
  let start:=15+15*block.val
  (R4333.FiniteColorCNF.edges order).map fun (a,b)=>
   let q:=templateColor order (if block=2 then twisted else false) a b
   ⟨true,⟨(start+a)%61,Nat.mod_lt _ (by decide)⟩,
    ⟨(start+b)%61,Nat.mod_lt _ (by decide)⟩,
    PricingABD.ABGeometry.foreign (block.succ) q⟩)

def membershipUnits (i : Leaf) : List PhysicalUnit :=
 (List.finRange 59).map fun z=>
  let v:=z.val+1
  ⟨markedMember i v,⟨v,by omega⟩,60,3⟩

def caseUnits (twisted : Bool) (i : Leaf) : List PhysicalUnit :=
 (List.finRange 60).map spoke ++ templateUnits twisted ++
 freeUnits i ++
 crossUnits i ++ membershipUnits i

def formula (twisted : Bool) (i : Leaf) : Ramsey61.DenseCounter.CNF :=
 Core.formula (caseUnits twisted i)

/-- The case facts hold in one actual full-host coloring. -/
theorem physical_satisfies (twisted : Bool) (i : Leaf) (c : Coloring)
 (hc : Ramsey61.NoMonochromaticTriangle c) (h : UnitsMatch c (caseUnits twisted i)) :
 Ramsey61.DenseCounter.FormulaSat (physicalValuation c) (formula twisted i) :=
 Core.coloring_satisfies_formula c hc _ h

#print axioms physical_satisfies
end UniformK61.MarkedUU
