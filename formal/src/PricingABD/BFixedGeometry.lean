import PricingABD.BCommands
import PricingABD.TTExchange

namespace PricingABD.BFixedGeometry
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open PricingABD.BPhysicalBounds PricingABD.BPrimary

abbrev Edge := Fin 52 × Fin 52 × Fin 4
 def pairs (n : Nat) : List (Fin n × Fin n) :=
   (List.finRange n).flatMap fun u => ((List.finRange n).filter (fun v => u<v)).map (fun v => (u,v))
 def left (i : Fin 15) : Fin 52 := ⟨5+i.val,by omega⟩
 def right (i : Fin 16) : Fin 52 := ⟨20+i.val,by omega⟩
 def marked (i : Fin 16) : Fin 52 := ⟨36+i.val,by omega⟩
 def leftColor (q : Fin 3) : Fin 4 := ![0,2,3] q
 def rightColor (q : Fin 3) : Fin 4 := ![0,1,3] q
 def markedColor (q : Fin 3) : Fin 4 := ⟨q.val,by omega⟩
 def freeColor (u v : Fin 5) : Fin 4 := if v.val=u.val+1 ∨ (u.val=0 ∧ v.val=4) then 1 else 2
 def templateEdges : List Edge :=
   (pairs 15).map (fun p => (left p.1,left p.2,leftColor (R4333.k15Twisted p.1 p.2))) ++
   (pairs 16).map (fun p => (right p.1,right p.2,rightColor (R4333.k16Template true p.1 p.2))) ++
   (pairs 16).map (fun p => (marked p.1,marked p.2,markedColor (R4333.k16Template true p.1 p.2)))
 def freeEdges : List Edge := (pairs 5).map (fun p => (freeLabel p.1,freeLabel p.2,freeColor p.1 p.2))
 def markEdges : List Edge := (List.finRange 5).map (fun u => (51,freeLabel u,3))
 def fixedEdges : List Edge := templateEdges ++ freeEdges ++ markEdges
 theorem fixedEdges_length : fixedEdges.length=360 := by decide +kernel
 theorem fixedEdges_distinct : ∀e∈fixedEdges,e.1≠e.2.1 := by
  have h : fixedEdges.all (fun e => decide (e.1≠e.2.1))=true := by decide +kernel
  intro e he
  exact of_decide_eq_true ((List.all_eq_true.mp h) e he)

 /-- Entire specified critical templates, one physical free C5, and all five
 marked attachments. These are same-host color equations, not CNF assumptions. -/
 def FixedGeometry {c : Host} (f : Frame c) : Prop :=
   ∀e∈fixedEdges,c (f.vertex e.1) (f.vertex e.2.1)=palette e.2.2
 def units (es : List Edge) : CNF := es.map (fun e => [(true,B52Core.edgeVar e.1 e.2.1 e.2.2)])
 def forbidden : CNF := (pairs 5).map (fun p => [(false,B52Core.edgeVar (freeLabel p.1) (freeLabel p.2) 0)])
 def physicalBase : CNF := B52Core.physicalClauses ++ B52Core.triangleClauses ++ units templateEdges ++ forbidden ++ units freeEdges ++ units markEdges

 theorem fixed_unit_sat {c : Host} (f : Frame c) (hg : FixedGeometry f) (e : Edge) (he : e∈fixedEdges) :
    ClauseSat (primary f) [(true,B52Core.edgeVar e.1 e.2.1 e.2.2)] := by
  exact ⟨(true,B52Core.edgeVar e.1 e.2.1 e.2.2),by simp,(primary_edge f _ _ _ (fixedEdges_distinct _ he)).mpr (hg e he)⟩
 theorem fixed_known_value {c : Host} (f : Frame c) (hg : FixedGeometry f) (e : Edge) (he : e∈fixedEdges) (q : Fin 4) :
    primary f (B52Core.edgeVar e.1 e.2.1 q)=decide (q=e.2.2) := by
  apply Bool.eq_iff_iff.mpr
  rw [primary_edge f _ _ _ (fixedEdges_distinct _ he),decide_eq_true_eq,hg e he]
  exact ⟨fun h => (palette_injective h).symm,fun h => congrArg palette h.symm⟩

#print axioms fixed_known_value
end PricingABD.BFixedGeometry
