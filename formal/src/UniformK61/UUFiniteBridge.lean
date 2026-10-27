import UniformK61.UUBridgeData
import UniformK61.UUSourceSoundness
import UniformK61.UUTemplateTransport
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UniformK61.UUFiniteBridge
open Ramsey61 UniformK61.Core UniformK61.UUSupportData UniformK61.UUSourceDefs
open UniformK61.UUBridgeData UniformK61.UUSourceSoundness

/-- A successful finite check transports the complete actual host by a single
vertex permutation and a single global palette permutation. -/
theorem finite_bridge_sound_of_check {q : Bool} {p : Pair} {i : Fin 600} {c : Host}
 (w : SourceWitness q p i c) (h : checkEntry q p i=true) :
 ∃v : DenseCounter.Valuation,
 DenseCounter.FormulaSat v (MarkedUU.formula q (UUData.leaf (target p i))) := by
 let a:=action p i
 let π:=vertices q a
 let σ:=colors a
 let d:=UnitTransport.transformed c π σ
 have hd : NoMonochromaticTriangle d := UnitTransport.transformed_good c w.good π σ
 have hu : UnitsMatch d (MarkedUU.caseUnits q (UUData.leaf (target p i))) := by
  intro u hm
  have hf : sourceFact q p i (pulledUnit q a u)=true := List.all_eq_true.mp h u hm
  have hs := sourceFact_matches w (pulledUnit q a u) hf
  apply UnitTransport.related_matches c π σ u (pulledUnit q a u) hs
  exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩
 exact ⟨physicalValuation d,coloring_satisfies_formula d hd _ hu⟩

/-- The static template and root clauses are transported once mathematically;
the checked residual contains the case-specific matrix and signed memberships. -/
theorem finite_bridge_sound_of_residual {q : Bool} {p : Pair} {i : Fin 600} {c : Host}
 (w : SourceWitness q p i c) (h : checkResidual q p i=true) :
 ∃v : DenseCounter.Valuation,
 DenseCounter.FormulaSat v (MarkedUU.formula q (UUData.leaf (target p i))) := by
 let a:=action p i
 let π:=vertices q a
 let σ:=colors a
 let d:=UnitTransport.transformed c π σ
 let j:=UUData.leaf (target p i)
 have hd : NoMonochromaticTriangle d := UnitTransport.transformed_good c w.good π σ
 have hstatic:=UUTemplateTransport.static_units_match w a
 have hu : UnitsMatch d (MarkedUU.caseUnits q j) := by
  intro u hm
  have he : MarkedUU.caseUnits q j=
    ((List.finRange 60).map MarkedUU.spoke ++ MarkedUU.templateUnits q) ++ residualUnits j := by
   simp only[MarkedUU.caseUnits,residualUnits,List.append_assoc]
  rw[he] at hm
  rcases List.mem_append.mp hm with hm|hm
  · exact hstatic u hm
  · have hf : sourceFact q p i (pulledUnit q a u)=true := List.all_eq_true.mp h u hm
    have hs := sourceFact_matches w (pulledUnit q a u) hf
    apply UnitTransport.related_matches c π σ u (pulledUnit q a u) hs
    exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩
 exact ⟨physicalValuation d,coloring_satisfies_formula d hd _ hu⟩

#print axioms finite_bridge_sound_of_check
#print axioms finite_bridge_sound_of_residual
end UniformK61.UUFiniteBridge
