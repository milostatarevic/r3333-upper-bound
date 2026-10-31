import UniformK60.UUSourceSoundness
import UniformK61.UUChecks
import UniformK61.UUFiniteBridge

set_option autoImplicit false
namespace UniformK60.UUFiniteBridge
open Ramsey61 UniformK61.Core UniformK61.UUSupportData UniformK61.UUSourceDefs
open UniformK61.UUBridgeData UniformK60.UUSourceFacts UniformK60.UUSourceSoundness

/-- The published finite transport applies to reference facts alone.
It needs no triangle-free coloring on the omitted reference position. -/
theorem transported_units {q : Bool} {p : Pair} {i : Fin 600}
    {c : UnitRestriction.ReferenceColoring} (w : SourceFacts q p i c) :
    UniformK61.Core.UnitsMatch
      (UniformK61.UnitTransport.transformed c (vertices q (action p i)) (colors (action p i)))
      (UniformK61.MarkedUU.caseUnits q (UniformK61.UUData.leaf (target p i))) := by
  let a := action p i
  let j := UniformK61.UUData.leaf (target p i)
  have h := UniformK61.UUChecks.residual_all q p i
  intro u hu
  have he : UniformK61.MarkedUU.caseUnits q j =
      ((List.finRange 60).map UniformK61.MarkedUU.spoke ++ UniformK61.MarkedUU.templateUnits q) ++
        residualUnits j := by
    simp only [UniformK61.MarkedUU.caseUnits, residualUnits, List.append_assoc]
  rw [he] at hu
  rcases List.mem_append.mp hu with hu | hu
  · rcases List.mem_append.mp hu with hu | hu
    · exact UniformK61.UUTemplateTransport.spokes_match
        (UniformK61.UUTemplateTransport.static_transport w.toStaticHost a) u hu
    · exact UniformK61.UUTemplateTransport.templates_match
        (UniformK61.UUTemplateTransport.static_transport w.toStaticHost a) u hu
  · have hf : sourceFact q p i (pulledUnit q a u) = true := List.all_eq_true.mp h u hu
    have hs := sourceFact_matches w (pulledUnit q a u) hf
    apply UniformK61.UnitTransport.related_matches c (vertices q a) (colors a) u (pulledUnit q a u) hs
    exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- A surviving physical K60 and the finite action give a fresh satisfying
assignment for the restricted target leaf, without reusing an UNSAT result. -/
theorem restricted_satisfiable {q : Bool} {p : Pair} {i : Fin 600}
    {c : UnitRestriction.ReferenceColoring} (w : SourceFacts q p i c)
    (source targetOmission : UnitRestriction.Omission)
    (hπ : vertices q (action p i) targetOmission.castSucc = source.castSucc)
    (hc : NoMonochromaticTriangle (UnitRestriction.restrictColoring c source)) :
    ∃ v : DenseCounter.Valuation, DenseCounter.FormulaSat v
      (UnitRestriction.formula targetOmission
        (ReferenceSource.units (UniformK61.MarkedUU.caseUnits q
          (UniformK61.UUData.leaf (target p i))))) := by
  let d := UniformK61.UnitTransport.transformed c (vertices q (action p i)) (colors (action p i))
  apply UnitRestriction.restriction_satisfiable d targetOmission _
  · exact ReferenceExtension.restriction_transformed_good c source targetOmission _ _ hπ hc
  · intro u hu _
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hu
    exact (ReferenceSource.reference_matches d old).mpr (transported_units w old hold)

#print axioms transported_units
#print axioms restricted_satisfiable
end UniformK60.UUFiniteBridge
