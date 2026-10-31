import UniformK60.CEntranceBridgeDataDefs
import UniformK60.CEntranceSourceSoundness

set_option autoImplicit false
namespace UniformK60.CEntranceBridge
open Ramsey61 UniformK60.Physical UniformK60.CEntranceSource

/-- A checked finite transport carries every exact frozen target fact by
one actual60 bijection and one global color permutation. -/
theorem valid_satisfiable (e : Entry) (valid : Valid e) (c : Host)
    (w : SourceWitness e.mode e.pair (rep e) c) :
    ∃ k : CEntranceFormula.Case,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (CEntranceFormula.formula k) := by
  let π := vertexEquiv e valid
  let σ := colorMap e
  let d := UnitTransport.transformed c π σ
  have good : NoMonochromaticTriangle d := UnitTransport.transformed_good c w.good π σ
  have hunits : Core.UnitsMatch d (targetUnits e) := by
    intro u hu
    have hf := List.all_eq_true.mp valid.2.2.2.2 u hu
    have hs := sourceFact_matches w (pullUnit e u) hf
    apply UnitTransport.related_matches c π σ u (pullUnit e u) hs
    exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩
  have hsat := Core.coloring_satisfies_formula d good (targetUnits e) hunits
  by_cases hm : e.mode=2
  · have hlegal : CEntranceFormula.c2Allowed e.target e.omission := by
      simpa only [TargetLegal,if_pos hm] using valid.2.2.1
    let k : CEntranceFormula.C2Case := ⟨e.target,⟨e.omission,hlegal⟩⟩
    exact ⟨.inr k,Core.physicalValuation d,hsat⟩
  · have ho : e.omission=CEntranceFormula.c1Omission (e.target,decide (e.mode=1)) := by
      simpa only [TargetLegal,if_neg hm] using valid.2.2.1
    refine ⟨.inl (e.target,decide (e.mode=1)),Core.physicalValuation d,?_⟩
    change DenseCounter.FormulaSat (Core.physicalValuation d)
      (Core.formula (UnitRestriction.restrictUnits
        (CEntranceFormula.c1Omission (e.target,decide (e.mode=1)))
        (CEntranceFormula.referenceUnits e.target)))
    rw [←ho]
    exact hsat

#print axioms valid_satisfiable
end UniformK60.CEntranceBridge
