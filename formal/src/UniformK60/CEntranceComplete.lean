import UniformK60.CEntranceBlocks
import UniformK60.CEntranceWordCover
import UniformK60.CEntranceFiniteCover

/-! Closed actual-host coverage of the frozen692 C1 and7840 C2 formulas.
Only the final finite formula UNSAT results remain an external boundary. -/
set_option autoImplicit false
namespace UniformK60.CEntranceComplete
open Ramsey61 UniformK60.Physical

/-- Every ordinary entrance at either C profile satisfies an exact retained
formula, with no restriction on the root's total incoming tickets. -/
theorem ordinary_entrance_cover (c : Host) (hc : NoMonochromaticTriangle c)
    (entrance : CEntranceWitness c) :
    ∃ k : CEntranceFormula.Case,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (CEntranceFormula.formula k) := by
  obtain ⟨σ,root,mark,mode,good,hd,five,types,b,owner,hroot,_⟩ :=
    CEntranceBlocks.actual_blocks_of_entrance c hc entrance
  have hdegree : ∀ q : Color,
      colorDegree (HostNormalization.relabel c (Equiv.refl _) σ) (palette q) b.root=
        CEntranceLayout.shape mode q := by
    intro q;rw [hroot];exact hd q
  obtain ⟨p,j,hp,d,w⟩ := CEntranceWordCover.actual_source b good hdegree owner
  exact CEntranceFiniteCover.source_satisfiable mode p j hp d w

/-- Preserve the selector's eligible-witness interface. -/
theorem actual_entrance_cover (c : Host) (hc : NoMonochromaticTriangle c)
    (exterior : CExteriorWitness c) :
    ∃ k : CEntranceFormula.Case,∃ v : DenseCounter.Valuation,
      DenseCounter.FormulaSat v (CEntranceFormula.formula k) :=
  ordinary_entrance_cover c hc (exterior_is_entrance c exterior)

/-- The exact finite boundary excludes all entrances as defined in the paper. -/
theorem no_entrance_of_all_unsat
    (unsat : ∀ k : CEntranceFormula.Case,∀ v : DenseCounter.Valuation,
      ¬DenseCounter.FormulaSat v (CEntranceFormula.formula k))
    (c : Host) (hc : NoMonochromaticTriangle c) : ¬CEntranceWitness c := by
  intro h
  obtain ⟨k,v,hv⟩ := ordinary_entrance_cover c hc h
  exact unsat k v hv

/-- The selector's eligible entrances are excluded as a special case. -/
theorem no_exterior_of_all_unsat
    (unsat : ∀ k : CEntranceFormula.Case,∀ v : DenseCounter.Valuation,
      ¬DenseCounter.FormulaSat v (CEntranceFormula.formula k))
    (c : Host) (hc : NoMonochromaticTriangle c) : ¬CExteriorWitness c := by
  intro h
  exact no_entrance_of_all_unsat unsat c hc (exterior_is_entrance c h)

#print axioms ordinary_entrance_cover
#print axioms no_entrance_of_all_unsat
#print axioms actual_entrance_cover
#print axioms no_exterior_of_all_unsat
end UniformK60.CEntranceComplete
