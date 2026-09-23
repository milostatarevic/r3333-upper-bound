import R4333Lean.ProfileDHighOwnFiveSupportC5FullBaseNamespace

namespace R4333
namespace ProfileDHighOwnFiveSupportC5CounterNamespace

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5FullBaseNamespace

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind

theorem rowColorAtoms_outside_counterNamespace
    (reserved : CounterContext) (a : FiveVertex) (q : Fin 4) :
    InputsOutsideNamespace (counterTag reserved) (rowColorAtoms a q) := by
  intro atom hatom
  simp only [rowColorAtoms, List.mem_map] at hatom
  obtain ⟨x, _hx, rfl⟩ := hatom
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    (namespaceVertex reserved) (namespaceColor reserved) (by omega) (by omega)

theorem rowOtherColorAtoms_outside_counterNamespace
    (reserved : CounterContext) (a : FiveVertex) (q : Fin 4) :
    InputsOutsideNamespace (counterTag reserved)
      (rowOtherColorAtoms a q) := by
  intro atom hatom
  simp only [rowOtherColorAtoms, List.mem_flatMap] at hatom
  obtain ⟨r, _hr, hatom⟩ := hatom
  exact rowColorAtoms_outside_counterNamespace reserved a r atom hatom

theorem selectedTailColorAtoms_outside_counterNamespace
    (reserved : CounterContext) (block : Fin 3)
    (position : Fin (blockSize block)) (q : Fin 4) :
    InputsOutsideNamespace (counterTag reserved)
      (selectedTailColorAtoms block position q) := by
  intro atom hatom
  simp only [selectedTailColorAtoms, List.mem_map] at hatom
  obtain ⟨y, _hy, rfl⟩ := hatom
  unfold counterTag OutsideDegreeCapCNF.outsideIncidentEdgeAtom
  apply OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
  · exact lt_of_le_of_lt
      (Nat.min_le_left
        (tailVertex (selectedTailVertex block position)).val
        (tailVertex y).val)
      ((tailVertex (selectedTailVertex block position)).isLt.trans (by omega))
  · exact max_lt
      ((tailVertex (selectedTailVertex block position)).isLt.trans (by omega))
      ((tailVertex y).isLt.trans (by omega))

theorem selectedTailOtherColorAtoms_outside_counterNamespace
    (reserved : CounterContext) (block : Fin 3)
    (position : Fin (blockSize block)) :
    InputsOutsideNamespace (counterTag reserved)
      (selectedTailOtherColorAtoms block position) := by
  intro atom hatom
  simp only [selectedTailOtherColorAtoms, List.mem_flatMap] at hatom
  obtain ⟨q, _hq, hatom⟩ := hatom
  exact selectedTailColorAtoms_outside_counterNamespace
    reserved block position q atom hatom

theorem contextInputs_outside_counterNamespace
    (reserved target : CounterContext) (block : Fin 3)
    (position : Fin (blockSize block)) :
    InputsOutsideNamespace (counterTag reserved)
      (contextInputs block position target) := by
  cases target with
  | row a q phase =>
      by_cases hphase : phase = upperPhase
      · simp only [contextInputs, hphase, if_pos]
        exact rowColorAtoms_outside_counterNamespace reserved a q
      · simp only [contextInputs, hphase]
        exact rowOtherColorAtoms_outside_counterNamespace reserved a q
  | selectedTail phase =>
      by_cases hphase : phase = upperPhase
      · simp only [contextInputs, hphase, if_pos]
        exact selectedTailColorAtoms_outside_counterNamespace
          reserved block position (blockRootColor block)
      · simp only [contextInputs, hphase]
        exact selectedTailOtherColorAtoms_outside_counterNamespace
          reserved block position

theorem counterSpecs_wellFormed
    (kind : Kind) (block : Fin 3) (position : Fin (blockSize block)) :
    ManyCounterWellFormed (baseFmla kind block position)
      (counterSpecs block position) := by
  refine ⟨counterSpecs_tags_nodup block position, ?_, ?_⟩
  · intro reserved hreserved
    have hreserved' : reserved ∈ counterSpecs block position := hreserved
    simp only [counterSpecs, List.mem_map] at hreserved'
    obtain ⟨context, _hcontext, rfl⟩ := hreserved'
    exact baseFmla_outside_counterNamespace kind block position context
  · intro reserved hreserved target htarget
    have hreserved' : reserved ∈ counterSpecs block position := hreserved
    have htarget' : target ∈ counterSpecs block position := htarget
    simp only [counterSpecs, List.mem_map] at hreserved' htarget'
    obtain ⟨reservedContext, _hr, rfl⟩ := hreserved'
    obtain ⟨targetContext, _ht, rfl⟩ := htarget'
    exact contextInputs_outside_counterNamespace
      reservedContext targetContext block position

end ProfileDHighOwnFiveSupportC5CounterNamespace
end R4333
