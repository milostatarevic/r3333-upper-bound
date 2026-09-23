import R4333Lean.ProfileDHighOwnFiveSupportC5CounterNamespace

namespace R4333
namespace ProfileDHighOwnFiveSupportC5AllCaps

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ProfileDTripleJoinReduction ProfileDRowSupportBounds61
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind

theorem allCaps_of_canonicalBranch
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    AllCaps (counterSpecs block position)
      (coloringValuation
        (totalColoring
          branch.toDegreeFlooredFiveExtension.toFiveExtension)) := by
  intro spec hspec
  have hspec' : spec ∈ counterSpecs block position := hspec
  simp only [counterSpecs, List.mem_map] at hspec'
  obtain ⟨context, _hcontext, rfl⟩ := hspec'
  unfold InputsAtMost counterSpec
  cases context with
  | row a q phase =>
      by_cases hphase : phase = upperPhase
      · simp only [contextInputs, contextBound, hphase, if_pos]
        rw [trueInputCount_rowColorAtoms]
        by_cases hq : q = 0
        · subst q
          simpa [supportUpperBound] using
            branch.toDegreeFlooredFiveExtension.zeroSupportUpper a
        · simpa [supportUpperBound, hq] using
            branch.toDegreeFlooredFiveExtension.nonzeroSupportUpper a q hq
      · simp only [contextInputs, contextBound, hphase, if_false]
        rw [trueInputCount_rowOtherColorAtoms]
        by_cases hq : q = 0
        · subst q
          have hlower :=
            branch.toDegreeFlooredFiveExtension.zeroSupportLower a
          simp only [complementaryUpperBound, if_pos]
          omega
        · have hlower :=
            branch.toDegreeFlooredFiveExtension.nonzeroSupportLower a q hq
          simp only [complementaryUpperBound, hq, if_false]
          omega
  | selectedTail phase =>
      by_cases hphase : phase = upperPhase
      · simp only [contextInputs, contextBound, hphase, if_pos]
        rw [trueInputCount_selectedTailColorAtoms]
        exact branch.tailOwnDegreeUpper
      · simp only [contextInputs, contextBound, hphase, if_false]
        rw [trueInputCount_selectedTailOtherColorAtoms]
        have hlower : 9 ≤ colorDegree
            branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
              (blockRootColor block) (selectedTailVertex block position) := by
          simpa [selectedTailVertex] using branch.tailOwnDegreeLower
        omega

end ProfileDHighOwnFiveSupportC5AllCaps
end R4333
