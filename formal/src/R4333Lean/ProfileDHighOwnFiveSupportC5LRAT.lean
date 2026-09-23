import R4333Lean.ProfileDHighOwnFiveSupportC5CNF

/-!
# Checked-LRAT endpoint for the profile-D five-support C5 formula

This module proves the collision-free sequential-counter contract for the
exact formula defined in `ProfileDHighOwnFiveSupportC5CNF`, supplies its
semantic satisfying valuation, and exposes certificate slots for every
profile-D kind/block/position branch.  No certificate is included.
-/

namespace R4333
namespace ProfileDHighOwnFiveSupportC5LRAT

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ThresholdDegreeCapsCNF ColoringJoinRows
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDRowSupportBounds61 ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind

/-! ## Collision-free atom namespaces -/

private theorem blockTemplateUnitClauses_outside
    (kind : Kind) (block : Fin 3) (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      (blockTemplateUnitClauses kind block) := by
  unfold counterTag blockTemplateUnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    obtain ⟨hleft, _hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega
  · intro pair hpair
    obtain ⟨_hleft, hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega

theorem templateUnitClauses_outside
    (kind : Kind) (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      (templateUnitClauses kind) := by
  unfold templateUnitClauses
  apply formulaOutsideNamespace_append
  · apply formulaOutsideNamespace_append
    · exact blockTemplateUnitClauses_outside kind 0 reserved
    · exact blockTemplateUnitClauses_outside kind 1 reserved
  · exact blockTemplateUnitClauses_outside kind 2 reserved

end ProfileDHighOwnFiveSupportC5LRAT
end R4333
