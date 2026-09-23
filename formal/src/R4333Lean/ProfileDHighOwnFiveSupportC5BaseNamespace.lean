import R4333Lean.ProfileDHighOwnFiveSupportC5LRAT

namespace R4333
namespace ProfileDHighOwnFiveSupportC5BaseNamespace

open FiniteColorCNF SequentialAtMostCNF
open ThresholdDegreeCapsCNF
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5LRAT

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind

theorem insideRootForbiddenUnitClauses_outside
    (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      insideRootForbiddenUnitClauses := by
  unfold counterTag insideRootForbiddenUnitClauses
  apply negativeEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).1.trans (by omega)
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).2.1.trans (by omega)

theorem allFiveOwnUnitClauses_outside
    (block : Fin 3) (position : Fin (blockSize block))
    (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      (allFiveOwnUnitClauses block position) := by
  unfold counterTag allFiveOwnUnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro a _ha
    exact a.isLt.trans (by omega)
  · intro _a _ha
    have hselected : (blockVertex block position.val).val < 46 :=
      (blockVertex block position.val).isLt
    omega

theorem insideC5UnitClauses_outside
    (block : Fin 3) (reserved : CounterContext) :
    FormulaOutsideNamespace (counterTag reserved)
      (insideC5UnitClauses block) := by
  unfold counterTag insideC5UnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).1.trans (by omega)
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).2.1.trans (by omega)

end ProfileDHighOwnFiveSupportC5BaseNamespace
end R4333
