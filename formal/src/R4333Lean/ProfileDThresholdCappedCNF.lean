import R4333Lean.ThresholdDegreeCapsCNF
import R4333Lean.ProfileDFourRowDegreeCap

/-!
# Degree-strengthened profile-D threshold formulas

The exact four-row profile-D formula receives either 50 own-root
degree-fifteen counters or all 200 threshold counters.  The omitted-root
degree facts come from `ProfileDFourRowDegreeCap`; this file proves the exact
SAT namespace and checked-refutation boundary.  No certificate is asserted.
-/

namespace R4333
namespace ProfileDThresholdCappedCNF

open FiniteColorCNF SequentialAtMostCNF
open ThresholdDegreeCapsCNF
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDFourRowCNF
open ProfileDFourRowDegreeCap

set_option maxRecDepth 1000000

private theorem blockTemplateUnitClauses_outside
    (kind : Kind) (block : Fin 3) (reservedX : Fin 50)
    (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (blockTemplateUnitClauses kind block) := by
  unfold blockTemplateUnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    obtain ⟨hleft, _hright, _hlr⟩ := mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega
  · intro pair hpair
    obtain ⟨_hleft, hright, _hlr⟩ := mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega

private theorem templateUnitClauses_outside
    (kind : Kind) (reservedX : Fin 50) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (templateUnitClauses kind) := by
  unfold templateUnitClauses
  apply formulaOutsideNamespace_append
  · apply formulaOutsideNamespace_append
    · exact blockTemplateUnitClauses_outside kind 0 reservedX reservedQ
    · exact blockTemplateUnitClauses_outside kind 1 reservedX reservedQ
  · exact blockTemplateUnitClauses_outside kind 2 reservedX reservedQ

private theorem insideRootForbiddenUnitClauses_outside
    (reservedX : Fin 50) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      insideRootForbiddenUnitClauses := by
  unfold insideRootForbiddenUnitClauses
  apply negativeEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    exact (mem_edges_bounds hpair).1.trans (by omega)
  · intro pair hpair
    exact (mem_edges_bounds hpair).2.1.trans (by omega)

theorem fmla_outside_counterNamespace (kind : Kind)
    (reservedX : Fin 50) (reservedQ : Fin 4) :
    FormulaOutsideNamespace
      (OutsideDegreeCapCNF.outsideDegreeCounterTag reservedX reservedQ)
      (ProfileDFourRowCNF.fmla kind) := by
  unfold ProfileDFourRowCNF.fmla
  apply formulaOutsideNamespace_append
  · apply formulaOutsideNamespace_append
    · exact OutsideDegreeCapCNF.goodColoringFmla_outside_counterNamespace
        reservedX reservedQ
    · exact templateUnitClauses_outside kind reservedX reservedQ
  · exact insideRootForbiddenUnitClauses_outside reservedX reservedQ

def ownCappedFmla (kind : Kind) : Sat.Fmla :=
  withOwnDegreeCapsFmla (ProfileDFourRowCNF.fmla kind) totalRootColor

def allCappedFmla (kind : Kind) : Sat.Fmla :=
  withAllDegreeCapsFmla (ProfileDFourRowCNF.fmla kind) totalRootColor

theorem ownCounterCount :
    (ownDegreeCounterSpecs totalRootColor).length = 50 :=
  ownDegreeCounterSpecs_length totalRootColor

theorem allCounterCount :
    (allDegreeCounterSpecs totalRootColor).length = 200 := by
  simpa using allDegreeCounterSpecs_length totalRootColor

theorem fourExtension_satisfies_ownCappedFmla {kind : Kind}
    (ext : FourExtension kind) :
    (SequentialAtMostManyCNF.iteratedSequentialExtension
      (ownDegreeCounterSpecs totalRootColor)
      (coloringValuation (totalColoring ext))).satisfies_fmla
        (ownCappedFmla kind) := by
  exact coloring_satisfies_withOwnDegreeCapsFmla
    (ProfileDFourRowCNF.fmla kind) totalRootColor (totalColoring ext)
    (fun x => fmla_outside_counterNamespace kind x (totalRootColor x))
    (fourExtension_satisfies_fmla ext)
    (totalColoring_ownRootColorDegree_le_fifteen ext)

theorem fourExtension_satisfies_allCappedFmla {kind : Kind}
    (ext : FourExtension kind) :
    (SequentialAtMostManyCNF.iteratedSequentialExtension
      (allDegreeCounterSpecs totalRootColor)
      (coloringValuation (totalColoring ext))).satisfies_fmla
        (allCappedFmla kind) := by
  exact coloring_satisfies_withAllDegreeCapsFmla
    (ProfileDFourRowCNF.fmla kind) totalRootColor (totalColoring ext)
    (fmla_outside_counterNamespace kind)
    (fourExtension_satisfies_fmla ext)
    (totalColoring_ownRootColorDegree_le_fifteen ext)
    (fun x q => colorDegree_le_sixteen ext q x)

theorem noFourExtension_of_ownCapped_lrat (kind : Kind)
    (hunsat : (ownCappedFmla kind).proof []) :
    ¬Nonempty (FourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat _ (fourExtension_satisfies_ownCappedFmla ext)

theorem noFourExtension_of_allCapped_lrat (kind : Kind)
    (hunsat : (allCappedFmla kind).proof []) :
    ¬Nonempty (FourExtension kind) := by
  rintro ⟨ext⟩
  exact hunsat _ (fourExtension_satisfies_allCappedFmla ext)

#print axioms R4333.ProfileDThresholdCappedCNF.fmla_outside_counterNamespace
#print axioms R4333.ProfileDThresholdCappedCNF.fourExtension_satisfies_allCappedFmla
#print axioms R4333.ProfileDThresholdCappedCNF.noFourExtension_of_allCapped_lrat

end ProfileDThresholdCappedCNF
end R4333
