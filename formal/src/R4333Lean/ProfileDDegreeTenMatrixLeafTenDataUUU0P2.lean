import R4333Lean.ProfileDDegreeTenMatrixLeafTenDataUUU0
import R4333Lean.ProfileBFourRowCNF

/-!
# Ten explicit UUU / block-zero / position-two degree-ten leaves

The labelled neighbourhood data for source position two is the same finite
catalogue as for source position zero: the three ordered support coordinate
systems and the ten `15 x 15` matrices are unchanged.  What changes is the
selected tail endpoint occurring in the base and foreign-support clauses.

This module makes that distinction explicit.  It reuses only the already
kernel-checked finite support and matrix data, defines the new authoritative
position-two formulas, and proves their exact lengths and semantic endpoint.
It contains no refutation or UNSAT claim.
-/

namespace R4333
namespace ProfileDDegreeTenMatrixLeafTenDataUUU0P2

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open ProfileDDegreeTenMatrixCNF
open SequentialAtMostCNF SequentialAtMostManyCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Leaf := ProfileDDegreeTenMatrixLeafTenDataUUU0.Leaf

abbrev leaves := ProfileDDegreeTenMatrixLeafTenDataUUU0.leaves
abbrev supportIndex := ProfileDDegreeTenMatrixLeafTenDataUUU0.supportIndex
abbrev matrixIndexNumber :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0.matrixIndexNumber
abbrev fileStem := ProfileDDegreeTenMatrixLeafTenDataUUU0.fileStem
abbrev coordinates := ProfileDDegreeTenMatrixLeafTenDataUUU0.coordinates
abbrev matrix := ProfileDDegreeTenMatrixLeafTenDataUUU0.matrix

theorem leaves_nodup : leaves.Nodup :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0.leaves_nodup

theorem leaves_length : leaves.length = 10 :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0.leaves_length

theorem leaves_metadata :
    leaves.map (fun leaf => (supportIndex leaf, matrixIndexNumber leaf)) =
      [(0, 0), (0, 20), (0, 21), (0, 25),
       (2, 0), (2, 1), (2, 5), (2, 100),
       (7, 0), (7, 45)] :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0.leaves_metadata

theorem matrix_diagonal_zero (leaf : Leaf) (vertex : Fin 15) :
    matrix leaf vertex vertex = 0 :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0.matrix_diagonal_zero leaf vertex

theorem matrix_avoids_one (leaf : Leaf) (left right : Fin 15) :
    matrix leaf left right ≠ 1 :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0.matrix_avoids_one leaf left right

/-! ## The new selected endpoint and exact formulas -/

def selectedPosition : Fin (blockSize 0) :=
  ⟨2, by decide⟩

theorem selectedPosition_val : selectedPosition.val = 2 := rfl

theorem selectedTotalVertex_val :
    (tailVertex (blockVertex 0 selectedPosition.val)).val = 7 := by
  decide

def formula (leaf : Leaf) : Sat.Fmla :=
  fixedDegreeTenMatrixFmla .uuu 0 selectedPosition
    (coordinates leaf) (matrix leaf)

theorem supportUnitClauses_length (leaf : Leaf) :
    (foreignSupportUnitClauses
      0 selectedPosition (coordinates leaf)).length = 31 := by
  exact foreignSupportUnitClauses_length_block_zero
    selectedPosition (coordinates leaf)

theorem matrixClauses_length (leaf : Leaf) :
    (matrixUnitClauses (coordinates leaf) (matrix leaf)).length = 75 := by
  exact matrixUnitClauses_length (coordinates leaf) (matrix leaf)

theorem templateUnitClauses_length :
    (ProfileDHighOwnFiveSupportC5CNF.templateUnitClauses .uuu).length =
      330 := by
  decide

theorem insideRootForbiddenUnitClauses_length :
    ProfileDHighOwnFiveSupportC5CNF.insideRootForbiddenUnitClauses.length =
      10 := by
  decide

theorem allFiveOwnUnitClauses_length :
    (ProfileDHighOwnFiveSupportC5CNF.allFiveOwnUnitClauses
      0 selectedPosition).length = 5 := by
  decide

theorem insideC5UnitClauses_length :
    (ProfileDHighOwnFiveSupportC5CNF.insideC5UnitClauses 0).length = 10 := by
  decide

theorem basePrefix_length :
    (ProfileDHighOwnFiveSupportC5CNF.baseFmla
      .uuu 0 selectedPosition).length = 92580 := by
  simp only [ProfileDHighOwnFiveSupportC5CNF.baseFmla,
    List.length_append, ProfileBFourRowCNF.goodColoringFmla_length,
    templateUnitClauses_length, insideRootForbiddenUnitClauses_length,
    allFiveOwnUnitClauses_length, insideC5UnitClauses_length]

theorem counterBlocks_length :
    ((counterSpecs 0 selectedPosition).map fun spec =>
      (counterBlock spec).length).sum = 250788 := by
  simp only [counterBlock, sequentialAtMostFmla_length]
  decide

theorem exactBranchFormula_length :
    (ProfileDHighOwnFiveSupportC5Formula.fmla
      .uuu 0 selectedPosition).length = 343368 := by
  rw [ProfileDHighOwnFiveSupportC5Formula.fmla,
    manySequentialAtMostFmla_length, basePrefix_length,
    counterBlocks_length]

theorem formula_length (leaf : Leaf) : (formula leaf).length = 343474 := by
  simp only [formula, fixedDegreeTenMatrixFmla, List.length_append,
    exactBranchFormula_length, supportUnitClauses_length,
    matrixClauses_length]

/-! ## Semantic endpoint for future checked certificates -/

abbrev RepresentativeExactBranch (leaf : Leaf) :=
  ExactDegreeTenMatrixBranch .uuu 0 selectedPosition
    (coordinates leaf) (matrix leaf)

theorem representativeExactBranch_satisfies_formula
    (leaf : Leaf) (exact : RepresentativeExactBranch leaf) :
    (finalValuation exact.branch).satisfies_fmla (formula leaf) := by
  exact exactBranch_satisfies_fixedDegreeTenMatrixFmla exact

#print axioms leaves_metadata
#print axioms selectedTotalVertex_val
#print axioms formula_length
#print axioms representativeExactBranch_satisfies_formula

end ProfileDDegreeTenMatrixLeafTenDataUUU0P2
end R4333
