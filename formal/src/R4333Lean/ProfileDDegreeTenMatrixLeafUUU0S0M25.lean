import R4333Lean.ProfileDDegreeTenMatrixCNF
import R4333Lean.ProfileBFourRowCNF

/-!
# One explicit profile-D degree-ten matrix leaf

This module contains only the finite data for the discovery leaf conventionally
named `UUU / block 0 / position 0 / K15-support 0 / K16-support 0 /
matrix 25`, and the exact Lean formula obtained from that data.

The two support tuples are `(0,1,4,8,14)`.  Matrix index 25 is recorded as a
literal symmetric `15 × 15` table in the actual four-colour palette.  These
definitions establish formula identity only: this module deliberately makes
no claim that the support or matrix indices cover any catalogue orbit.
-/

namespace R4333
namespace ProfileDDegreeTenMatrixLeafUUU0S0M25

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open ProfileDDegreeTenMatrixCNF
open SequentialAtMostCNF SequentialAtMostManyCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex

/-! ## The two index-zero ordered supports -/

/-- Index zero in the untwisted K15 colour-one-independent-five list. -/
def k15SupportIndexZeroEmbedding : FiveVertex ↪ Fin 15 where
  toFun := ![0, 1, 4, 8, 14]
  inj' := by decide

theorem k15SupportIndexZeroEmbedding_strictMono :
    StrictMono k15SupportIndexZeroEmbedding := by
  decide

def k15SupportIndexZero : OrderedFiveSupport 15 where
  embedding := k15SupportIndexZeroEmbedding
  ascending := k15SupportIndexZeroEmbedding_strictMono

/-- Index zero in the untwisted K16 colour-one-independent-five list. -/
def k16SupportIndexZeroEmbedding : FiveVertex ↪ Fin 16 where
  toFun := ![0, 1, 4, 8, 14]
  inj' := by decide

theorem k16SupportIndexZeroEmbedding_strictMono :
    StrictMono k16SupportIndexZeroEmbedding := by
  decide

def k16SupportIndexZero : OrderedFiveSupport 16 where
  embedding := k16SupportIndexZeroEmbedding
  ascending := k16SupportIndexZeroEmbedding_strictMono

theorem k15SupportIndexZero_positions :
    k15SupportIndexZero.positions = {0, 1, 4, 8, 14} := by
  decide

theorem k16SupportIndexZero_positions :
    k16SupportIndexZero.positions = {0, 1, 4, 8, 14} := by
  decide

/-! ## Consecutive free/support/support matrix labelling -/

/-- Total-graph labels
`0,1,2,3,4; 20,21,24,28,34; 35,36,39,43,49`. -/
def matrixVertexEmbedding : Fin 15 ↪ TotalVertex where
  toFun := ![0, 1, 2, 3, 4, 20, 21, 24, 28, 34, 35, 36, 39, 43, 49]
  inj' := by decide

def matrixCoordinates : MatrixCoordinates 0 where
  first := k15SupportIndexZero
  second := k16SupportIndexZero
  vertex := matrixVertexEmbedding
  vertex_free := by
    intro a
    fin_cases a <;> decide
  vertex_first := by
    intro a
    fin_cases a <;> decide
  vertex_second := by
    intro a
    fin_cases a <;> decide

theorem matrixVertexEmbedding_values :
    (List.finRange 15).map (fun i => (matrixVertexEmbedding i).val) =
      [0, 1, 2, 3, 4, 20, 21, 24, 28, 34, 35, 36, 39, 43, 49] := by
  decide

/-! ## Literal labelled matrix number 25 -/

/-- The symmetric matrix is written out in full to keep its identity local,
finite, and kernel-reducible.  Diagonal zeroes are conventional and do not
generate clauses. -/
def catalogMatrixIndex25Table : Fin 15 → Fin 15 → Fin 4 :=
  ![![0, 2, 3, 3, 2, 0, 2, 0, 3, 2, 0, 2, 3, 3, 0],
    ![2, 0, 2, 3, 3, 0, 3, 2, 2, 0, 2, 0, 3, 0, 3],
    ![3, 2, 0, 2, 3, 2, 2, 3, 0, 0, 0, 3, 0, 2, 3],
    ![3, 3, 2, 0, 2, 3, 0, 2, 0, 2, 3, 3, 2, 0, 0],
    ![2, 3, 3, 2, 0, 2, 0, 0, 2, 3, 3, 0, 0, 3, 2],
    ![0, 0, 2, 3, 2, 0, 0, 3, 0, 3, 2, 2, 0, 3, 3],
    ![2, 3, 2, 0, 0, 0, 0, 3, 3, 0, 0, 3, 2, 3, 2],
    ![0, 2, 3, 2, 0, 3, 3, 0, 0, 0, 3, 2, 3, 0, 2],
    ![3, 2, 0, 0, 2, 0, 3, 0, 0, 3, 3, 0, 2, 2, 3],
    ![2, 0, 0, 2, 3, 3, 0, 0, 3, 0, 2, 3, 3, 2, 0],
    ![0, 2, 0, 3, 3, 2, 0, 3, 3, 2, 0, 0, 2, 0, 2],
    ![2, 0, 3, 3, 0, 2, 3, 2, 0, 3, 0, 0, 2, 2, 0],
    ![3, 3, 0, 2, 0, 0, 2, 3, 2, 3, 2, 2, 0, 0, 0],
    ![3, 0, 2, 0, 3, 3, 3, 0, 2, 2, 0, 2, 0, 0, 2],
    ![0, 3, 3, 0, 2, 3, 2, 2, 3, 0, 2, 0, 0, 2, 0]]

theorem catalogMatrixIndex25Table_symmetric
    (left right : Fin 15) :
    catalogMatrixIndex25Table left right =
      catalogMatrixIndex25Table right left := by
  fin_cases left <;> fin_cases right <;> decide

def catalogMatrixIndex25 : EdgeColoring (Fin 15) (Fin 4) where
  color := catalogMatrixIndex25Table
  color_symm := catalogMatrixIndex25Table_symmetric

/-- The original 105-entry upper-triangle word, in
`FiniteColorCNF.edges 15` order. -/
def catalogMatrixIndex25UpperTriangle : List (Fin 4) :=
  (FiniteColorCNF.edges 15).map fun pair =>
    catalogMatrixIndex25 (matrixIndex pair.1) (matrixIndex pair.2)

theorem catalogMatrixIndex25UpperTriangle_values :
    catalogMatrixIndex25UpperTriangle =
      [2, 3, 3, 2, 0, 2, 0, 3, 2, 0, 2, 3, 3, 0,
       2, 3, 3, 0, 3, 2, 2, 0, 2, 0, 3, 0, 3, 2,
       3, 2, 2, 3, 0, 0, 0, 3, 0, 2, 3, 2, 3, 0,
       2, 0, 2, 3, 3, 2, 0, 0, 2, 0, 0, 2, 3, 3, 0,
       0, 3, 2, 0, 3, 0, 3, 2, 2, 0, 3, 3, 3, 3, 0,
       0, 3, 2, 3, 2, 0, 0, 3, 2, 3, 0, 2, 3, 3, 0,
       2, 2, 3, 2, 3, 3, 2, 0, 0, 2, 0, 2, 2, 2, 0,
       0, 0, 2] := by
  decide

/-! ## The concrete authoritative formula -/

def selectedPosition : Fin (blockSize 0) :=
  ⟨0, by decide⟩

def formula : Sat.Fmla :=
  fixedDegreeTenMatrixFmla .uuu 0 selectedPosition
    matrixCoordinates catalogMatrixIndex25

theorem supportUnitClauses_length :
    (foreignSupportUnitClauses
      0 selectedPosition matrixCoordinates).length = 31 := by
  exact foreignSupportUnitClauses_length_block_zero
    selectedPosition matrixCoordinates

theorem matrixClauses_length :
    (matrixUnitClauses matrixCoordinates catalogMatrixIndex25).length = 75 := by
  exact matrixUnitClauses_length matrixCoordinates catalogMatrixIndex25

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

theorem formula_length : formula.length = 343474 := by
  simp only [formula, fixedDegreeTenMatrixFmla, List.length_append,
    exactBranchFormula_length, supportUnitClauses_length,
    matrixClauses_length]

#print axioms k15SupportIndexZeroEmbedding_strictMono
#print axioms catalogMatrixIndex25Table_symmetric
#print axioms formula_length

end ProfileDDegreeTenMatrixLeafUUU0S0M25
end R4333
