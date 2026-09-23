import R4333Lean.ProfileDDegreeTenMatrixLeafUUU0S0M25

/-!
# Ten explicit discovered profile-D degree-ten leaves

This is a finite data module for the ten direct leaves currently selected by
the external exploration:

* support 0 with matrices 0, 20, 21, 25;
* support 2 with matrices 0, 1, 5, 100; and
* support 7 with matrices 0, 45.

All leaves use kind `uuu`, source block zero, source position zero, and K16
support zero.  Each K15 support is an explicit increasing five-tuple, each
matrix is an explicit symmetric `Fin 15` table, and `formula` is exactly the
generic fixed-degree-ten formula.  This module records no orbit or catalogue
completeness theorem.
-/

namespace R4333
namespace ProfileDDegreeTenMatrixLeafTenDataUUU0

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex

inductive Leaf where
  | s0m0 | s0m20 | s0m21 | s0m25
  | s2m0 | s2m1 | s2m5 | s2m100
  | s7m0 | s7m45
  deriving DecidableEq, Fintype, Repr

def leaves : List Leaf :=
  [.s0m0, .s0m20, .s0m21, .s0m25,
   .s2m0, .s2m1, .s2m5, .s2m100,
   .s7m0, .s7m45]

def supportIndex : Leaf → Nat
  | .s0m0 | .s0m20 | .s0m21 | .s0m25 => 0
  | .s2m0 | .s2m1 | .s2m5 | .s2m100 => 2
  | .s7m0 | .s7m45 => 7

def matrixIndexNumber : Leaf → Nat
  | .s0m0 | .s2m0 | .s7m0 => 0
  | .s2m1 => 1
  | .s2m5 => 5
  | .s0m20 => 20
  | .s0m21 => 21
  | .s0m25 => 25
  | .s7m45 => 45
  | .s2m100 => 100

def fileStem : Leaf → String
  | .s0m0 => "s0-m0"
  | .s0m20 => "s0-m20"
  | .s0m21 => "s0-m21"
  | .s0m25 => "s0-m25"
  | .s2m0 => "s2-m0"
  | .s2m1 => "s2-m1"
  | .s2m5 => "s2-m5"
  | .s2m100 => "s2-m100"
  | .s7m0 => "s7-m0"
  | .s7m45 => "s7-m45"

theorem leaves_nodup : leaves.Nodup := by decide

theorem leaves_length : leaves.length = 10 := by decide

theorem leaves_metadata :
    leaves.map (fun leaf => (supportIndex leaf, matrixIndexNumber leaf)) =
      [(0, 0), (0, 20), (0, 21), (0, 25),
       (2, 0), (2, 1), (2, 5), (2, 100),
       (7, 0), (7, 45)] := by
  decide

/-! ## The three explicit support coordinate systems -/

def k15SupportIndexTwoEmbedding : FiveVertex ↪ Fin 15 where
  toFun := ![0, 6, 8, 9, 12]
  inj' := by decide

def k15SupportIndexTwo : OrderedFiveSupport 15 where
  embedding := k15SupportIndexTwoEmbedding
  ascending := by decide

def k15SupportIndexSevenEmbedding : FiveVertex ↪ Fin 15 where
  toFun := ![2, 4, 8, 12, 13]
  inj' := by decide

def k15SupportIndexSeven : OrderedFiveSupport 15 where
  embedding := k15SupportIndexSevenEmbedding
  ascending := by decide

def matrixVertexEmbeddingSupportTwo : Fin 15 ↪ TotalVertex where
  toFun := ![0, 1, 2, 3, 4, 20, 26, 28, 29, 32,
    35, 36, 39, 43, 49]
  inj' := by decide

def matrixVertexEmbeddingSupportSeven : Fin 15 ↪ TotalVertex where
  toFun := ![0, 1, 2, 3, 4, 22, 24, 28, 32, 33,
    35, 36, 39, 43, 49]
  inj' := by decide

def matrixCoordinatesSupportTwo : MatrixCoordinates 0 where
  first := k15SupportIndexTwo
  second := ProfileDDegreeTenMatrixLeafUUU0S0M25.k16SupportIndexZero
  vertex := matrixVertexEmbeddingSupportTwo
  vertex_free := by intro a; fin_cases a <;> decide
  vertex_first := by intro a; fin_cases a <;> decide
  vertex_second := by intro a; fin_cases a <;> decide

def matrixCoordinatesSupportSeven : MatrixCoordinates 0 where
  first := k15SupportIndexSeven
  second := ProfileDDegreeTenMatrixLeafUUU0S0M25.k16SupportIndexZero
  vertex := matrixVertexEmbeddingSupportSeven
  vertex_free := by intro a; fin_cases a <;> decide
  vertex_first := by intro a; fin_cases a <;> decide
  vertex_second := by intro a; fin_cases a <;> decide

def coordinates : Leaf → MatrixCoordinates 0
  | .s0m0 | .s0m20 | .s0m21 | .s0m25 =>
      ProfileDDegreeTenMatrixLeafUUU0S0M25.matrixCoordinates
  | .s2m0 | .s2m1 | .s2m5 | .s2m100 => matrixCoordinatesSupportTwo
  | .s7m0 | .s7m45 => matrixCoordinatesSupportSeven

theorem supportIndexTwo_positions :
    k15SupportIndexTwo.positions = {0, 6, 8, 9, 12} := by decide

theorem supportIndexSeven_positions :
    k15SupportIndexSeven.positions = {2, 4, 8, 12, 13} := by decide

/-! ## The ten literal symmetric matrices -/

def matrixTable : Leaf → Fin 15 → Fin 15 → Fin 4
  | .s0m0 =>
      ![![0, 2, 3, 3, 2, 0, 2, 0, 2, 3, 0, 2, 3, 3, 0],
        ![2, 0, 2, 3, 3, 2, 0, 0, 3, 2, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 0, 3, 2, 2, 0, 3, 0, 0, 2, 3],
        ![3, 3, 2, 0, 2, 2, 2, 3, 0, 0, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 3, 0, 2, 0, 2, 0, 3, 0, 3, 2],
        ![0, 2, 0, 2, 3, 0, 0, 3, 0, 3, 3, 2, 3, 0, 2],
        ![2, 0, 3, 2, 0, 0, 0, 3, 3, 0, 2, 3, 3, 2, 0],
        ![0, 0, 2, 3, 2, 3, 3, 0, 0, 0, 2, 2, 0, 3, 3],
        ![2, 3, 2, 0, 0, 0, 3, 0, 0, 3, 3, 0, 2, 3, 2],
        ![3, 2, 0, 0, 2, 3, 0, 0, 3, 0, 0, 3, 2, 2, 3],
        ![0, 2, 3, 3, 0, 3, 2, 2, 3, 0, 0, 0, 2, 0, 2],
        ![2, 0, 0, 3, 3, 2, 3, 2, 0, 3, 0, 0, 2, 2, 0],
        ![3, 3, 0, 2, 0, 3, 3, 0, 2, 2, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 0, 2, 3, 3, 2, 0, 2, 0, 0, 2],
        ![0, 3, 3, 0, 2, 2, 0, 3, 2, 3, 2, 0, 0, 2, 0]]
  | .s0m20 =>
      ![![0, 2, 3, 3, 2, 0, 2, 0, 3, 2, 0, 2, 0, 3, 3],
        ![2, 0, 2, 3, 3, 0, 3, 2, 2, 0, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 2, 2, 3, 0, 0, 0, 3, 3, 2, 0],
        ![3, 3, 2, 0, 2, 3, 0, 0, 2, 2, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 0, 2, 0, 3, 3, 0, 0, 3, 2],
        ![0, 0, 2, 3, 2, 0, 0, 3, 0, 3, 2, 2, 3, 3, 0],
        ![2, 3, 2, 0, 0, 0, 0, 3, 3, 0, 0, 3, 2, 3, 2],
        ![0, 2, 3, 0, 2, 3, 3, 0, 0, 0, 3, 0, 2, 2, 3],
        ![3, 2, 0, 2, 0, 0, 3, 0, 0, 3, 3, 2, 3, 0, 2],
        ![2, 0, 0, 2, 3, 3, 0, 0, 3, 0, 2, 3, 0, 2, 3],
        ![0, 2, 0, 3, 3, 2, 0, 3, 3, 2, 0, 0, 2, 0, 2],
        ![2, 0, 3, 3, 0, 2, 3, 0, 2, 3, 0, 0, 2, 2, 0],
        ![0, 3, 3, 2, 0, 3, 2, 2, 3, 0, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 3, 3, 2, 0, 2, 0, 2, 0, 0, 2],
        ![3, 3, 0, 0, 2, 0, 2, 3, 2, 3, 2, 0, 0, 2, 0]]
  | .s0m21 =>
      ![![0, 2, 3, 3, 2, 0, 2, 0, 3, 2, 0, 2, 0, 3, 3],
        ![2, 0, 2, 3, 3, 2, 0, 0, 2, 3, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 3, 0, 2, 0, 2, 0, 3, 3, 2, 0],
        ![3, 3, 2, 0, 2, 0, 2, 3, 2, 0, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 3, 2, 0, 0, 3, 0, 0, 3, 2],
        ![0, 2, 3, 0, 2, 0, 0, 3, 0, 3, 3, 0, 2, 2, 3],
        ![2, 0, 0, 2, 3, 0, 0, 3, 3, 0, 2, 3, 0, 2, 3],
        ![0, 0, 2, 3, 2, 3, 3, 0, 0, 0, 2, 2, 3, 3, 0],
        ![3, 2, 0, 2, 0, 0, 3, 0, 0, 3, 3, 2, 3, 0, 2],
        ![2, 3, 2, 0, 0, 3, 0, 0, 3, 0, 0, 3, 2, 3, 2],
        ![0, 2, 0, 3, 3, 3, 2, 2, 3, 0, 0, 0, 2, 0, 2],
        ![2, 0, 3, 3, 0, 0, 3, 2, 2, 3, 0, 0, 2, 2, 0],
        ![0, 3, 3, 2, 0, 2, 0, 3, 3, 2, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 2, 2, 3, 0, 3, 0, 2, 0, 0, 2],
        ![3, 3, 0, 0, 2, 3, 3, 0, 2, 2, 2, 0, 0, 2, 0]]
  | .s0m25 =>
      ProfileDDegreeTenMatrixLeafUUU0S0M25.catalogMatrixIndex25Table
  | .s2m0 =>
      ![![0, 2, 3, 3, 2, 0, 0, 2, 2, 3, 0, 2, 0, 3, 3],
        ![2, 0, 2, 3, 3, 0, 2, 3, 0, 2, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 2, 3, 2, 0, 0, 0, 3, 3, 2, 0],
        ![3, 3, 2, 0, 2, 3, 0, 0, 2, 2, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 2, 0, 3, 0, 3, 0, 0, 3, 2],
        ![0, 0, 2, 3, 2, 0, 3, 0, 3, 0, 2, 2, 3, 3, 0],
        ![0, 2, 3, 0, 2, 3, 0, 3, 0, 0, 3, 0, 2, 2, 3],
        ![2, 3, 2, 0, 0, 0, 3, 0, 0, 3, 0, 3, 2, 3, 2],
        ![2, 0, 0, 2, 3, 3, 0, 0, 0, 3, 2, 3, 0, 2, 3],
        ![3, 2, 0, 2, 0, 0, 0, 3, 3, 0, 3, 2, 3, 0, 2],
        ![0, 2, 0, 3, 3, 2, 3, 0, 2, 3, 0, 0, 2, 0, 2],
        ![2, 0, 3, 3, 0, 2, 0, 3, 3, 2, 0, 0, 2, 2, 0],
        ![0, 3, 3, 2, 0, 3, 2, 2, 0, 3, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 3, 2, 3, 2, 0, 0, 2, 0, 0, 2],
        ![3, 3, 0, 0, 2, 0, 3, 2, 3, 2, 2, 0, 0, 2, 0]]
  | .s2m1 =>
      ![![0, 2, 3, 3, 2, 0, 0, 2, 2, 3, 0, 2, 0, 3, 3],
        ![2, 0, 2, 3, 3, 2, 0, 0, 3, 2, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 3, 2, 0, 2, 0, 0, 3, 3, 2, 0],
        ![3, 3, 2, 0, 2, 0, 3, 2, 0, 2, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 2, 3, 0, 0, 3, 0, 0, 3, 2],
        ![0, 2, 3, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2, 2, 3],
        ![0, 0, 2, 3, 2, 3, 0, 3, 0, 0, 2, 2, 3, 3, 0],
        ![2, 0, 0, 2, 3, 0, 3, 0, 0, 3, 2, 3, 0, 2, 3],
        ![2, 3, 2, 0, 0, 3, 0, 0, 0, 3, 0, 3, 2, 3, 2],
        ![3, 2, 0, 2, 0, 0, 0, 3, 3, 0, 3, 2, 3, 0, 2],
        ![0, 2, 0, 3, 3, 3, 2, 2, 0, 3, 0, 0, 2, 0, 2],
        ![2, 0, 3, 3, 0, 0, 2, 3, 3, 2, 0, 0, 2, 2, 0],
        ![0, 3, 3, 2, 0, 2, 3, 0, 2, 3, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 2, 3, 2, 3, 0, 0, 2, 0, 0, 2],
        ![3, 3, 0, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 2, 0]]
  | .s2m5 =>
      ![![0, 2, 3, 3, 2, 0, 0, 2, 2, 3, 0, 2, 3, 3, 0],
        ![2, 0, 2, 3, 3, 0, 2, 3, 0, 2, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 2, 3, 2, 0, 0, 0, 3, 0, 2, 3],
        ![3, 3, 2, 0, 2, 3, 2, 0, 2, 0, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 0, 0, 3, 2, 3, 0, 0, 3, 2],
        ![0, 0, 2, 3, 2, 0, 3, 0, 3, 0, 2, 2, 0, 3, 3],
        ![0, 2, 3, 2, 0, 3, 0, 3, 0, 0, 3, 2, 3, 0, 2],
        ![2, 3, 2, 0, 0, 0, 3, 0, 0, 3, 0, 3, 2, 3, 2],
        ![2, 0, 0, 2, 3, 3, 0, 0, 0, 3, 2, 3, 3, 2, 0],
        ![3, 2, 0, 0, 2, 0, 0, 3, 3, 0, 3, 0, 2, 2, 3],
        ![0, 2, 0, 3, 3, 2, 3, 0, 2, 3, 0, 0, 2, 0, 2],
        ![2, 0, 3, 3, 0, 2, 2, 3, 3, 0, 0, 0, 2, 2, 0],
        ![3, 3, 0, 2, 0, 0, 3, 2, 3, 2, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 3, 0, 3, 2, 2, 0, 2, 0, 0, 2],
        ![0, 3, 3, 0, 2, 3, 2, 2, 0, 3, 2, 0, 0, 2, 0]]
  | .s2m100 =>
      ![![0, 2, 3, 3, 2, 0, 0, 3, 2, 2, 0, 2, 3, 3, 0],
        ![2, 0, 2, 3, 3, 0, 2, 2, 0, 3, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 2, 0, 0, 3, 2, 3, 0, 0, 2, 3],
        ![3, 3, 2, 0, 2, 3, 2, 0, 2, 0, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 3, 2, 0, 0, 0, 3, 0, 3, 2],
        ![0, 0, 2, 3, 2, 0, 3, 0, 3, 0, 2, 2, 0, 3, 3],
        ![0, 2, 0, 2, 3, 3, 0, 3, 0, 0, 3, 2, 3, 0, 2],
        ![3, 2, 0, 0, 2, 0, 3, 0, 0, 3, 0, 3, 2, 2, 3],
        ![2, 0, 3, 2, 0, 3, 0, 0, 0, 3, 2, 3, 3, 2, 0],
        ![2, 3, 2, 0, 0, 0, 0, 3, 3, 0, 3, 0, 2, 3, 2],
        ![0, 2, 3, 3, 0, 2, 3, 0, 2, 3, 0, 0, 2, 0, 2],
        ![2, 0, 0, 3, 3, 2, 2, 3, 3, 0, 0, 0, 2, 2, 0],
        ![3, 3, 0, 2, 0, 0, 3, 2, 3, 2, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 3, 0, 2, 2, 3, 0, 2, 0, 0, 2],
        ![0, 3, 3, 0, 2, 3, 2, 3, 0, 2, 2, 0, 0, 2, 0]]
  | .s7m0 =>
      ![![0, 2, 3, 3, 2, 0, 0, 2, 2, 3, 0, 2, 3, 3, 0],
        ![2, 0, 2, 3, 3, 0, 2, 3, 0, 2, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 2, 0, 2, 3, 0, 3, 0, 0, 2, 3],
        ![3, 3, 2, 0, 2, 3, 2, 0, 2, 0, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 3, 0, 0, 2, 0, 3, 0, 3, 2],
        ![0, 0, 2, 3, 2, 0, 3, 0, 3, 0, 2, 2, 0, 3, 3],
        ![0, 2, 0, 2, 3, 3, 0, 0, 0, 3, 3, 2, 3, 0, 2],
        ![2, 3, 2, 0, 0, 0, 0, 0, 3, 3, 3, 0, 2, 3, 2],
        ![2, 0, 3, 2, 0, 3, 0, 3, 0, 0, 2, 3, 3, 2, 0],
        ![3, 2, 0, 0, 2, 0, 3, 3, 0, 0, 0, 3, 2, 2, 3],
        ![0, 2, 3, 3, 0, 2, 3, 3, 2, 0, 0, 0, 2, 0, 2],
        ![2, 0, 0, 3, 3, 2, 2, 0, 3, 3, 0, 0, 2, 2, 0],
        ![3, 3, 0, 2, 0, 0, 3, 2, 3, 2, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 3, 0, 3, 2, 2, 0, 2, 0, 0, 2],
        ![0, 3, 3, 0, 2, 3, 2, 2, 0, 3, 2, 0, 0, 2, 0]]
  | .s7m45 =>
      ![![0, 2, 3, 3, 2, 0, 0, 3, 2, 2, 0, 2, 3, 3, 0],
        ![2, 0, 2, 3, 3, 0, 2, 2, 0, 3, 2, 0, 3, 0, 3],
        ![3, 2, 0, 2, 3, 2, 3, 0, 0, 2, 0, 3, 0, 2, 3],
        ![3, 3, 2, 0, 2, 3, 2, 0, 2, 0, 3, 3, 2, 0, 0],
        ![2, 3, 3, 2, 0, 2, 0, 2, 3, 0, 3, 0, 0, 3, 2],
        ![0, 0, 2, 3, 2, 0, 3, 0, 3, 0, 2, 2, 0, 3, 3],
        ![0, 2, 3, 2, 0, 3, 0, 0, 0, 3, 3, 2, 3, 0, 2],
        ![3, 2, 0, 0, 2, 0, 0, 0, 3, 3, 3, 0, 2, 2, 3],
        ![2, 0, 0, 2, 3, 3, 0, 3, 0, 0, 2, 3, 3, 2, 0],
        ![2, 3, 2, 0, 0, 0, 3, 3, 0, 0, 0, 3, 2, 3, 2],
        ![0, 2, 0, 3, 3, 2, 3, 3, 2, 0, 0, 0, 2, 0, 2],
        ![2, 0, 3, 3, 0, 2, 2, 0, 3, 3, 0, 0, 2, 2, 0],
        ![3, 3, 0, 2, 0, 0, 3, 2, 3, 2, 2, 2, 0, 0, 0],
        ![3, 0, 2, 0, 3, 3, 0, 2, 2, 3, 0, 2, 0, 0, 2],
        ![0, 3, 3, 0, 2, 3, 2, 3, 0, 2, 2, 0, 0, 2, 0]]

theorem matrixTable_symmetric (leaf : Leaf) (left right : Fin 15) :
    matrixTable leaf left right = matrixTable leaf right left := by
  cases leaf <;> fin_cases left <;> fin_cases right <;> decide

def matrix (leaf : Leaf) : EdgeColoring (Fin 15) (Fin 4) where
  color := matrixTable leaf
  color_symm := matrixTable_symmetric leaf

theorem matrix_diagonal_zero (leaf : Leaf) (vertex : Fin 15) :
    matrix leaf vertex vertex = 0 := by
  cases leaf <;> fin_cases vertex <;> decide

theorem matrix_avoids_one (leaf : Leaf) (left right : Fin 15) :
    matrix leaf left right ≠ 1 := by
  cases leaf <;> fin_cases left <;> fin_cases right <;> decide

/-! ## The indexed family of exact formulas -/

def formula (leaf : Leaf) : Sat.Fmla :=
  fixedDegreeTenMatrixFmla .uuu 0
    ProfileDDegreeTenMatrixLeafUUU0S0M25.selectedPosition
    (coordinates leaf) (matrix leaf)

theorem formula_length (leaf : Leaf) : (formula leaf).length = 343474 := by
  simp only [formula, fixedDegreeTenMatrixFmla, List.length_append,
    ProfileDDegreeTenMatrixLeafUUU0S0M25.exactBranchFormula_length,
    foreignSupportUnitClauses_length,
    matrixUnitClauses_length]
  cases leaf <;> decide

theorem formula_s0m25_eq_one :
    formula .s0m25 =
      ProfileDDegreeTenMatrixLeafUUU0S0M25.formula := by
  rfl

#print axioms matrixTable_symmetric
#print axioms matrix_avoids_one
#print axioms formula_length

end ProfileDDegreeTenMatrixLeafTenDataUUU0
end R4333
