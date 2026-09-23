import R4333Lean.ProfileDUUUFourSupportP0RepresentativeData61
import R4333Lean.ProfileDFourRowCNF

/-!
# Authoritative selector CNF for UUU/block zero/position zero

This is the exact Lean formula mirrored by
`profile_d_four_support_p0_quotient.cnf`.  Starting from the plain UUU
four-row formula, it appends, in order:

1. four own-colour row-to-selected units;
2. exactly one of three normalized support-pair selectors;
3. for each pair, 31 guarded exact-support literals and one matrix-choice
   clause; and
4. for each of the 36 matrix selectors, its pair implication and 91 guarded
   edge literals on the physical `4+5+5` coordinates.

This module defines a formula only.  It neither asserts a refutation nor
imports an LRAT certificate.
-/

namespace R4333
namespace ProfileDUUUFourSupportP0SelectorCNF61

open FiniteColorCNF
open ProfileDTripleJoinReduction
open ProfileDUUUDegreeTenSupportOrbits61
open ProfileDUUUFourSupportP0RepresentativeData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev TotalVertex := ProfileDFourRowCNF.TotalVertex

def selectedVertex : TotalVertex := 4

def firstForeignVertex (p : Fin 15) : TotalVertex :=
  ⟨19 + p.val, by omega⟩

def secondForeignVertex (p : Fin 16) : TotalVertex :=
  ⟨34 + p.val, by omega⟩

def supportLiteral (atom : Nat) (member : Bool) : Sat.Literal :=
  if member then .pos atom else .neg atom

def firstFourOwnUnitClauses : Sat.Fmla :=
  (List.finRange 4).map fun row =>
    [Sat.Literal.pos (edgeAtom row.val selectedVertex.val 1)]

def pairSelectorAtoms : List Nat :=
  (List.finRange 3).map pairSelectorAtom

def pairAtLeastOneClause : Sat.Clause :=
  pairSelectorAtoms.map Sat.Literal.pos

def pairAtMostOneClauses : Sat.Fmla :=
  (edges 3).map fun pair =>
    [Sat.Literal.neg (pairSelectorAtom (Fin.ofNat 3 pair.1)),
      Sat.Literal.neg (pairSelectorAtom (Fin.ofNat 3 pair.2))]

def pairExactlyOneClauses : Sat.Fmla :=
  [pairAtLeastOneClause] ++ pairAtMostOneClauses

def pairFirstSupport (pair : SupportPair) : Finset (Fin 15) :=
  u15Support (pairFirstSupportIndex pair)

def pairSecondSupport (_pair : SupportPair) : Finset (Fin 16) :=
  u16Support 0

def firstSupportGuardClause (pair : SupportPair)
    (p : Fin 15) : Sat.Clause :=
  [Sat.Literal.neg (pairSelectorAtom pair),
    supportLiteral
      (edgeAtom selectedVertex.val (firstForeignVertex p).val 1)
      (decide (p ∈ pairFirstSupport pair))]

def secondSupportGuardClause (pair : SupportPair)
    (p : Fin 16) : Sat.Clause :=
  [Sat.Literal.neg (pairSelectorAtom pair),
    supportLiteral
      (edgeAtom selectedVertex.val (secondForeignVertex p).val 1)
      (decide (p ∈ pairSecondSupport pair))]

/-- U15 positions `0,...,14`, followed by U16 positions `0,...,15`. -/
def supportGuardClauses (pair : SupportPair) : Sat.Fmla :=
  (List.finRange 15).map (firstSupportGuardClause pair) ++
    (List.finRange 16).map (secondSupportGuardClause pair)

def matrixSelectorsForPair (pair : SupportPair) : List MatrixSelector :=
  (List.finRange 36).filter fun selector => matrixPair selector = pair

def matrixChoiceClause (pair : SupportPair) : Sat.Clause :=
  Sat.Literal.neg (pairSelectorAtom pair) ::
    (matrixSelectorsForPair pair).map fun selector =>
      Sat.Literal.pos (matrixSelectorAtom selector)

def matrixPairImplicationClause (selector : MatrixSelector) : Sat.Clause :=
  [Sat.Literal.neg (matrixSelectorAtom selector),
    Sat.Literal.pos (pairSelectorAtom (matrixPair selector))]

def matrixIndex (label : Nat) : Fin 14 :=
  ⟨label % 14, Nat.mod_lt label (by omega)⟩

def matrixGuardClause (selector : MatrixSelector)
    (pair : Nat × Nat) : Sat.Clause :=
  let left := matrixIndex pair.1
  let right := matrixIndex pair.2
  let kind := pairSupportKind (matrixPair selector)
  [Sat.Literal.neg (matrixSelectorAtom selector),
    Sat.Literal.pos (edgeAtom
      (physicalVertex kind left).val
      (physicalVertex kind right).val
      (representativeMatrixColor selector left right).val)]

def matrixGuardClauses (selector : MatrixSelector) : Sat.Fmla :=
  (edges 14).map (matrixGuardClause selector)

def matrixSelectorClauses (selector : MatrixSelector) : Sat.Fmla :=
  [matrixPairImplicationClause selector] ++ matrixGuardClauses selector

def pairBranchClauses (pair : SupportPair) : Sat.Fmla :=
  supportGuardClauses pair ++ [matrixChoiceClause pair] ++
    (matrixSelectorsForPair pair).flatMap matrixSelectorClauses

def selectorFmla : Sat.Fmla :=
  firstFourOwnUnitClauses ++ pairExactlyOneClauses ++
    (List.finRange 3).flatMap pairBranchClauses

/-- Exact quotient formula. -/
def fmla : Sat.Fmla :=
  ProfileDFourRowCNF.fmla .uuu ++ selectorFmla

theorem edges_fourteen_length : (edges 14).length = 91 := by decide

theorem supportGuardClauses_length (pair : SupportPair) :
    (supportGuardClauses pair).length = 31 := by
  simp [supportGuardClauses]

theorem matrixSelectorsForPair_length :
    (matrixSelectorsForPair 0).length = 16 ∧
    (matrixSelectorsForPair 1).length = 16 ∧
    (matrixSelectorsForPair 2).length = 4 := by decide

theorem matrixSelectorClauses_length (selector : MatrixSelector) :
    (matrixSelectorClauses selector).length = 92 := by
  simp [matrixSelectorClauses, matrixGuardClauses, edges_fourteen_length]

theorem selectorFmla_length : selectorFmla.length = 3416 := by decide

theorem baseFmla_length :
    (ProfileDFourRowCNF.fmla .uuu).length = 87311 := by decide

theorem fmla_length : fmla.length = 90727 := by
  simp [fmla, baseFmla_length, selectorFmla_length]

/-- The external DIMACS header uses one-based variables and therefore ends
at variable `6000093`, exactly one above the last Lean atom. -/
theorem dimacs_header_counts :
    (6000093 : Nat) = matrixSelectorAtom (Fin.last 35) + 1 ∧
      fmla.length = 90727 := by
  exact ⟨by decide, fmla_length⟩

#print axioms selectorFmla_length
#print axioms baseFmla_length
#print axioms fmla_length
#print axioms dimacs_header_counts

end ProfileDUUUFourSupportP0SelectorCNF61
end R4333
