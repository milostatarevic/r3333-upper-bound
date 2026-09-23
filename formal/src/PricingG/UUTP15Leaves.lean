import R4333Lean.ClauseCore
import PricingG.UUTP15Base
import R4333Lean.ProfileDUUUFourSupportP15SwapFiniteCoverage61

/-!
# Matrix-only leaves for UUU/block two/position fifteen

The checked restored-root catalogue stores 372 ordered colour matrices on
the physical `4+5+5` non-root neighbours.  This module defines the exact
91-unit CNF suffix for one such matrix and its semantic satisfaction
interface.  The suffix fixes no selected-endpoint or foreign-support edge:
those additional 34 units are deliberately outside this smaller boundary.

There is no SAT result, LRAT trace, or census claim in this file.
-/

namespace R4333
namespace UUTP15Leaves

open FiniteColorCNF
open ProfileDTripleJoinReduction
open ProfileDFourSupportRestoredRootK15
open UUTP15SupportPair
open UUTP15Base
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev OrderedLeaf := ProfileDUUUFourSupportP15SwapData61.OrderedLeaf
abbrev SwapSeed := ProfileDUUUFourSupportP15SwapData61.SwapSeed

def matrixIndex (label : Nat) : Fin 14 :=
  ⟨label % 14, Nat.mod_lt label (by omega)⟩

/-! ## Literal physical coordinates of one stored leaf -/

/-- The concrete four-row-CNF vertex corresponding to one abstract
`4|5|5` matrix coordinate.  This is the same physical order used by the
audited Python leaf suffix: four retained rows, the ordered first support in
tail block zero, and the ordered second support in tail block one. -/
def leafPhysicalVertex (leaf : OrderedLeaf) (i : Fin 14) :
    ProfileDFourRowCNF.TotalVertex :=
  match fourFiveFiveEquiv.symm i with
  | .inl (.inl free) => ProfileDFourRowCNF.freeVertex free
  | .inl (.inr first) =>
      ProfileDFourRowCNF.tailVertex
        (blockVertex 0
          ((support (orderedFirst leaf)).embedding first).val)
  | .inr second =>
      ProfileDFourRowCNF.tailVertex
        (blockVertex 1
          ((support (orderedSecond leaf)).embedding second).val)

@[simp] theorem leafPhysicalVertex_free (leaf : OrderedLeaf) (p : Fin 4) :
    leafPhysicalVertex leaf (freeLabel p) =
      ProfileDFourRowCNF.freeVertex p := by
  simp [leafPhysicalVertex, freeLabel]

@[simp] theorem leafPhysicalVertex_first (leaf : OrderedLeaf) (p : Fin 5) :
    leafPhysicalVertex leaf (firstForeignLabel p) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 0 ((support (orderedFirst leaf)).embedding p).val) := by
  simp [leafPhysicalVertex, firstForeignLabel]

@[simp] theorem leafPhysicalVertex_second (leaf : OrderedLeaf) (p : Fin 5) :
    leafPhysicalVertex leaf (secondForeignLabel p) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 1 ((support (orderedSecond leaf)).embedding p).val) := by
  simp [leafPhysicalVertex, secondForeignLabel]

/-! ## Exact 91-unit formula -/

/-- One positive edge unit fixing one entry of a stored ordered matrix. -/
def matrixUnitClause (leaf : OrderedLeaf)
    (pair : Nat × Nat) : Sat.Clause :=
  let left := matrixIndex pair.1
  let right := matrixIndex pair.2
  [Sat.Literal.pos (edgeAtom
    (leafPhysicalVertex leaf left).val
    (leafPhysicalVertex leaf right).val
    (orderedMatrixColor leaf left right).val)]

/-- The 91 matrix units in the common lexicographic `edges 14` order. -/
def matrixUnitFmla (leaf : OrderedLeaf) : Sat.Fmla :=
  (edges 14).map (matrixUnitClause leaf)

/-- The authoritative UUU four-row base plus one exact ordered matrix. -/
def matrixLeafFmla (leaf : OrderedLeaf) : Sat.Fmla :=
  ProfileDFourRowCNF.fmla .uut ++ matrixUnitFmla leaf

theorem matrixUnitFmla_length (leaf : OrderedLeaf) :
    (matrixUnitFmla leaf).length = 91 := by
  simp [matrixUnitFmla]
  decide

theorem baseFmla_length :
    (ProfileDFourRowCNF.fmla .uut).length = 87311 := by
  decide

theorem matrixLeafFmla_length (leaf : OrderedLeaf) :
    (matrixLeafFmla leaf).length = 87402 := by
  simp [matrixLeafFmla, matrixUnitFmla_length, baseFmla_length]

/-! ## Semantic exact-leaf interface -/

/-- A semantic P15 branch whose normalized supports and physical old-root
matrix are exactly one stored ordered leaf.  The support equalities are not
needed to satisfy the 91-unit formula, but are retained for the subsequent
checked local-action and equal-K15-swap transports. -/
structure ExactOrderedLeaf (leaf : OrderedLeaf) where
  normalized : NormalizedSupportPair
  first_eq : normalized.first = orderedFirst leaf
  second_eq : normalized.second = orderedSecond leaf
  matrixExact : ∀ left right : Fin 14, left ≠ right →
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (leafPhysicalVertex leaf left) (leafPhysicalVertex leaf right) =
      orderedMatrixColor leaf left right

def baseValuation {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) : Sat.Valuation :=
  coloringValuation
    (ProfileDFourRowCNF.totalColoring
      (fourExtension exact.normalized.branch))

theorem exact_satisfies_baseFmla {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) :
    (baseValuation exact).satisfies_fmla
      (ProfileDFourRowCNF.fmla .uut) := by
  exact ProfileDFourRowCNF.fourExtension_satisfies_fmla
    (fourExtension exact.normalized.branch)

theorem exact_satisfies_matrixUnitFmla {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) :
    (baseValuation exact).satisfies_fmla (matrixUnitFmla leaf) := by
  constructor
  intro clause hclause
  simp only [matrixUnitFmla, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  obtain ⟨hleft, hright, hlr⟩ :=
    SingleRootStarCNF.mem_edges_bounds hpair
  let left : Fin 14 := matrixIndex pair.1
  let right : Fin 14 := matrixIndex pair.2
  have hleftVal : left.val = pair.1 := by
    simp [left, matrixIndex, Nat.mod_eq_of_lt hleft]
  have hrightVal : right.val = pair.2 := by
    simp [right, matrixIndex, Nat.mod_eq_of_lt hright]
  have hleftRight : left.val < right.val := by omega
  have hne : left ≠ right := Fin.ne_of_lt hleftRight
  let leftVertex := leafPhysicalVertex leaf left
  let rightVertex := leafPhysicalVertex leaf right
  apply satisfies_of_mem_holds (baseValuation exact)
    (l := Sat.Literal.pos (edgeAtom leftVertex.val rightVertex.val
      (orderedMatrixColor leaf left right).val))
  · exact List.Mem.head _
  · apply (coloringValuation_edgeAtom
      (ProfileDFourRowCNF.totalColoring
        (fourExtension exact.normalized.branch))
      leftVertex rightVertex (orderedMatrixColor leaf left right)).2
    exact exact.matrixExact left right hne

theorem exact_satisfies_matrixLeafFmla {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) :
    (baseValuation exact).satisfies_fmla (matrixLeafFmla leaf) := by
  apply ClauseCore.satisfies_append
  · exact exact_satisfies_baseFmla exact
  · exact exact_satisfies_matrixUnitFmla exact

/-! ## Conditional certificate boundary -/

/-- A kernel proof for every displayed swap seed rules out an exact semantic
realization of every one of those seed leaves.  This theorem does not assert
that arbitrary ordered leaves reach seeds; that semantic transport is a
separate downstream obligation. -/
theorem no_exactSeed_of_refutations
    (refute : ∀ seed : SwapSeed,
      (matrixLeafFmla
        (ProfileDUUUFourSupportP15SwapData61.seedLeaf seed)).proof
          Sat.Clause.nil)
    (seed : SwapSeed) :
    ¬ Nonempty
      (ExactOrderedLeaf
        (ProfileDUUUFourSupportP15SwapData61.seedLeaf seed)) := by
  rintro ⟨exact⟩
  exact refute seed (baseValuation exact)
    (exact_satisfies_matrixLeafFmla exact)

#print axioms leafPhysicalVertex_free
#print axioms matrixUnitFmla_length
#print axioms matrixLeafFmla_length
#print axioms exact_satisfies_matrixUnitFmla
#print axioms exact_satisfies_matrixLeafFmla
#print axioms no_exactSeed_of_refutations

end UUTP15Leaves
end R4333
