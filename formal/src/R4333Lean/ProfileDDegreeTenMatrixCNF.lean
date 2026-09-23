import R4333Lean.ProfileDHighOwnFiveSupportC5CheckedBoundary
import R4333Lean.ProfileDDegreeTenNeighborhoodPartition61
import R4333Lean.ProfileDDegreeTenRestoredRootK16

/-!
# A fixed degree-ten / catalogued-neighbourhood CNF leaf

This file appends only ordinary edge-atom units to the exact profile-D
five-support formula.  The order is deliberately part of the definition:

1. every position of the first foreign block, then every position of the
   second foreign block, is fixed positive or negative according to the
   selected endpoint's exact own-colour support; and
2. the 75 edges joining different consecutive five-sets of the labelled
   `Fin 15` neighbourhood are fixed positively to a supplied matrix.

For source block zero, the support prefix therefore has the requested 31
clauses (block one positions `0,...,14`, followed by block two positions
`0,...,15`).  The neighbourhood order is the free five, the ascending first
foreign support, and the ascending second foreign support.  Proof fields in
`MatrixCoordinates` make that order explicit while leaving the formula
generic for later orbit representatives and checked certificates.

No refutation certificate is supplied here.  `LeafLRATRefutation` is exactly
the proposition a future `checked_lrat_proof` invocation must establish.
-/

namespace R4333
namespace ProfileDDegreeTenMatrixCNF

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ProfileDTripleJoinReduction
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5CounterNamespace
open ProfileDHighOwnFiveSupportC5Formula

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex

/-! ## Ordered support and matrix coordinates -/

/-- Five distinct local positions, supplied in strictly increasing order. -/
structure OrderedFiveSupport (n : Nat) where
  embedding : FiveVertex ↪ Fin n
  ascending : StrictMono embedding

def OrderedFiveSupport.positions {n : Nat}
    (support : OrderedFiveSupport n) : Finset (Fin n) :=
  Finset.univ.image support.embedding

/-- Consecutive matrix indices `0,...,4`. -/
def freeMatrixIndex (a : FiveVertex) : Fin 15 :=
  ⟨a.val, by omega⟩

/-- Consecutive matrix indices `5,...,9`. -/
def firstForeignMatrixIndex (a : FiveVertex) : Fin 15 :=
  ⟨5 + a.val, by omega⟩

/-- Consecutive matrix indices `10,...,14`. -/
def secondForeignMatrixIndex (a : FiveVertex) : Fin 15 :=
  ⟨10 + a.val, by omega⟩

/-- The exact labelled neighbourhood used by the matrix units.  The
equations force the advertised order; injectivity guarantees that every
ordinary matrix edge has distinct endpoints. -/
structure MatrixCoordinates (block : Fin 3) where
  first : OrderedFiveSupport (blockSize (firstForeignBlock block))
  second : OrderedFiveSupport (blockSize (secondForeignBlock block))
  vertex : Fin 15 ↪ TotalVertex
  vertex_free : ∀ a : FiveVertex,
    vertex (freeMatrixIndex a) = freeVertex a
  vertex_first : ∀ a : FiveVertex,
    vertex (firstForeignMatrixIndex a) =
      tailVertex (blockVertex (firstForeignBlock block)
        (first.embedding a).val)
  vertex_second : ∀ a : FiveVertex,
    vertex (secondForeignMatrixIndex a) =
      tailVertex (blockVertex (secondForeignBlock block)
        (second.embedding a).val)

/-! ## Deterministic ordinary-unit formula -/

def selectedToForeignAtom (block : Fin 3)
    (position : Fin (blockSize block)) (target : Fin 3)
    (targetPosition : Fin (blockSize target)) : Nat :=
  OutsideDegreeCapCNF.outsideIncidentEdgeAtom
    (tailVertex (blockVertex block position.val))
    (tailVertex (blockVertex target targetPosition.val))
    (blockRootColor block)

def supportLiteral (atom : Nat) (isMember : Bool) : Sat.Literal :=
  if isMember then Sat.Literal.pos atom else Sat.Literal.neg atom

/-- First foreign block in position order, then second foreign block in
position order. -/
def foreignSupportUnitClauses (block : Fin 3)
    (position : Fin (blockSize block))
    (coordinates : MatrixCoordinates block) : Sat.Fmla :=
  ((List.finRange (blockSize (firstForeignBlock block))).map fun p =>
      (show Sat.Clause from [supportLiteral
        (selectedToForeignAtom block position (firstForeignBlock block) p)
        (decide (p ∈ coordinates.first.positions))])) ++
    ((List.finRange (blockSize (secondForeignBlock block))).map fun p =>
      (show Sat.Clause from [supportLiteral
        (selectedToForeignAtom block position (secondForeignBlock block) p)
        (decide (p ∈ coordinates.second.positions))]))

/-- Lexicographically ordered `Fin 15` pairs joining different consecutive
five-sets. -/
def crossGroupMatrixPairs : List (Nat × Nat) :=
  (FiniteColorCNF.edges 15).filter fun pair =>
    pair.1 / 5 ≠ pair.2 / 5

/-- Total conversion used in the executable clause generator.  Every number
occurring in `crossGroupMatrixPairs` is already below 15, so the modulus is
proved away in the semantic lemmas below. -/
def matrixIndex (label : Nat) : Fin 15 :=
  ⟨label % 15, Nat.mod_lt label (by omega)⟩

def matrixUnitClauses (coordinates : MatrixCoordinates block)
    (matrix : EdgeColoring (Fin 15) (Fin 4)) : Sat.Fmla :=
  crossGroupMatrixPairs.map fun pair =>
    let left := matrixIndex pair.1
    let right := matrixIndex pair.2
    (show Sat.Clause from [Sat.Literal.pos
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        (coordinates.vertex left) (coordinates.vertex right)
        (matrix left right))])

@[simp] theorem foreignSupportUnitClauses_length (block : Fin 3)
    (position : Fin (blockSize block))
    (coordinates : MatrixCoordinates block) :
    (foreignSupportUnitClauses block position coordinates).length =
      blockSize (firstForeignBlock block) +
        blockSize (secondForeignBlock block) := by
  unfold foreignSupportUnitClauses
  rw [List.length_append, List.length_map, List.length_map,
    List.length_finRange, List.length_finRange]

theorem foreignSupportUnitClauses_length_block_zero
    (position : Fin (blockSize 0))
    (coordinates : MatrixCoordinates 0) :
    (foreignSupportUnitClauses 0 position coordinates).length = 31 := by
  simp [ProfileDTripleJoinReduction.blockSize, firstForeignBlock,
    secondForeignBlock]

@[simp] theorem crossGroupMatrixPairs_length :
    crossGroupMatrixPairs.length = 75 := by
  decide

@[simp] theorem matrixUnitClauses_length
    (coordinates : MatrixCoordinates block)
    (matrix : EdgeColoring (Fin 15) (Fin 4)) :
    (matrixUnitClauses coordinates matrix).length = 75 := by
  simp [matrixUnitClauses]

/-- The exact leaf whose DIMACS/LRAT identity later certificates use. -/
def fixedDegreeTenMatrixFmla (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (coordinates : MatrixCoordinates block)
    (matrix : EdgeColoring (Fin 15) (Fin 4)) : Sat.Fmla :=
  (fmla kind block position ++
      foreignSupportUnitClauses block position coordinates) ++
    matrixUnitClauses coordinates matrix

/-! ## Exact semantic branch -/

/-- A canonical branch together with precisely the equalities asserted by
the ordinary support and cross-matrix units.  The exact tail degree is kept
as an explicit mathematical field, even though the two ordered supports
already expose its ten foreign neighbours. -/
structure ExactDegreeTenMatrixBranch (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (coordinates : MatrixCoordinates block)
    (matrix : EdgeColoring (Fin 15) (Fin 4)) where
  branch : CanonicalBranch kind block position
  tailOwnDegreeTen :
    colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) = 10
  firstSupportExact : ∀ p : Fin (blockSize (firstForeignBlock block)),
    p ∈ coordinates.first.positions ↔
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex block position.val)
        (blockVertex (firstForeignBlock block) p.val) =
          blockRootColor block
  secondSupportExact : ∀ p : Fin (blockSize (secondForeignBlock block)),
    p ∈ coordinates.second.positions ↔
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex block position.val)
        (blockVertex (secondForeignBlock block) p.val) =
          blockRootColor block
  matrixExact : ∀ left right : Fin 15,
    left.val / 5 ≠ right.val / 5 →
      totalColoring
        branch.toDegreeFlooredFiveExtension.toFiveExtension
          (coordinates.vertex left) (coordinates.vertex right) =
        matrix left right

/-! ## Ordinary atoms survive all 42 sequential extensions -/

private theorem iteratedSequentialExtension_eq_of_outside_all
    (specs : List CounterSpec) (valuation : Sat.Valuation) (atom : Nat)
    (houtside : ∀ spec, spec ∈ specs →
      ¬InSequentialNamespace spec.tag atom) :
    iteratedSequentialExtension specs valuation atom ↔ valuation atom := by
  induction specs generalizing valuation with
  | nil => rfl
  | cons head tail ih =>
      rw [iteratedSequentialExtension_cons]
      exact (ih (sequentialExtension head.tag head.inputs valuation) (by
        intro spec hspec
        exact houtside spec (List.Mem.tail head hspec))).trans
          (sequentialExtension_eq_of_outside head.tag head.inputs valuation
            (houtside head (List.Mem.head tail)))

theorem ordinaryEdgeAtom_outside_all_counters
    (block : Fin 3) (position : Fin (blockSize block))
    (left right : TotalVertex) (color : Fin 4) :
    ∀ spec, spec ∈ counterSpecs block position →
      ¬InSequentialNamespace spec.tag
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right color) := by
  intro spec hspec
  have hspec' := hspec
  simp only [counterSpecs, List.mem_map] at hspec'
  obtain ⟨context, _hcontext, rfl⟩ := hspec'
  simp only [counterSpec]
  unfold counterTag OutsideDegreeCapCNF.outsideIncidentEdgeAtom
  apply OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    (namespaceVertex context) (namespaceColor context)
  · exact lt_of_le_of_lt (Nat.min_le_left left.val right.val)
      (lt_trans left.isLt (by omega))
  · exact max_lt (lt_trans left.isLt (by omega))
      (lt_trans right.isLt (by omega))

theorem finalValuation_ordinaryEdgeAtom
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (left right : TotalVertex) (hne : left ≠ right) (color : Fin 4) :
    finalValuation branch
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right color) ↔
      totalColoring
        branch.toDegreeFlooredFiveExtension.toFiveExtension left right =
          color := by
  unfold finalValuation
  rw [iteratedSequentialExtension_eq_of_outside_all
    (counterSpecs block position)
    (coloringValuation
      (totalColoring
        branch.toDegreeFlooredFiveExtension.toFiveExtension))
    (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right color)
    (ordinaryEdgeAtom_outside_all_counters
      block position left right color)]
  exact OutsideDegreeCapCNF.coloringValuation_outsideIncidentEdgeAtom
    (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension)
    left right hne color

/-! ## Satisfaction of the two unit layers -/

private theorem satisfies_fmla_append {valuation : Sat.Valuation}
    {first second : Sat.Fmla}
    (hfirst : valuation.satisfies_fmla first)
    (hsecond : valuation.satisfies_fmla second) :
    valuation.satisfies_fmla (first ++ second) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · exact hfirst.prop clause hclause
  · exact hsecond.prop clause hclause

private theorem selected_ne_firstForeign
    (block : Fin 3) (position : Fin (blockSize block))
    (p : Fin (blockSize (firstForeignBlock block))) :
    tailVertex (blockVertex block position.val) ≠
      tailVertex (blockVertex (firstForeignBlock block) p.val) := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne block (firstForeignBlock block)
      (firstForeignBlock_ne block).symm position.isLt p.isLt)

private theorem selected_ne_secondForeign
    (block : Fin 3) (position : Fin (blockSize block))
    (p : Fin (blockSize (secondForeignBlock block))) :
    tailVertex (blockVertex block position.val) ≠
      tailVertex (blockVertex (secondForeignBlock block) p.val) := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne block (secondForeignBlock block)
      (secondForeignBlock_ne block).symm position.isLt p.isLt)

theorem exactBranch_satisfies_foreignSupportUnits
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    {coordinates : MatrixCoordinates block}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch
      kind block position coordinates matrix) :
    (finalValuation exact.branch).satisfies_fmla
      (foreignSupportUnitClauses block position coordinates) := by
  constructor
  intro clause hclause
  simp only [foreignSupportUnitClauses] at hclause
  rcases List.mem_append.mp hclause with hfirst | hsecond
  · obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hfirst
    by_cases hmem : p ∈ coordinates.first.positions
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.pos
          (selectedToForeignAtom block position
            (firstForeignBlock block) p))
      · simpa [supportLiteral, hmem] using
          (List.Mem.head ([] : List Sat.Literal) :
            List.Mem (Sat.Literal.pos
              (selectedToForeignAtom block position
                (firstForeignBlock block) p))
              [Sat.Literal.pos
                (selectedToForeignAtom block position
                  (firstForeignBlock block) p)])
      · change finalValuation exact.branch
          (selectedToForeignAtom block position
            (firstForeignBlock block) p)
        rw [selectedToForeignAtom,
          finalValuation_ordinaryEdgeAtom exact.branch _ _
            (selected_ne_firstForeign block position p),
          totalColoring_tail_tail]
        exact (exact.firstSupportExact p).mp hmem
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg
          (selectedToForeignAtom block position
            (firstForeignBlock block) p))
      · simpa [supportLiteral, hmem] using
          (List.Mem.head ([] : List Sat.Literal) :
            List.Mem (Sat.Literal.neg
              (selectedToForeignAtom block position
                (firstForeignBlock block) p))
              [Sat.Literal.neg
                (selectedToForeignAtom block position
                  (firstForeignBlock block) p)])
      · change ¬finalValuation exact.branch
          (selectedToForeignAtom block position
            (firstForeignBlock block) p)
        rw [selectedToForeignAtom,
          finalValuation_ordinaryEdgeAtom exact.branch _ _
            (selected_ne_firstForeign block position p),
          totalColoring_tail_tail]
        intro hcolor
        exact hmem ((exact.firstSupportExact p).mpr hcolor)
  · obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hsecond
    by_cases hmem : p ∈ coordinates.second.positions
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.pos
          (selectedToForeignAtom block position
            (secondForeignBlock block) p))
      · simpa [supportLiteral, hmem] using
          (List.Mem.head ([] : List Sat.Literal) :
            List.Mem (Sat.Literal.pos
              (selectedToForeignAtom block position
                (secondForeignBlock block) p))
              [Sat.Literal.pos
                (selectedToForeignAtom block position
                  (secondForeignBlock block) p)])
      · change finalValuation exact.branch
          (selectedToForeignAtom block position
            (secondForeignBlock block) p)
        rw [selectedToForeignAtom,
          finalValuation_ordinaryEdgeAtom exact.branch _ _
            (selected_ne_secondForeign block position p),
          totalColoring_tail_tail]
        exact (exact.secondSupportExact p).mp hmem
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg
          (selectedToForeignAtom block position
            (secondForeignBlock block) p))
      · simpa [supportLiteral, hmem] using
          (List.Mem.head ([] : List Sat.Literal) :
            List.Mem (Sat.Literal.neg
              (selectedToForeignAtom block position
                (secondForeignBlock block) p))
              [Sat.Literal.neg
                (selectedToForeignAtom block position
                  (secondForeignBlock block) p)])
      · change ¬finalValuation exact.branch
          (selectedToForeignAtom block position
            (secondForeignBlock block) p)
        rw [selectedToForeignAtom,
          finalValuation_ordinaryEdgeAtom exact.branch _ _
            (selected_ne_secondForeign block position p),
          totalColoring_tail_tail]
        intro hcolor
        exact hmem ((exact.secondSupportExact p).mpr hcolor)

theorem matrixIndex_val_of_lt {label : Nat} (hlabel : label < 15) :
    (matrixIndex label).val = label := by
  simp [matrixIndex, Nat.mod_eq_of_lt hlabel]

theorem exactBranch_satisfies_matrixUnits
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    {coordinates : MatrixCoordinates block}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch
      kind block position coordinates matrix) :
    (finalValuation exact.branch).satisfies_fmla
      (matrixUnitClauses coordinates matrix) := by
  constructor
  intro clause hclause
  simp only [matrixUnitClauses, List.mem_map] at hclause
  obtain ⟨pair, hpair, rfl⟩ := hclause
  have hedge : pair ∈ FiniteColorCNF.edges 15 :=
    (List.mem_filter.mp hpair).1
  obtain ⟨hleft, hright, hlr⟩ :=
    SingleRootStarCNF.mem_edges_bounds hedge
  have hgroups : pair.1 / 5 ≠ pair.2 / 5 :=
    of_decide_eq_true (List.mem_filter.mp hpair).2
  have hindices : matrixIndex pair.1 ≠ matrixIndex pair.2 := by
    intro heq
    have hvals := congrArg Fin.val heq
    rw [matrixIndex_val_of_lt hleft,
      matrixIndex_val_of_lt hright] at hvals
    omega
  apply satisfies_of_mem_holds
    (l := Sat.Literal.pos
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        (coordinates.vertex (matrixIndex pair.1))
        (coordinates.vertex (matrixIndex pair.2))
        (matrix (matrixIndex pair.1) (matrixIndex pair.2))))
  · exact List.Mem.head []
  · change finalValuation exact.branch
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        (coordinates.vertex (matrixIndex pair.1))
        (coordinates.vertex (matrixIndex pair.2))
        (matrix (matrixIndex pair.1) (matrixIndex pair.2)))
    rw [finalValuation_ordinaryEdgeAtom exact.branch _ _
      (coordinates.vertex.injective.ne hindices)]
    apply exact.matrixExact
    simpa [matrixIndex_val_of_lt hleft,
      matrixIndex_val_of_lt hright] using hgroups

theorem exactBranch_satisfies_fixedDegreeTenMatrixFmla
    {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    {coordinates : MatrixCoordinates block}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch
      kind block position coordinates matrix) :
    (finalValuation exact.branch).satisfies_fmla
      (fixedDegreeTenMatrixFmla
        kind block position coordinates matrix) := by
  apply satisfies_fmla_append
  · exact satisfies_fmla_append
      (canonicalBranch_satisfies_fmla exact.branch)
      (exactBranch_satisfies_foreignSupportUnits exact)
  · exact exactBranch_satisfies_matrixUnits exact

/-! ## Empty checked-certificate interface -/

/-- Exact proposition returned by a checked LRAT proof for one fixed leaf. -/
def LeafLRATRefutation (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (coordinates : MatrixCoordinates block)
    (matrix : EdgeColoring (Fin 15) (Fin 4)) : Prop :=
  (fixedDegreeTenMatrixFmla
    kind block position coordinates matrix).proof Sat.Clause.nil

theorem noExactDegreeTenMatrixBranch_of_lrat
    (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block))
    (coordinates : MatrixCoordinates block)
    (matrix : EdgeColoring (Fin 15) (Fin 4))
    (hunsat : LeafLRATRefutation
      kind block position coordinates matrix) :
    ¬Nonempty (ExactDegreeTenMatrixBranch
      kind block position coordinates matrix) := by
  rintro ⟨exact⟩
  exact hunsat (finalValuation exact.branch)
    (exactBranch_satisfies_fixedDegreeTenMatrixFmla exact)

#print axioms exactBranch_satisfies_fixedDegreeTenMatrixFmla
#print axioms noExactDegreeTenMatrixBranch_of_lrat

end ProfileDDegreeTenMatrixCNF
end R4333
