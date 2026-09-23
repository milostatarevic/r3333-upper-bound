import R4333Lean.ProfileDUUUDegreeTenEndToEndSemantic61

/-!
# Semantic entrance to the exact UUU degree-ten matrix branch

This module closes the gap between a canonical five-support branch whose
selected tail endpoint has exact own-colour degree ten and the labelled
`ExactDegreeTenMatrixBranch` consumed by the semantic catalogue quotient.

The two foreign own-colour supports have cardinality five.  We enumerate
each in increasing order, use those enumerations together with the retained
free five-set as matrix coordinates, and take the pulled-back total colouring
itself as the matrix.  No LRAT result is imported here.
-/

namespace R4333
namespace ProfileDUUUDegreeTenExactEntrance61

open ProfileDTripleJoinReduction
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDUUUDegreeTenEndToEndSemantic61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex

/-! ## Increasing enumeration of a five-element finset -/

noncomputable def orderedSupportOfCardFive {n : Nat}
    (support : Finset (Fin n)) (hcard : support.card = 5) :
    OrderedFiveSupport n where
  embedding := (support.orderEmbOfFin hcard).toEmbedding
  ascending := (support.orderEmbOfFin hcard).strictMono

@[simp] theorem orderedSupportOfCardFive_positions {n : Nat}
    (support : Finset (Fin n)) (hcard : support.card = 5) :
    (orderedSupportOfCardFive support hcard).positions = support := by
  unfold OrderedFiveSupport.positions orderedSupportOfCardFive
  exact Finset.image_orderEmbOfFin_univ support hcard

/-! ## Embedding the three ordered five-sets in the retained total graph -/

abbrev ThreeFiveCoordinates := (FiveVertex ⊕ FiveVertex) ⊕ FiveVertex
abbrev RetainedVertex := Sum FiveVertex TailVertex

noncomputable def retainedOrderedNeighborhoodEmbedding
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) :
    ThreeFiveCoordinates ↪ RetainedVertex where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr a) => .inr
        (ProfileDTripleJoinReduction.blockVertex 1
          (first.embedding a).val)
    | .inr a => .inr
        (ProfileDTripleJoinReduction.blockVertex 2
          (second.embedding a).val)
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
        cases x with
        | inl a =>
            cases y with
            | inl y =>
                cases y with
                | inl b =>
                    have hab := Sum.inl.inj hxy
                    subst b
                    rfl
                | inr b => cases hxy
            | inr b => cases hxy
        | inr a =>
            cases y with
            | inl y =>
                cases y with
                | inl b => cases hxy
                | inr b =>
                    have habVertex := Sum.inr.inj hxy
                    have habEmbedding :=
                      ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective
                        1 habVertex
                    have hab := first.embedding.injective habEmbedding
                    subst b
                    rfl
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
                  1 2 (by decide)
                  (first.embedding a).isLt
                  (second.embedding b).isLt hvertex).elim
    | inr a =>
        cases y with
        | inl y =>
            cases y with
            | inl b => cases hxy
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
                  2 1 (by decide)
                  (second.embedding a).isLt
                  (first.embedding b).isLt hvertex).elim
        | inr b =>
            have habVertex := Sum.inr.inj hxy
            have habEmbedding :=
              ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective
                2 habVertex
            have hab := second.embedding.injective habEmbedding
            subst b
            rfl

def mergeVertexEmbedding : RetainedVertex ↪ TotalVertex where
  toFun := mergeVertex
  inj' := by
    intro left right h
    have := congrArg splitVertex h
    simpa using this

noncomputable def totalOrderedNeighborhoodEmbedding
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) :
    ThreeFiveCoordinates ↪ TotalVertex :=
  (retainedOrderedNeighborhoodEmbedding first second).trans
    mergeVertexEmbedding

noncomputable def matrixVertexEmbedding
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) : Fin 15 ↪ TotalVertex :=
  ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm.toEmbedding.trans
    (totalOrderedNeighborhoodEmbedding first second)

@[simp] theorem matrixVertexEmbedding_free
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) (a : FiveVertex) :
    matrixVertexEmbedding first second (freeMatrixIndex a) = freeVertex a := by
  have hindex : freeMatrixIndex a =
      ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
        (.inl (.inl a)) :=
    catalogBlockZero_eq_freeMatrixIndex a |>.symm |>.trans
      (threeFiveEquiv_blockZero a).symm
  rw [hindex]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding first second
        (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm
          (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
            (.inl (.inl a))))) = freeVertex a
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem matrixVertexEmbedding_first
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) (a : FiveVertex) :
    matrixVertexEmbedding first second (firstForeignMatrixIndex a) =
      tailVertex (ProfileDTripleJoinReduction.blockVertex 1
        (first.embedding a).val) := by
  have hindex : firstForeignMatrixIndex a =
      ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
        (.inl (.inr a)) :=
    catalogBlockOne_eq_firstForeignMatrixIndex a |>.symm |>.trans
      (threeFiveEquiv_blockOne a).symm
  rw [hindex]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding first second
        (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm
          (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
            (.inl (.inr a))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem matrixVertexEmbedding_second
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) (a : FiveVertex) :
    matrixVertexEmbedding first second (secondForeignMatrixIndex a) =
      tailVertex (ProfileDTripleJoinReduction.blockVertex 2
        (second.embedding a).val) := by
  have hindex : secondForeignMatrixIndex a =
      ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
        (.inr a) :=
    catalogBlockTwo_eq_secondForeignMatrixIndex a |>.symm |>.trans
      (threeFiveEquiv_blockTwo a).symm
  rw [hindex]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding first second
        (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm
          (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
            (.inr a)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def matrixCoordinatesOfOrderedSupports
    (first : OrderedFiveSupport 15)
    (second : OrderedFiveSupport 16) : MatrixCoordinates 0 where
  first := first
  second := second
  vertex := matrixVertexEmbedding first second
  vertex_free := matrixVertexEmbedding_free first second
  vertex_first := by
    intro a
    change matrixVertexEmbedding first second (firstForeignMatrixIndex a) =
      tailVertex (ProfileDTripleJoinReduction.blockVertex 1
        (first.embedding a).val)
    exact matrixVertexEmbedding_first first second a
  vertex_second := by
    intro a
    change matrixVertexEmbedding first second (secondForeignMatrixIndex a) =
      tailVertex (ProfileDTripleJoinReduction.blockVertex 2
        (second.embedding a).val)
    exact matrixVertexEmbedding_second first second a

/-! ## Exact support-and-matrix packaging -/

def inducedMatrix
    {position : Fin (blockSize 0)}
    (branch : CanonicalBranch .uuu 0 position)
    (coordinates : MatrixCoordinates 0) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring
    (totalColoring
      branch.toDegreeFlooredFiveExtension.toFiveExtension)
    coordinates.vertex

theorem exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten
    {position : Fin (blockSize 0)}
    (branch : CanonicalBranch .uuu 0 position)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (ProfileDTripleJoinReduction.blockVertex 0 position.val) = 10) :
    ∃ coordinates : MatrixCoordinates 0,
      ∃ matrix : EdgeColoring (Fin 15) (Fin 4),
        Nonempty (ExactDegreeTenMatrixBranch .uuu 0 position
          coordinates matrix) := by
  let ext := branch.toFiveSupport
  obtain ⟨skeleton⟩ :=
    exists_threeC5Skeleton_of_tailOwnDegree_ten ext (by
      simpa [ext, CanonicalBranch.toFiveSupport] using hdegree)
  have hfirst : (foreignOwnSupport ext 1).card = 5 := by
    simpa [ext, CanonicalBranch.toFiveSupport,
      ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock] using
      skeleton.firstForeignCycle.supportCard
  have hsecond : (foreignOwnSupport ext 2).card = 5 := by
    simpa [ext, CanonicalBranch.toFiveSupport,
      ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock] using
      skeleton.secondForeignCycle.supportCard
  let first : OrderedFiveSupport 15 :=
    orderedSupportOfCardFive (foreignOwnSupport ext 1) hfirst
  let second : OrderedFiveSupport 16 :=
    orderedSupportOfCardFive (foreignOwnSupport ext 2) hsecond
  let coordinates : MatrixCoordinates 0 :=
    matrixCoordinatesOfOrderedSupports first second
  let matrix : EdgeColoring (Fin 15) (Fin 4) :=
    inducedMatrix branch coordinates
  refine ⟨coordinates, matrix, ⟨{
    branch := branch
    tailOwnDegreeTen := hdegree
    firstSupportExact := ?_
    secondSupportExact := ?_
    matrixExact := ?_
  }⟩⟩
  · intro p
    change p ∈ first.positions ↔ _
    rw [show first.positions = foreignOwnSupport ext 1 by
      exact orderedSupportOfCardFive_positions _ hfirst]
    change p ∈ foreignOwnSupport ext 1 ↔
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex ext.block ext.position.val)
        (ProfileDTripleJoinReduction.blockVertex 1 p.val) =
          blockRootColor ext.block
    exact mem_foreignOwnSupport ext 1 p
  · intro p
    change p ∈ second.positions ↔ _
    rw [show second.positions = foreignOwnSupport ext 2 by
      exact orderedSupportOfCardFive_positions _ hsecond]
    change p ∈ foreignOwnSupport ext 2 ↔
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (ProfileDTripleJoinReduction.blockVertex ext.block ext.position.val)
        (ProfileDTripleJoinReduction.blockVertex 2 p.val) =
          blockRootColor ext.block
    exact mem_foreignOwnSupport ext 2 p
  · intro left right _hgroups
    rfl

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafUUU0S0M25.selectedPosition

theorem exists_exactDegreeTenMatrixBranch_selected
    (branch : CanonicalBranch .uuu 0 SelectedPosition)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val) = 10) :
    ∃ coordinates : MatrixCoordinates 0,
      ∃ matrix : EdgeColoring (Fin 15) (Fin 4),
        Nonempty (ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
          coordinates matrix) :=
  exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten branch hdegree

/-- The complete LRAT-free semantic route from the canonical degree-ten
subbranch to one of the ten representative exact leaves. -/
theorem exists_representativeExactBranch_of_canonical_degreeTen
    (branch : CanonicalBranch .uuu 0 SelectedPosition)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val) = 10) :
    ∃ leaf : ProfileDDegreeTenMatrixLeafTenDataUUU0.Leaf,
      Nonempty
        (ProfileDDegreeTenRepresentativeLeafBridge61.RepresentativeExactBranch
          leaf) := by
  obtain ⟨coordinates, matrix, ⟨exact⟩⟩ :=
    exists_exactDegreeTenMatrixBranch_selected branch hdegree
  exact exists_representativeExactBranch_of_exact exact

#print axioms orderedSupportOfCardFive_positions
#print axioms exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten
#print axioms exists_exactDegreeTenMatrixBranch_selected
#print axioms exists_representativeExactBranch_of_canonical_degreeTen

end ProfileDUUUDegreeTenExactEntrance61
end R4333
