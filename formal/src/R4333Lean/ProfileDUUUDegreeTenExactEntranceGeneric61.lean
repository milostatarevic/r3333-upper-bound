import R4333Lean.ProfileDUUUDegreeTenExactEntrance61

/-!
# Block-generic semantic entrance to an exact UUU degree-ten matrix branch

The original entrance module specialized its retained-neighbourhood embedding
to source block zero.  This module packages the same construction uniformly
for any source block: the free five-set followed by the two ordered foreign
own-colour supports.  It contains no finite-refutation claim.
-/

namespace R4333
namespace ProfileDUUUDegreeTenExactEntranceGeneric61

open ProfileDTripleJoinReduction
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex
abbrev ThreeFiveCoordinates := (FiveVertex ⊕ FiveVertex) ⊕ FiveVertex
abbrev RetainedVertex := Sum FiveVertex TailVertex

noncomputable def retainedOrderedNeighborhoodEmbedding
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block))) :
    ThreeFiveCoordinates ↪ RetainedVertex where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr a) => .inr
        (blockVertex (firstForeignBlock block) (first.embedding a).val)
    | .inr a => .inr
        (blockVertex (secondForeignBlock block) (second.embedding a).val)
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
                    have habEmbedding := blockVertex_fixed_injective
                      (firstForeignBlock block) habVertex
                    have hab := first.embedding.injective habEmbedding
                    subst b
                    rfl
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (blockVertex_ne_of_block_ne
                  (firstForeignBlock block) (secondForeignBlock block)
                  (firstForeignBlock_ne_second block)
                  (first.embedding a).isLt (second.embedding b).isLt
                  hvertex).elim
    | inr a =>
        cases y with
        | inl y =>
            cases y with
            | inl b => cases hxy
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (blockVertex_ne_of_block_ne
                  (secondForeignBlock block) (firstForeignBlock block)
                  (firstForeignBlock_ne_second block).symm
                  (second.embedding a).isLt (first.embedding b).isLt
                  hvertex).elim
        | inr b =>
            have habVertex := Sum.inr.inj hxy
            have habEmbedding := blockVertex_fixed_injective
              (secondForeignBlock block) habVertex
            have hab := second.embedding.injective habEmbedding
            subst b
            rfl

noncomputable def totalOrderedNeighborhoodEmbedding
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block))) :
    ThreeFiveCoordinates ↪ TotalVertex :=
  (retainedOrderedNeighborhoodEmbedding block first second).trans
    ProfileDUUUDegreeTenExactEntrance61.mergeVertexEmbedding

noncomputable def matrixVertexEmbedding
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block))) :
    Fin 15 ↪ TotalVertex :=
  ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm.toEmbedding.trans
    (totalOrderedNeighborhoodEmbedding block first second)

@[simp] theorem matrixVertexEmbedding_free
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block)))
    (a : FiveVertex) :
    matrixVertexEmbedding block first second (freeMatrixIndex a) =
      freeVertex a := by
  rw [show freeMatrixIndex a =
      ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
        (.inl (.inl a)) by
    exact ProfileDUUUDegreeTenEndToEndSemantic61.catalogBlockZero_eq_freeMatrixIndex a |>.symm |>.trans
      (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv_blockZero a).symm]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding block first second
        (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm
          (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
            (.inl (.inl a))))) = freeVertex a
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem matrixVertexEmbedding_first
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block)))
    (a : FiveVertex) :
    matrixVertexEmbedding block first second (firstForeignMatrixIndex a) =
      tailVertex (blockVertex (firstForeignBlock block)
        (first.embedding a).val) := by
  rw [show firstForeignMatrixIndex a =
      ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
        (.inl (.inr a)) by
    exact ProfileDUUUDegreeTenEndToEndSemantic61.catalogBlockOne_eq_firstForeignMatrixIndex a |>.symm |>.trans
      (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv_blockOne a).symm]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding block first second
        (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm
          (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
            (.inl (.inr a))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem matrixVertexEmbedding_second
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block)))
    (a : FiveVertex) :
    matrixVertexEmbedding block first second (secondForeignMatrixIndex a) =
      tailVertex (blockVertex (secondForeignBlock block)
        (second.embedding a).val) := by
  rw [show secondForeignMatrixIndex a =
      ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
        (.inr a) by
    exact ProfileDUUUDegreeTenEndToEndSemantic61.catalogBlockTwo_eq_secondForeignMatrixIndex a |>.symm |>.trans
      (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv_blockTwo a).symm]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding block first second
        (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv.symm
          (ProfileDUUUDegreeTenEndToEndSemantic61.threeFiveEquiv
            (.inr a)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def matrixCoordinatesOfOrderedSupports
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block))) :
    MatrixCoordinates block where
  first := first
  second := second
  vertex := matrixVertexEmbedding block first second
  vertex_free := matrixVertexEmbedding_free block first second
  vertex_first := matrixVertexEmbedding_first block first second
  vertex_second := matrixVertexEmbedding_second block first second

def inducedMatrix
    {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch .uuu block position)
    (coordinates : MatrixCoordinates block) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring
    (totalColoring
      branch.toDegreeFlooredFiveExtension.toFiveExtension)
    coordinates.vertex

/-- Uniform exact support-and-matrix packaging for a canonical UUU branch
whose selected endpoint has exact tail own-degree ten. -/
theorem exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten
    {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch .uuu block position)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) = 10) :
    ∃ coordinates : MatrixCoordinates block,
      ∃ matrix : EdgeColoring (Fin 15) (Fin 4),
        Nonempty (ExactDegreeTenMatrixBranch .uuu block position
          coordinates matrix) := by
  let ext := branch.toFiveSupport
  obtain ⟨skeleton⟩ :=
    exists_threeC5Skeleton_of_tailOwnDegree_ten ext (by
      simpa [ext, CanonicalBranch.toFiveSupport] using hdegree)
  have hfirst :
      (foreignOwnSupport ext (firstForeignBlock block)).card = 5 := by
    simpa [ext, CanonicalBranch.toFiveSupport] using
      skeleton.firstForeignCycle.supportCard
  have hsecond :
      (foreignOwnSupport ext (secondForeignBlock block)).card = 5 := by
    simpa [ext, CanonicalBranch.toFiveSupport] using
      skeleton.secondForeignCycle.supportCard
  let first : OrderedFiveSupport (blockSize (firstForeignBlock block)) :=
    ProfileDUUUDegreeTenExactEntrance61.orderedSupportOfCardFive
      (foreignOwnSupport ext (firstForeignBlock block)) hfirst
  let second : OrderedFiveSupport (blockSize (secondForeignBlock block)) :=
    ProfileDUUUDegreeTenExactEntrance61.orderedSupportOfCardFive
      (foreignOwnSupport ext (secondForeignBlock block)) hsecond
  let coordinates : MatrixCoordinates block :=
    matrixCoordinatesOfOrderedSupports block first second
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
    rw [show first.positions =
        foreignOwnSupport ext (firstForeignBlock block) by
      exact ProfileDUUUDegreeTenExactEntrance61.orderedSupportOfCardFive_positions
        _ hfirst]
    simpa [ext, CanonicalBranch.toFiveSupport] using
      mem_foreignOwnSupport ext (firstForeignBlock block) p
  · intro p
    change p ∈ second.positions ↔ _
    rw [show second.positions =
        foreignOwnSupport ext (secondForeignBlock block) by
      exact ProfileDUUUDegreeTenExactEntrance61.orderedSupportOfCardFive_positions
        _ hsecond]
    simpa [ext, CanonicalBranch.toFiveSupport] using
      mem_foreignOwnSupport ext (secondForeignBlock block) p
  · intro left right _hgroups
    rfl

#print axioms matrixCoordinatesOfOrderedSupports
#print axioms exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten

end ProfileDUUUDegreeTenExactEntranceGeneric61
end R4333
