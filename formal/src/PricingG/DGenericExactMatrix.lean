import R4333Lean.ProfileDDegreeTenMatrixCNF

namespace PricingG.DGenericExactMatrix
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61 ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF ProfileDDegreeTenMatrixCNF

set_option maxHeartbeats 0
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex
abbrev ThreeFiveCoordinates := (FiveVertex ⊕ FiveVertex) ⊕ FiveVertex
abbrev RetainedVertex := Sum FiveVertex TailVertex

noncomputable def orderedSupportOfCardFive {n : Nat}
    (support : Finset (Fin n)) (hcard : support.card = 5) : OrderedFiveSupport n where
  embedding := (support.orderEmbOfFin hcard).toEmbedding
  ascending := (support.orderEmbOfFin hcard).strictMono
@[simp] theorem orderedSupportOfCardFive_positions {n : Nat}
    (support : Finset (Fin n)) (hcard : support.card = 5) :
    (orderedSupportOfCardFive support hcard).positions = support := by
  unfold OrderedFiveSupport.positions orderedSupportOfCardFive
  exact Finset.image_orderEmbOfFin_univ support hcard

def mergeVertexEmbedding : RetainedVertex ↪ TotalVertex where
  toFun := mergeVertex
  inj' := by
    intro left right h
    have hinv (x : RetainedVertex) : splitVertex (mergeVertex x) = x := by
      cases x <;> simp [mergeVertex]
    have hh := congrArg splitVertex h
    simpa only [hinv] using hh

def threeFiveEquiv : ThreeFiveCoordinates ≃ Fin 15 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl FiveVertex)).trans finSumFinEquiv
@[simp] theorem threeFiveEquiv_free (a : FiveVertex) :
    threeFiveEquiv (.inl (.inl a)) = freeMatrixIndex a := by fin_cases a <;> rfl
@[simp] theorem threeFiveEquiv_firstForeign (a : FiveVertex) :
    threeFiveEquiv (.inl (.inr a)) = firstForeignMatrixIndex a := by fin_cases a <;> rfl
@[simp] theorem threeFiveEquiv_secondForeign (a : FiveVertex) :
    threeFiveEquiv (.inr a) = secondForeignMatrixIndex a := by fin_cases a <;> rfl

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
    mergeVertexEmbedding

noncomputable def matrixVertexEmbedding
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block))) :
    Fin 15 ↪ TotalVertex :=
  threeFiveEquiv.symm.toEmbedding.trans
    (totalOrderedNeighborhoodEmbedding block first second)

@[simp] theorem matrixVertexEmbedding_free
    (block : Fin 3)
    (first : OrderedFiveSupport (blockSize (firstForeignBlock block)))
    (second : OrderedFiveSupport (blockSize (secondForeignBlock block)))
    (a : FiveVertex) :
    matrixVertexEmbedding block first second (freeMatrixIndex a) =
      freeVertex a := by
  rw [show freeMatrixIndex a =
      threeFiveEquiv
        (.inl (.inl a)) by
    exact (threeFiveEquiv_free a).symm]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding block first second
        (threeFiveEquiv.symm
          (threeFiveEquiv
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
      threeFiveEquiv
        (.inl (.inr a)) by
    exact (threeFiveEquiv_firstForeign a).symm]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding block first second
        (threeFiveEquiv.symm
          (threeFiveEquiv
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
      threeFiveEquiv
        (.inr a) by
    exact (threeFiveEquiv_secondForeign a).symm]
  change mergeVertex
      (retainedOrderedNeighborhoodEmbedding block first second
        (threeFiveEquiv.symm
          (threeFiveEquiv
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

def inducedMatrix {kind : ProfileDTripleJoinReduction.Kind}
    {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (coordinates : MatrixCoordinates block) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring
    (totalColoring
      branch.toDegreeFlooredFiveExtension.toFiveExtension)
    coordinates.vertex

/-- Uniform exact support-and-matrix packaging for a canonical UUU branch
whose selected endpoint has exact tail own-degree ten. -/
theorem exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten {kind : ProfileDTripleJoinReduction.Kind}
    {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) = 10) :
    ∃ coordinates : MatrixCoordinates block,
      ∃ matrix : EdgeColoring (Fin 15) (Fin 4),
        Nonempty (ExactDegreeTenMatrixBranch kind block position
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
    orderedSupportOfCardFive
      (foreignOwnSupport ext (firstForeignBlock block)) hfirst
  let second : OrderedFiveSupport (blockSize (secondForeignBlock block)) :=
    orderedSupportOfCardFive
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
      exact orderedSupportOfCardFive_positions
        _ hfirst]
    simpa [ext, CanonicalBranch.toFiveSupport] using
      mem_foreignOwnSupport ext (firstForeignBlock block) p
  · intro p
    change p ∈ second.positions ↔ _
    rw [show second.positions =
        foreignOwnSupport ext (secondForeignBlock block) by
      exact orderedSupportOfCardFive_positions
        _ hsecond]
    simpa [ext, CanonicalBranch.toFiveSupport] using
      mem_foreignOwnSupport ext (secondForeignBlock block) p
  · intro left right _hgroups
    rfl


#print axioms exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten
end PricingG.DGenericExactMatrix
