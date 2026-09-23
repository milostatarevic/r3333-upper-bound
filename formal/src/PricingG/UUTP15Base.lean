import PricingG.UUTP15SupportPair
import R4333Lean.ProfileDFourSupportInside61
import R4333Lean.ProfileDFourSupportRestoredRootK15

/-!
# Semantic restored-root base for UUU/block two/position fifteen

After strong support normalization, this file gives the exact ordered
`4|5|5` embedding used by the 372-leaf catalogue.  It also proves that the
semantic matrix is the old-vertex part of the restored critical `K15` and
that the restored root has colour-zero degree four.
-/

namespace R4333
namespace UUTP15Base

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportInside61
open ProfileDFourSupportRestoredRootK15
open UUTP15SupportPair
open ProfileDDegreeTenMatrixLeafDataUUU2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## Restrict to four rows and choose the exact ordered supports -/

def fourExtension (branch : Branch) :
    ProfileDFourRowBoundary.FourExtension .uut where
  tail := branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  inside := firstFourInsideColoring (semantic branch)
  rows := fun row =>
    branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row.castSucc
  insideNoMono := firstFourInsideColoring_noMono (semantic branch)
  insideRootForbidden := by
    intro left right hne
    exact firstFourInsideColoring_ne_zero (semantic branch) left right hne
  rowsAdmissible := by
    intro row
    exact branch.toDegreeFlooredFiveExtension.toFiveExtension.rowsAdmissible
      row.castSucc
  rowsPairCompatible := by
    intro left right hne x hbad
    exact branch.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible
      left.castSucc right.castSucc (Fin.castSuccEmb.injective.ne hne) x hbad

noncomputable def canonicalEnumerations (normalized : NormalizedSupportPair) :
    ForeignSupportEnumerations (semantic normalized.branch) where
  firstEmbedding := (support normalized.first).embedding
  firstEmbeddingRange := by
    change (support normalized.first).positions =
      ProfileDFourSupportForeignSupports61.firstForeignOwnSupport
        (semantic normalized.branch)
    exact normalized.firstSupport.symm
  secondEmbedding := (support normalized.second).embedding
  secondEmbeddingRange := by
    change (support normalized.second).positions =
      ProfileDFourSupportForeignSupports61.secondForeignOwnSupport
        (semantic normalized.branch)
    exact normalized.secondSupport.symm

@[simp] theorem canonicalEnumerations_firstEmbedding
    (normalized : NormalizedSupportPair) (p : Fin 5) :
    (canonicalEnumerations normalized).firstEmbedding p =
      (support normalized.first).embedding p := by
  rfl

@[simp] theorem canonicalEnumerations_secondEmbedding
    (normalized : NormalizedSupportPair) (p : Fin 5) :
    (canonicalEnumerations normalized).secondEmbedding p =
      (support normalized.second).embedding p := by
  rfl

@[simp] theorem semantic_toDegreeFlooredFiveExtension (branch : Branch) :
    (semantic branch).toDegreeFlooredFiveExtension =
      branch.toDegreeFlooredFiveExtension := by
  rfl

/-! ## Physical `Fin 50` coordinates -/

/-- The semantic `4|5|5` coordinates before merging them into the literal
`Fin 50` order.  Keeping this as an embedding makes the distinctness proof
structural, rather than an arithmetic proof about the final offsets. -/
noncomputable def physicalCoordinateEmbedding
    (normalized : NormalizedSupportPair) :
    FourFiveFiveCoordinates ↪ Sum (Fin 4) ProfileDRowExtension.TailVertex where
  toFun
    | .inl (.inl free) => .inl free
    | .inl (.inr first) => .inr
        (blockVertex 0 ((support normalized.first).embedding first).val)
    | .inr second => .inr
        (blockVertex 1 ((support normalized.second).embedding second).val)
  inj' := by
    intro left right h
    rcases left with (left | leftSecond)
    · rcases left with (leftFree | leftFirst)
      · rcases right with (right | rightSecond)
        · rcases right with (rightFree | rightFirst)
          · exact congrArg (fun p => Sum.inl (Sum.inl p)) (Sum.inl.inj h)
          · cases h
        · cases h
      · rcases right with (right | rightSecond)
        · rcases right with (rightFree | rightFirst)
          · cases h
          · have hvertex := Sum.inr.inj h
            have hembedding :=
              (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 0)
                hvertex
            exact congrArg (fun p => Sum.inl (Sum.inr p))
              ((support normalized.first).embedding.injective hembedding)
        · have hvertex := Sum.inr.inj h
          exact (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
            0 1 (by decide)
            ((support normalized.first).embedding leftFirst).isLt
            ((support normalized.second).embedding rightSecond).isLt
            hvertex).elim
    · rcases right with (right | rightSecond)
      · rcases right with (rightFree | rightFirst)
        · cases h
        · have hvertex := Sum.inr.inj h
          exact (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
            1 0 (by decide)
            ((support normalized.second).embedding leftSecond).isLt
            ((support normalized.first).embedding rightFirst).isLt
            hvertex).elim
      · have hvertex := Sum.inr.inj h
        have hembedding :=
          (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 1)
            hvertex
        exact congrArg Sum.inr
          ((support normalized.second).embedding.injective hembedding)

/-- `mergeVertex` packaged with its semantic injectivity proof. -/
def physicalMergeEmbedding :
    Sum (Fin 4) ProfileDRowExtension.TailVertex ↪
      ProfileDFourRowCNF.TotalVertex where
  toFun := ProfileDFourRowCNF.mergeVertex
  inj' := by
    intro left right h
    have hsplit := congrArg ProfileDFourRowCNF.splitVertex h
    rcases left with (left | left) <;>
      rcases right with (right | right) <;>
      simpa [ProfileDFourRowCNF.mergeVertex] using hsplit

noncomputable def physicalVertexEmbedding
    (normalized : NormalizedSupportPair) :
    Fin 14 ↪ ProfileDFourRowCNF.TotalVertex :=
  (fourFiveFiveEquiv.symm.toEmbedding).trans
    ((physicalCoordinateEmbedding normalized).trans physicalMergeEmbedding)

noncomputable def physicalVertex (normalized : NormalizedSupportPair)
    (i : Fin 14) : ProfileDFourRowCNF.TotalVertex :=
  physicalVertexEmbedding normalized i

@[simp] theorem physicalVertex_free (normalized : NormalizedSupportPair)
    (p : Fin 4) :
    physicalVertex normalized (freeLabel p) =
      ProfileDFourRowCNF.freeVertex p := by
  simp [physicalVertex, physicalVertexEmbedding,
    physicalCoordinateEmbedding, physicalMergeEmbedding,
    ProfileDFourRowCNF.mergeVertex, freeLabel]

@[simp] theorem physicalVertex_first (normalized : NormalizedSupportPair)
    (p : Fin 5) :
    physicalVertex normalized (firstForeignLabel p) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 0 ((support normalized.first).embedding p).val) := by
  simp [physicalVertex, physicalVertexEmbedding,
    physicalCoordinateEmbedding, physicalMergeEmbedding,
    ProfileDFourRowCNF.mergeVertex, firstForeignLabel]

@[simp] theorem physicalVertex_second (normalized : NormalizedSupportPair)
    (p : Fin 5) :
    physicalVertex normalized (secondForeignLabel p) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 1 ((support normalized.second).embedding p).val) := by
  simp [physicalVertex, physicalVertexEmbedding,
    physicalCoordinateEmbedding, physicalMergeEmbedding,
    ProfileDFourRowCNF.mergeVertex, secondForeignLabel]

@[simp] theorem physicalVertex_freeCoordinate
    (normalized : NormalizedSupportPair) (p : Fin 4) :
    physicalVertex normalized (fourFiveFiveEquiv (.inl (.inl p))) =
      ProfileDFourRowCNF.freeVertex p := by
  simpa [freeLabel] using physicalVertex_free normalized p

@[simp] theorem physicalVertex_firstCoordinate
    (normalized : NormalizedSupportPair) (p : Fin 5) :
    physicalVertex normalized (fourFiveFiveEquiv (.inl (.inr p))) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 0 ((support normalized.first).embedding p).val) := by
  simpa [firstForeignLabel] using physicalVertex_first normalized p

@[simp] theorem physicalVertex_secondCoordinate
    (normalized : NormalizedSupportPair) (p : Fin 5) :
    physicalVertex normalized (fourFiveFiveEquiv (.inr p)) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 1 ((support normalized.second).embedding p).val) := by
  simpa [secondForeignLabel] using physicalVertex_second normalized p

theorem physicalVertex_injective (normalized : NormalizedSupportPair) :
    Function.Injective (physicalVertex normalized) := by
  exact (physicalVertexEmbedding normalized).injective

theorem physicalMatrix_eq_ownNeighborhood
    (normalized : NormalizedSupportPair) (left right : Fin 14) :
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized left) (physicalVertex normalized right) =
      ownNeighborhoodHostColoring (canonicalEnumerations normalized)
        left right := by
  rw [← fourFiveFiveEquiv.apply_symm_apply left,
    ← fourFiveFiveEquiv.apply_symm_apply right]
  generalize fourFiveFiveEquiv.symm left = lc
  generalize fourFiveFiveEquiv.symm right = rc
  rcases lc with (lc | ls)
  · rcases lc with (lf | lfirst)
    · rcases rc with (rc | rs)
      · rcases rc with (rf | rfirst)
        · rw [physicalVertex_freeCoordinate, physicalVertex_freeCoordinate]
          simp [canonicalEnumerations,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            fourExtension, ownNeighborhoodHostColoring,
            pullbackColoring, neighborhoodEmbedding,
            neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
            joinColoring, firstFourInsideColoring]
        · rw [physicalVertex_freeCoordinate, physicalVertex_firstCoordinate]
          simp [canonicalEnumerations,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            fourExtension, ownNeighborhoodHostColoring,
            pullbackColoring, neighborhoodEmbedding,
            neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
            joinColoring]
          rfl
      · rw [physicalVertex_freeCoordinate, physicalVertex_secondCoordinate]
        simp [canonicalEnumerations,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          fourExtension, ownNeighborhoodHostColoring,
          pullbackColoring, neighborhoodEmbedding,
          neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
          joinColoring]
        rfl
    · rcases rc with (rc | rs)
      · rcases rc with (rf | rfirst)
        · rw [physicalVertex_firstCoordinate, physicalVertex_freeCoordinate]
          rw [(ProfileDFourRowCNF.totalColoring
            (fourExtension normalized.branch)).color_symm]
          simp [canonicalEnumerations,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            fourExtension, ownNeighborhoodHostColoring,
            pullbackColoring, neighborhoodEmbedding,
            neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
            joinColoring]
          rfl
        · rw [physicalVertex_firstCoordinate, physicalVertex_firstCoordinate]
          simp [canonicalEnumerations,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            fourExtension, ownNeighborhoodHostColoring,
            pullbackColoring, neighborhoodEmbedding,
            neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
            joinColoring]
          rfl
      · rw [physicalVertex_firstCoordinate, physicalVertex_secondCoordinate]
        simp [canonicalEnumerations,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          fourExtension, ownNeighborhoodHostColoring,
          pullbackColoring, neighborhoodEmbedding,
          neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
          joinColoring]
        rfl
  · rcases rc with (rc | rs)
    · rcases rc with (rf | rfirst)
      · rw [physicalVertex_secondCoordinate, physicalVertex_freeCoordinate]
        rw [(ProfileDFourRowCNF.totalColoring
          (fourExtension normalized.branch)).color_symm]
        simp [canonicalEnumerations,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          fourExtension, ownNeighborhoodHostColoring,
          pullbackColoring, neighborhoodEmbedding,
          neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
          joinColoring]
        rfl
      · rw [physicalVertex_secondCoordinate, physicalVertex_firstCoordinate]
        simp [canonicalEnumerations,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          fourExtension, ownNeighborhoodHostColoring,
          pullbackColoring, neighborhoodEmbedding,
          neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
          joinColoring]
        rfl
    · rw [physicalVertex_secondCoordinate, physicalVertex_secondCoordinate]
      simp [canonicalEnumerations,
        ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
        ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
        fourExtension, ownNeighborhoodHostColoring,
        pullbackColoring, neighborhoodEmbedding,
        neighborhoodEmbeddingOnCoordinates, retainedJoinedColoring,
        joinColoring]
      rfl

/-! ## The restored root has the required `4|5|5` degree split -/

theorem restoredRootHostK15_root_degree_free
    (normalized : NormalizedSupportPair) :
    colorDegree
        (restoredRootHostK15 (canonicalEnumerations normalized))
        0 (Fin.last 14) = 4 := by
  let c := restoredRootHostK15 (canonicalEnumerations normalized)
  let freeVertices : Finset (Fin 15) :=
    Finset.univ.image (fun p : Fin 4 => (freeLabel p).castSucc)
  have hneighborhood : colorNeighborhood c 0 (Fin.last 14) =
      freeVertices := by
    ext x
    induction x using Fin.lastCases with
    | last =>
        simp only [mem_colorNeighborhood]
        constructor
        · rintro ⟨hne, -⟩
          exact (hne rfl).elim
        · intro hmem
          change Fin.last 14 ∈ Finset.univ.image
            (fun p : Fin 4 => (freeLabel p).castSucc) at hmem
          obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem
          exact (Fin.castSucc_ne_last (freeLabel p) hp).elim
    | cast i =>
        rw [← fourFiveFiveEquiv.apply_symm_apply i]
        generalize fourFiveFiveEquiv.symm i = coordinate
        rcases coordinate with (left | second)
        · rcases left with (free | first)
          · simp only [mem_colorNeighborhood]
            constructor
            · intro _
              change (freeLabel free).castSucc ∈ Finset.univ.image
                (fun p : Fin 4 => (freeLabel p).castSucc)
              exact Finset.mem_image.mpr ⟨free, Finset.mem_univ _, rfl⟩
            · intro _
              constructor
              · exact Fin.castSucc_ne_last (freeLabel free)
              · change extendByLast
                    (ownNeighborhoodHostColoring
                      (canonicalEnumerations normalized))
                    (restoredRootHostAttachment
                      (semantic normalized.branch)) 0
                    (Fin.last 14) (freeLabel free).castSucc = 0
                rw [extendByLast_last_old,
                  show restoredRootHostAttachment
                      (semantic normalized.branch) (freeLabel free) = 0 by
                    simpa [freeLabel, freeHostForbiddenColor] using
                      restoredRootHostAttachment_freeCoordinate
                        (semantic normalized.branch) free]
          · simp only [mem_colorNeighborhood]
            constructor
            · rintro ⟨-, hcolor⟩
              change extendByLast
                    (ownNeighborhoodHostColoring
                      (canonicalEnumerations normalized))
                    (restoredRootHostAttachment
                      (semantic normalized.branch)) 0
                    (Fin.last 14) (firstForeignLabel first).castSucc = 0
                at hcolor
              rw [extendByLast_last_old,
                show restoredRootHostAttachment
                    (semantic normalized.branch) (firstForeignLabel first) =
                      firstForeignHostForbiddenColor
                        (semantic normalized.branch) by
                  simpa [firstForeignLabel] using
                    restoredRootHostAttachment_firstForeignCoordinate
                      (semantic normalized.branch) first] at hcolor
              simp [firstForeignHostForbiddenColor] at hcolor
            · intro hmem
              change (firstForeignLabel first).castSucc ∈
                Finset.univ.image
                  (fun p : Fin 4 => (freeLabel p).castSucc) at hmem
              obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
              have hlabel := Fin.castSuccEmb.injective ha
              have hcoordinate := fourFiveFiveEquiv.injective hlabel
              cases hcoordinate
        · simp only [mem_colorNeighborhood]
          constructor
          · rintro ⟨-, hcolor⟩
            change extendByLast
                  (ownNeighborhoodHostColoring
                    (canonicalEnumerations normalized))
                  (restoredRootHostAttachment
                    (semantic normalized.branch)) 0
                  (Fin.last 14) (secondForeignLabel second).castSucc = 0
              at hcolor
            rw [extendByLast_last_old,
              show restoredRootHostAttachment
                  (semantic normalized.branch) (secondForeignLabel second) =
                    secondForeignHostForbiddenColor
                      (semantic normalized.branch) by
                simpa [secondForeignLabel] using
                  restoredRootHostAttachment_secondForeignCoordinate
                    (semantic normalized.branch) second] at hcolor
            simp [secondForeignHostForbiddenColor] at hcolor
          · intro hmem
            change (secondForeignLabel second).castSucc ∈
              Finset.univ.image
                (fun p : Fin 4 => (freeLabel p).castSucc) at hmem
            obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
            have hlabel := Fin.castSuccEmb.injective ha
            have hcoordinate := fourFiveFiveEquiv.injective hlabel
            cases hcoordinate
  change (colorNeighborhood c 0 (Fin.last 14)).card = 4
  rw [hneighborhood]
  change (Finset.univ.image
    (fun p : Fin 4 => (freeLabel p).castSucc)).card = 4
  rw [Finset.card_image_of_injective]
  · simp
  · intro left right h
    apply Fin.castSuccEmb.injective at h
    exact Sum.inl.inj (Sum.inl.inj (fourFiveFiveEquiv.injective h))

#print axioms fourExtension
#print axioms physicalVertex_injective
#print axioms physicalMatrix_eq_ownNeighborhood
#print axioms restoredRootHostK15_root_degree_free

end UUTP15Base
end R4333
