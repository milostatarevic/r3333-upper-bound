import R4333Lean.ProfileDUUUFourSupportP0OrbitFiniteCoverage61
import R4333Lean.CriticalK15ColorPreservingClassification
import R4333Lean.ProfileDUUUDegreeNineFactorOrbitCoverage61

/-!
# Semantic restored-root orbit bridge for the four-support branch

This file connects an arbitrary normalized semantic branch to the concrete
rooted `K15` candidates checked in the finite orbit certificate.
-/

namespace R4333
namespace ProfileDUUUFourSupportP0SemanticOrbit61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportRestoredRootK15
open ProfileDUUUFourSupportP0SupportPair61
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenEndToEndSemantic61
open ProfileDUUUFourSupportP0RepresentativeData61
open ProfileDUUUFourSupportP0SelectorBridge61
open ProfileDUUUFourSupportP0OrbitData61
open ProfileDUUUDegreeNineFactorOrbitCoverage61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable def canonicalEnumerations (normalized : NormalizedSupportPair) :
    ForeignSupportEnumerations (semantic normalized.branch) where
  firstEmbedding := (canonicalCoordinates normalized.kind).first.embedding
  firstEmbeddingRange := by
    rw [normalized.firstSupport]
    exact canonicalCoordinates_first_positions normalized.kind
  secondEmbedding := (canonicalCoordinates normalized.kind).second.embedding
  secondEmbeddingRange := by
    rw [normalized.secondSupport]
    exact canonicalCoordinates_second_positions normalized.kind

@[simp] theorem canonicalEnumerations_firstEmbedding
    (normalized : NormalizedSupportPair) (p : Fin 5) :
    (canonicalEnumerations normalized).firstEmbedding p =
      u15SupportVertex normalized.kind p := by
  exact canonicalCoordinates_first_embedding_eq_supportVertex
    normalized.kind p

@[simp] theorem canonicalEnumerations_secondEmbedding
    (normalized : NormalizedSupportPair) (p : Fin 5) :
    (canonicalEnumerations normalized).secondEmbedding p =
      u16SupportZeroVertex p := by
  exact canonicalCoordinates_second_embedding_eq_supportVertex
    normalized.kind p

@[simp] theorem physicalVertex_freeCoordinate (kind : SupportKind)
    (p : Fin 4) :
    physicalVertex kind (matrixCoordinateIndex (.inl (.inl p))) =
      ProfileDFourRowCNF.freeVertex p := by
  cases kind <;> fin_cases p <;> rfl

@[simp] theorem physicalVertex_firstCoordinate (kind : SupportKind)
    (p : Fin 5) :
    physicalVertex kind (matrixCoordinateIndex (.inl (.inr p))) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 1 (u15SupportVertex kind p).val) := by
  cases kind <;> fin_cases p <;> rfl

@[simp] theorem physicalVertex_secondCoordinate (kind : SupportKind)
    (p : Fin 5) :
    physicalVertex kind (matrixCoordinateIndex (.inr p)) =
      ProfileDFourRowCNF.tailVertex
        (blockVertex 2 (u16SupportZeroVertex p).val) := by
  cases kind <;> fin_cases p <;> rfl

theorem physicalMatrix_eq_ownNeighborhood
    (normalized : NormalizedSupportPair)
    (left right : Fin 14) :
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized.kind left)
        (physicalVertex normalized.kind right) =
      ownNeighborhoodHostColoring (canonicalEnumerations normalized)
        left right := by
  rw [← matrixCoordinateIndex_coordinate left,
    ← matrixCoordinateIndex_coordinate right]
  generalize matrixCoordinate left = leftCoordinate
  generalize matrixCoordinate right = rightCoordinate
  rcases leftCoordinate with (leftCoordinate | leftSecond)
  · rcases leftCoordinate with (leftFree | leftFirst)
    · rcases rightCoordinate with (rightCoordinate | rightSecond)
      · rcases rightCoordinate with (rightFree | rightFirst)
        · rw [physicalVertex_freeCoordinate,
            physicalVertex_freeCoordinate]
          simp [matrixCoordinateIndex_eq_equiv, fourExtension,
            ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring,
            ProfileDFourSupportInside61.firstFourInsideColoring]
        · rw [physicalVertex_freeCoordinate,
            physicalVertex_firstCoordinate]
          simp [matrixCoordinateIndex_eq_equiv, fourExtension,
            ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring]
          exact (congrArg (fun q : Fin 15 =>
            normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
              leftFree.castSucc (blockVertex 1 q.val))
            (canonicalCoordinates_first_embedding_eq_supportVertex
              normalized.kind rightFirst)).symm
      · rw [physicalVertex_freeCoordinate,
          physicalVertex_secondCoordinate]
        simp [matrixCoordinateIndex_eq_equiv, fourExtension,
          ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring]
        exact (congrArg (fun q : Fin 16 =>
          normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
            leftFree.castSucc (blockVertex 2 q.val))
          (canonicalCoordinates_second_embedding_eq_supportVertex
            normalized.kind rightSecond)).symm
    · rcases rightCoordinate with (rightCoordinate | rightSecond)
      · rcases rightCoordinate with (rightFree | rightFirst)
        · rw [physicalVertex_firstCoordinate,
            physicalVertex_freeCoordinate]
          rw [(ProfileDFourRowCNF.totalColoring
            (fourExtension normalized.branch)).color_symm]
          simp [matrixCoordinateIndex_eq_equiv, fourExtension,
            ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring]
          exact (congrArg (fun q : Fin 15 =>
            normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
              rightFree.castSucc (blockVertex 1 q.val))
            (canonicalCoordinates_first_embedding_eq_supportVertex
              normalized.kind leftFirst)).symm
        · rw [physicalVertex_firstCoordinate,
            physicalVertex_firstCoordinate]
          simp [matrixCoordinateIndex_eq_equiv, fourExtension,
            ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring]
          exact (congrArg₂ (fun q r : Fin 15 =>
            normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
              (blockVertex 1 q.val) (blockVertex 1 r.val))
            (canonicalCoordinates_first_embedding_eq_supportVertex
              normalized.kind leftFirst)
            (canonicalCoordinates_first_embedding_eq_supportVertex
              normalized.kind rightFirst)).symm
      · rw [physicalVertex_firstCoordinate,
          physicalVertex_secondCoordinate]
        simp [matrixCoordinateIndex_eq_equiv, fourExtension,
          ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring]
        exact (congrArg₂ (fun q : Fin 15 => fun r : Fin 16 =>
          normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockVertex 1 q.val) (blockVertex 2 r.val))
          (canonicalCoordinates_first_embedding_eq_supportVertex
            normalized.kind leftFirst)
          (canonicalCoordinates_second_embedding_eq_supportVertex
            normalized.kind rightSecond)).symm
  · rcases rightCoordinate with (rightCoordinate | rightSecond)
    · rcases rightCoordinate with (rightFree | rightFirst)
      · rw [physicalVertex_secondCoordinate,
          physicalVertex_freeCoordinate]
        rw [(ProfileDFourRowCNF.totalColoring
          (fourExtension normalized.branch)).color_symm]
        simp [matrixCoordinateIndex_eq_equiv, fourExtension,
          ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring]
        exact (congrArg (fun q : Fin 16 =>
          normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
            rightFree.castSucc (blockVertex 2 q.val))
          (canonicalCoordinates_second_embedding_eq_supportVertex
            normalized.kind leftSecond)).symm
      · rw [physicalVertex_secondCoordinate,
          physicalVertex_firstCoordinate]
        simp [matrixCoordinateIndex_eq_equiv, fourExtension,
          ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring]
        exact (congrArg₂ (fun q : Fin 16 => fun r : Fin 15 =>
          normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockVertex 2 q.val) (blockVertex 1 r.val))
          (canonicalCoordinates_second_embedding_eq_supportVertex
            normalized.kind leftSecond)
          (canonicalCoordinates_first_embedding_eq_supportVertex
            normalized.kind rightFirst)).symm
    · rw [physicalVertex_secondCoordinate,
        physicalVertex_secondCoordinate]
      simp [matrixCoordinateIndex_eq_equiv, fourExtension,
        ownNeighborhoodHostColoring, pullbackColoring,
        neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
        retainedJoinedColoring, joinColoring]
      exact (congrArg₂ (fun q r : Fin 16 =>
        normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 2 q.val) (blockVertex 2 r.val))
        (canonicalCoordinates_second_embedding_eq_supportVertex
          normalized.kind leftSecond)
        (canonicalCoordinates_second_embedding_eq_supportVertex
          normalized.kind rightSecond)).symm

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
              rw [Finset.mem_image] at hmem
              obtain ⟨a, -, ha⟩ := hmem
              have hval := congrArg Fin.val ha
              simp [freeLabel, firstForeignLabel] at hval
              omega
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
            rw [Finset.mem_image] at hmem
            obtain ⟨a, -, ha⟩ := hmem
            have hval := congrArg Fin.val ha
            simp [freeLabel, secondForeignLabel] at hval
            omega
  change (colorNeighborhood c 0 (Fin.last 14)).card = 4
  rw [hneighborhood]
  change (Finset.univ.image
    (fun p : Fin 4 => (freeLabel p).castSucc)).card = 4
  rw [Finset.card_image_of_injective]
  · simp
  · intro left right h
    apply Fin.castSuccEmb.injective at h
    exact Sum.inl.inj (Sum.inl.inj (fourFiveFiveEquiv.injective h))

theorem rootCase_complete (twisted : Bool) (root : Fin 15)
    (hdegree : colorDegree (k15Template twisted) 0 root = 4) :
    ∃ rootCase : RootCase,
      rootTwisted rootCase = twisted ∧ rootVertex rootCase = root := by
  cases twisted <;> fin_cases root <;> (revert hdegree; decide)

/-! ## Extracting the rooted labelling from a colour-preserving template map -/

theorem colorDegree_zero_eq_of_hostNormalization
    (source : EdgeColoring (Fin 15) (Fin 4))
    (twisted : Bool) (vertex : Fin 15 ≃ Fin 15)
    (hnormalizes : ∀ u v, u ≠ v →
      source (vertex u) (vertex v) =
        canonicalPalette 1 (k15Template twisted u v))
    (u : Fin 15) :
    colorDegree (k15Template twisted) 0 u =
      colorDegree source 0 (vertex u) := by
  change (colorNeighborhood (k15Template twisted) 0 u).card =
    (colorNeighborhood source 0 (vertex u)).card
  exact Finset.card_equiv vertex fun v => by
    simp only [mem_colorNeighborhood]
    constructor
    · rintro ⟨hvu, hcolor⟩
      refine ⟨vertex.injective.ne hvu, ?_⟩
      rw [hnormalizes u v hvu.symm, hcolor]
      decide
    · rintro ⟨hvertex, hcolor⟩
      have hvu : v ≠ u := fun h => hvertex (congrArg vertex h)
      refine ⟨hvu, ?_⟩
      have hencoded := (hnormalizes u v hvu.symm).symm.trans hcolor
      apply SingleRootStarWitness61.canonicalPalette_injective 1
      exact hencoded.trans (by decide)

def sourceFreeVertex (vertex : Fin 15 ≃ Fin 15) (p : Fin 4) : Fin 15 :=
  vertex.symm (freeLabel p).castSucc

def sourceFirstVertex (vertex : Fin 15 ≃ Fin 15) (p : Fin 5) : Fin 15 :=
  vertex.symm (firstForeignLabel p).castSucc

def sourceSecondVertex (vertex : Fin 15 ≃ Fin 15) (p : Fin 5) : Fin 15 :=
  vertex.symm (secondForeignLabel p).castSucc

theorem sourceFreeVertex_injective (vertex : Fin 15 ≃ Fin 15) :
    Function.Injective (sourceFreeVertex vertex) := by
  intro left right h
  apply vertex.symm.injective at h
  apply Fin.castSuccEmb.injective at h
  exact Sum.inl.inj (Sum.inl.inj (fourFiveFiveEquiv.injective h))

theorem sourceFirstVertex_injective (vertex : Fin 15 ≃ Fin 15) :
    Function.Injective (sourceFirstVertex vertex) := by
  intro left right h
  apply vertex.symm.injective at h
  apply Fin.castSuccEmb.injective at h
  have houter : Sum.inr left = Sum.inr right :=
    Sum.inl.inj (fourFiveFiveEquiv.injective h)
  exact Sum.inr.inj houter

theorem sourceSecondVertex_injective (vertex : Fin 15 ≃ Fin 15) :
    Function.Injective (sourceSecondVertex vertex) := by
  intro left right h
  apply vertex.symm.injective at h
  apply Fin.castSuccEmb.injective at h
  exact Sum.inr.inj (fourFiveFiveEquiv.injective h)

theorem freeLabelPermutation_complete_at (index : Fin 24) :
    ∃ action : FreeLabelAction, ∀ p,
      fourPermutationAt index p = freeLabelPermutation action p := by
  revert index
  decide

theorem freeLabelPermutation_complete (perm : Equiv.Perm (Fin 4)) :
    ∃ action : FreeLabelAction, ∀ p,
      perm p = freeLabelPermutation action p := by
  obtain ⟨action, ha⟩ :=
    freeLabelPermutation_complete_at (fourPermutationIndex perm)
  refine ⟨action, ?_⟩
  intro p
  rw [fourPermutationAt_index] at ha
  exact ha p

def FirstCompatibility (kind : SupportKind) (root : RootCase)
    (perm : Equiv.Perm (Fin 5)) : Prop :=
  ∀ left right, left ≠ right →
    canonicalPalette 1
        (k15Template (rootTwisted root)
          (rootFirstGroupVertex root (perm left))
          (rootFirstGroupVertex root (perm right))) =
      canonicalPalette 2
        (k15Template false
          (u15SupportVertex kind left) (u15SupportVertex kind right))

instance (kind : SupportKind) (root : RootCase)
    (perm : Equiv.Perm (Fin 5)) :
    Decidable (FirstCompatibility kind root perm) := by
  unfold FirstCompatibility
  infer_instance

def SecondCompatibility (root : RootCase)
    (perm : Equiv.Perm (Fin 5)) : Prop :=
  ∀ left right, left ≠ right →
    canonicalPalette 1
        (k15Template (rootTwisted root)
          (rootSecondGroupVertex root (perm left))
          (rootSecondGroupVertex root (perm right))) =
      canonicalPalette 3
        (k16Template false
          (u16SupportZeroVertex left) (u16SupportZeroVertex right))

instance (root : RootCase) (perm : Equiv.Perm (Fin 5)) :
    Decidable (SecondCompatibility root perm) := by
  unfold SecondCompatibility
  infer_instance

theorem firstCompatiblePerm_complete_at (kind : SupportKind) (root : RootCase)
    (index : Fin 120)
    (hcompat : FirstCompatibility kind root (fivePermutationAt index)) :
    ∃ action : Fin 10, ∀ p,
      fivePermutationAt index p =
        firstCompatiblePerm kind root action p := by
  cases kind <;> (revert root index hcompat; decide)

theorem firstCompatiblePerm_complete (kind : SupportKind) (root : RootCase)
    (perm : Equiv.Perm (Fin 5)) (hcompat : FirstCompatibility kind root perm) :
    ∃ action : Fin 10, ∀ p,
      perm p = firstCompatiblePerm kind root action p := by
  have hcompatAt : FirstCompatibility kind root
      (fivePermutationAt (fivePermutationIndex perm)) := by
    simpa only [fivePermutationAt_index] using hcompat
  obtain ⟨action, ha⟩ := firstCompatiblePerm_complete_at kind root
    (fivePermutationIndex perm) hcompatAt
  refine ⟨action, ?_⟩
  intro p
  rw [fivePermutationAt_index] at ha
  exact ha p

theorem secondCompatiblePerm_complete_at (root : RootCase)
    (index : Fin 120)
    (hcompat : SecondCompatibility root (fivePermutationAt index)) :
    ∃ action : Fin 10, ∀ p,
      fivePermutationAt index p = secondCompatiblePerm root action p := by
  revert root index hcompat
  decide

theorem secondCompatiblePerm_complete (root : RootCase)
    (perm : Equiv.Perm (Fin 5)) (hcompat : SecondCompatibility root perm) :
    ∃ action : Fin 10, ∀ p,
      perm p = secondCompatiblePerm root action p := by
  have hcompatAt : SecondCompatibility root
      (fivePermutationAt (fivePermutationIndex perm)) := by
    simpa only [fivePermutationAt_index] using hcompat
  obtain ⟨action, ha⟩ := secondCompatiblePerm_complete_at root
    (fivePermutationIndex perm) hcompatAt
  refine ⟨action, ?_⟩
  intro p
  rw [fivePermutationAt_index] at ha
  exact ha p

#print axioms restoredRootHostK15_root_degree_free
#print axioms rootCase_complete
#print axioms freeLabelPermutation_complete_at
#print axioms freeLabelPermutation_complete
#print axioms firstCompatiblePerm_complete_at
#print axioms firstCompatiblePerm_complete
#print axioms secondCompatiblePerm_complete_at
#print axioms secondCompatiblePerm_complete

end ProfileDUUUFourSupportP0SemanticOrbit61
end R4333
