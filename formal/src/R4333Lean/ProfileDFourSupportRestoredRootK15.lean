import R4333Lean.ProfileDFourSupportForeignSupports61
import R4333Lean.CriticalK15ColorPreservingClassification
import R4333Lean.CriticalCatalogues

/-!
# Restored-root K15 in the profile-D four-support branch

For a four-support endpoint of exact tail own-degree ten, the first four
retained vertices and the two exact foreign five-supports are fourteen
distinct own-colour neighbours.  Restoring the deleted global root gives a
triangle-free host-colour `K15` avoiding the selected endpoint's own colour.
After deleting that colour, the checked critical catalogue places the result
in one of the two canonical `K15` templates.

The construction is entirely semantic.  In particular, the only finite
classification invoked here is the already checked `k15CriticalCatalogue`.
-/

namespace R4333
namespace ProfileDFourSupportRestoredRootK15

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportInside61
open ProfileDFourSupportForeignSupports61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FourVertex := Fin 4
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FourSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension

/-! ## Exact enumerations of the two foreign five-supports -/

/-- Enumerations of both exact foreign own-colour supports. -/
structure ForeignSupportEnumerations {kind : Kind}
    (ext : FourSupportExtension kind) where
  firstEmbedding :
    FiveVertex ↪ Fin (blockSize (firstForeignBlock ext.block))
  firstEmbeddingRange :
    Finset.univ.image firstEmbedding = firstForeignOwnSupport ext
  secondEmbedding :
    FiveVertex ↪ Fin (blockSize (secondForeignBlock ext.block))
  secondEmbeddingRange :
    Finset.univ.image secondEmbedding = secondForeignOwnSupport ext

private theorem exists_fiveEmbedding_of_card_eq
    {n : Nat} (support : Finset (Fin n)) (hcard : support.card = 5) :
    ∃ embedding : FiveVertex ↪ Fin n,
      Finset.univ.image embedding = support := by
  classical
  have hcardLe : Fintype.card FiveVertex ≤ support.card := by
    simp [FiveVertex, hcard]
  obtain ⟨embedding, hembedding⟩ :=
    Function.Embedding.exists_of_card_le_finset hcardLe
  have hmem (a : FiveVertex) : embedding a ∈ support :=
    hembedding ⟨a, rfl⟩
  refine ⟨embedding, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    exact hmem a
  · rw [hcard]
    rw [Finset.card_image_of_injective _ embedding.injective]
    simp [FiveVertex]

theorem exists_foreignSupportEnumerations {kind : Kind}
    (ext : FourSupportExtension kind) :
    Nonempty (ForeignSupportEnumerations ext) := by
  classical
  obtain ⟨firstEmbedding, hfirst⟩ :=
    exists_fiveEmbedding_of_card_eq (firstForeignOwnSupport ext)
      (firstForeignOwnSupport_card_eq_five ext)
  obtain ⟨secondEmbedding, hsecond⟩ :=
    exists_fiveEmbedding_of_card_eq (secondForeignOwnSupport ext)
      (secondForeignOwnSupport_card_eq_five ext)
  exact ⟨{
    firstEmbedding := firstEmbedding
    firstEmbeddingRange := hfirst
    secondEmbedding := secondEmbedding
    secondEmbeddingRange := hsecond
  }⟩

theorem firstEmbedding_mem {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    enumerations.firstEmbedding a ∈ firstForeignOwnSupport ext := by
  rw [← enumerations.firstEmbeddingRange]
  exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩

theorem secondEmbedding_mem {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    enumerations.secondEmbedding a ∈ secondForeignOwnSupport ext := by
  rw [← enumerations.secondEmbeddingRange]
  exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩

/-! ## Four-plus-five-plus-five labelling and neighbourhood embedding -/

abbrev FourFiveFiveCoordinates :=
  (FourVertex ⊕ FiveVertex) ⊕ FiveVertex

def fourFiveFiveEquiv : FourFiveFiveCoordinates ≃ Fin 14 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl FiveVertex)).trans
    finSumFinEquiv

def freeLabel (a : FourVertex) : Fin 14 :=
  fourFiveFiveEquiv (.inl (.inl a))

def firstForeignLabel (a : FiveVertex) : Fin 14 :=
  fourFiveFiveEquiv (.inl (.inr a))

def secondForeignLabel (a : FiveVertex) : Fin 14 :=
  fourFiveFiveEquiv (.inr a)

abbrev RetainedJoinedVertex := Sum FiveVertex TailVertex

def retainedJoinedColoring {kind : Kind}
    (ext : FourSupportExtension kind) :
    EdgeColoring RetainedJoinedVertex (Fin 4) :=
  joinColoring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rows

theorem retainedJoinedColoring_noMono {kind : Kind}
    (ext : FourSupportExtension kind) :
    NoMonochromaticTriangle (retainedJoinedColoring ext) := by
  exact (noMono_joinColoring_iff _ _ _).2 ⟨
    ext.toDegreeFlooredFiveExtension.toFiveExtension.insideNoMono,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.noMono,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsAdmissible,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible⟩

def selectedEndpoint {kind : Kind} (ext : FourSupportExtension kind) :
    RetainedJoinedVertex :=
  .inr (blockVertex ext.block ext.position.val)

noncomputable def neighborhoodEmbeddingOnCoordinates {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    FourFiveFiveCoordinates ↪ RetainedJoinedVertex where
  toFun
    | .inl (.inl a) => .inl a.castSucc
    | .inl (.inr a) => .inr (blockVertex
        (firstForeignBlock ext.block)
        (enumerations.firstEmbedding a).val)
    | .inr a => .inr (blockVertex
        (secondForeignBlock ext.block)
        (enumerations.secondEmbedding a).val)
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
                    have hab : a.castSucc = b.castSucc := Sum.inl.inj hxy
                    exact congrArg Sum.inl (congrArg Sum.inl
                      (Fin.castSuccEmb.injective hab))
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
                      (firstForeignBlock ext.block) habVertex
                    have hab := enumerations.firstEmbedding.injective
                      habEmbedding
                    subst b
                    rfl
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (blockVertex_ne_of_block_ne
                  (firstForeignBlock ext.block)
                  (secondForeignBlock ext.block)
                  (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne_second
                    ext.block)
                  (enumerations.firstEmbedding a).isLt
                  (enumerations.secondEmbedding b).isLt hvertex).elim
    | inr a =>
        cases y with
        | inl y =>
            cases y with
            | inl b => cases hxy
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (blockVertex_ne_of_block_ne
                  (secondForeignBlock ext.block)
                  (firstForeignBlock ext.block)
                  (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne_second
                    ext.block).symm
                  (enumerations.secondEmbedding a).isLt
                  (enumerations.firstEmbedding b).isLt hvertex).elim
        | inr b =>
            have habVertex := Sum.inr.inj hxy
            have habEmbedding := blockVertex_fixed_injective
              (secondForeignBlock ext.block) habVertex
            have hab := enumerations.secondEmbedding.injective habEmbedding
            subst b
            rfl

noncomputable def neighborhoodEmbedding {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    Fin 14 ↪ RetainedJoinedVertex :=
  (fourFiveFiveEquiv.symm.toEmbedding).trans
    (neighborhoodEmbeddingOnCoordinates enumerations)

@[simp] theorem neighborhoodEmbedding_freeLabel {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FourVertex) :
    neighborhoodEmbedding enumerations (freeLabel a) = .inl a.castSucc := by
  simp [neighborhoodEmbedding, freeLabel,
    neighborhoodEmbeddingOnCoordinates]

@[simp] theorem neighborhoodEmbedding_firstForeignLabel {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    neighborhoodEmbedding enumerations (firstForeignLabel a) =
      .inr (blockVertex (firstForeignBlock ext.block)
        (enumerations.firstEmbedding a).val) := by
  simp [neighborhoodEmbedding, firstForeignLabel,
    neighborhoodEmbeddingOnCoordinates]

@[simp] theorem neighborhoodEmbedding_secondForeignLabel {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    neighborhoodEmbedding enumerations (secondForeignLabel a) =
      .inr (blockVertex (secondForeignBlock ext.block)
        (enumerations.secondEmbedding a).val) := by
  simp [neighborhoodEmbedding, secondForeignLabel,
    neighborhoodEmbeddingOnCoordinates]

/-! ## The fourteen vertices are own-colour neighbours -/

theorem selectedEndpoint_ne_free {kind : Kind}
    (ext : FourSupportExtension kind) (a : FourVertex) :
    selectedEndpoint ext ≠
      (Sum.inl a.castSucc : RetainedJoinedVertex) := by
  simp [selectedEndpoint]

theorem selectedEndpoint_ne_firstForeign {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    selectedEndpoint ext ≠
      .inr (blockVertex (firstForeignBlock ext.block)
        (enumerations.firstEmbedding a).val) := by
  intro hvertices
  apply blockVertex_ne_of_block_ne ext.block
    (firstForeignBlock ext.block)
    (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne ext.block).symm
    ext.position.isLt (enumerations.firstEmbedding a).isLt
  exact Sum.inr.inj hvertices

theorem selectedEndpoint_ne_secondForeign {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    selectedEndpoint ext ≠
      .inr (blockVertex (secondForeignBlock ext.block)
        (enumerations.secondEmbedding a).val) := by
  intro hvertices
  apply blockVertex_ne_of_block_ne ext.block
    (secondForeignBlock ext.block)
    (ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock_ne ext.block).symm
    ext.position.isLt (enumerations.secondEmbedding a).isLt
  exact Sum.inr.inj hvertices

theorem selectedEndpoint_color_free {kind : Kind}
    (ext : FourSupportExtension kind) (a : FourVertex) :
    retainedJoinedColoring ext (selectedEndpoint ext)
        (.inl a.castSucc) = blockRootColor ext.block := by
  exact ext.firstFourOwn a

theorem selectedEndpoint_color_firstForeign {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    retainedJoinedColoring ext (selectedEndpoint ext)
        (.inr (blockVertex (firstForeignBlock ext.block)
          (enumerations.firstEmbedding a).val)) =
      blockRootColor ext.block := by
  exact (mem_foreignOwnSupport ext (firstForeignBlock ext.block)
    (enumerations.firstEmbedding a)).mp (by
      simpa [firstForeignOwnSupport] using
        firstEmbedding_mem enumerations a)

theorem selectedEndpoint_color_secondForeign {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (a : FiveVertex) :
    retainedJoinedColoring ext (selectedEndpoint ext)
        (.inr (blockVertex (secondForeignBlock ext.block)
          (enumerations.secondEmbedding a).val)) =
      blockRootColor ext.block := by
  exact (mem_foreignOwnSupport ext (secondForeignBlock ext.block)
    (enumerations.secondEmbedding a)).mp (by
      simpa [secondForeignOwnSupport] using
        secondEmbedding_mem enumerations a)

theorem selectedEndpoint_ne_neighborhoodEmbedding {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (i : Fin 14) :
    selectedEndpoint ext ≠ neighborhoodEmbedding enumerations i := by
  rw [← fourFiveFiveEquiv.apply_symm_apply i]
  generalize fourFiveFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
        using selectedEndpoint_ne_free ext free
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
        using selectedEndpoint_ne_firstForeign enumerations first
  · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
      using selectedEndpoint_ne_secondForeign enumerations second

theorem selectedEndpoint_color_neighborhoodEmbedding {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) (i : Fin 14) :
    retainedJoinedColoring ext (selectedEndpoint ext)
        (neighborhoodEmbedding enumerations i) =
      blockRootColor ext.block := by
  rw [← fourFiveFiveEquiv.apply_symm_apply i]
  generalize fourFiveFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
        using selectedEndpoint_color_free ext free
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
        using selectedEndpoint_color_firstForeign enumerations first
  · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
      using selectedEndpoint_color_secondForeign enumerations second

/-! ## Pullback to the fourteen old vertices -/

noncomputable def ownNeighborhoodHostColoring {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    EdgeColoring (Fin 14) (Fin 4) :=
  pullbackColoring (retainedJoinedColoring ext)
    (neighborhoodEmbedding enumerations)

theorem ownNeighborhoodHostColoring_noMono {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    NoMonochromaticTriangle
      (ownNeighborhoodHostColoring enumerations) := by
  exact noMono_pullback (retainedJoinedColoring ext)
    (neighborhoodEmbedding enumerations)
    (neighborhoodEmbedding enumerations).injective
    (retainedJoinedColoring_noMono ext)

theorem ownNeighborhoodHostColoring_avoids_own {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext)
    (u v : Fin 14) (huv : u ≠ v) :
    ownNeighborhoodHostColoring enumerations u v ≠
      blockRootColor ext.block := by
  intro hedge
  apply retainedJoinedColoring_noMono ext
    (selectedEndpoint ext)
    (neighborhoodEmbedding enumerations u)
    (neighborhoodEmbedding enumerations v)
  · exact ⟨selectedEndpoint_ne_neighborhoodEmbedding enumerations u,
      selectedEndpoint_ne_neighborhoodEmbedding enumerations v,
      (neighborhoodEmbedding enumerations).injective.ne huv⟩
  · constructor
    · exact (selectedEndpoint_color_neighborhoodEmbedding
        enumerations u).trans
        (selectedEndpoint_color_neighborhoodEmbedding
          enumerations v).symm
    · exact (selectedEndpoint_color_neighborhoodEmbedding
        enumerations v).trans hedge.symm

@[simp] theorem ownNeighborhoodHostColoring_freeCoordinate {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext)
    (a b : FourVertex) :
    ownNeighborhoodHostColoring enumerations
        (fourFiveFiveEquiv (.inl (.inl a)))
        (fourFiveFiveEquiv (.inl (.inl b))) =
      firstFourInsideColoring ext a b := by
  simp [ownNeighborhoodHostColoring, pullbackColoring,
    neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
    retainedJoinedColoring, firstFourInsideColoring]

@[simp] theorem ownNeighborhoodHostColoring_firstForeignCoordinate
    {kind : Kind} {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext)
    (a b : FiveVertex) :
    ownNeighborhoodHostColoring enumerations
        (fourFiveFiveEquiv (.inl (.inr a)))
        (fourFiveFiveEquiv (.inl (.inr b))) =
      ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
        (firstForeignBlock ext.block)
        (enumerations.firstEmbedding a)
        (enumerations.firstEmbedding b) := by
  simp [ownNeighborhoodHostColoring, pullbackColoring,
    neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
    retainedJoinedColoring,
    ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring]

@[simp] theorem ownNeighborhoodHostColoring_secondForeignCoordinate
    {kind : Kind} {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext)
    (a b : FiveVertex) :
    ownNeighborhoodHostColoring enumerations
        (fourFiveFiveEquiv (.inr a))
        (fourFiveFiveEquiv (.inr b)) =
      ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
        (secondForeignBlock ext.block)
        (enumerations.secondEmbedding a)
        (enumerations.secondEmbedding b) := by
  simp [ownNeighborhoodHostColoring, pullbackColoring,
    neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
    retainedJoinedColoring,
    ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring]

/-! ## Restoring the deleted global root -/

def freeHostForbiddenColor : Fin 4 := 0

def firstForeignHostForbiddenColor {kind : Kind}
    (ext : FourSupportExtension kind) : Fin 4 :=
  blockRootColor (firstForeignBlock ext.block)

def secondForeignHostForbiddenColor {kind : Kind}
    (ext : FourSupportExtension kind) : Fin 4 :=
  blockRootColor (secondForeignBlock ext.block)

/-- The root sees the four free support rows in colour zero and each
foreign support in that foreign block's root colour. -/
def restoredRootHostAttachment {kind : Kind}
    (ext : FourSupportExtension kind) (i : Fin 14) : Fin 4 :=
  match fourFiveFiveEquiv.symm i with
  | .inl (.inl _) => freeHostForbiddenColor
  | .inl (.inr _) => firstForeignHostForbiddenColor ext
  | .inr _ => secondForeignHostForbiddenColor ext

@[simp] theorem restoredRootHostAttachment_freeCoordinate {kind : Kind}
    (ext : FourSupportExtension kind) (a : FourVertex) :
    restoredRootHostAttachment ext
        (fourFiveFiveEquiv (.inl (.inl a))) =
      freeHostForbiddenColor := by
  simp [restoredRootHostAttachment]

@[simp] theorem restoredRootHostAttachment_firstForeignCoordinate
    {kind : Kind} (ext : FourSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext
        (fourFiveFiveEquiv (.inl (.inr a))) =
      firstForeignHostForbiddenColor ext := by
  simp [restoredRootHostAttachment]

@[simp] theorem restoredRootHostAttachment_secondForeignCoordinate
    {kind : Kind} (ext : FourSupportExtension kind) (a : FiveVertex) :
    restoredRootHostAttachment ext (fourFiveFiveEquiv (.inr a)) =
      secondForeignHostForbiddenColor ext := by
  simp [restoredRootHostAttachment]

theorem blockRootColor_injective : Function.Injective blockRootColor := by
  intro source target hcolor
  exact Fin.succ_injective 3 hcolor

theorem blockRootColor_ne_of_block_ne {source target : Fin 3}
    (hne : source ≠ target) :
    blockRootColor source ≠ blockRootColor target :=
  blockRootColor_injective.ne hne

theorem freeHostForbiddenColor_ne_firstForeignHostForbiddenColor
    {kind : Kind} (ext : FourSupportExtension kind) :
    freeHostForbiddenColor ≠ firstForeignHostForbiddenColor ext := by
  exact fun h =>
    (blockRootColor_ne_zero (firstForeignBlock ext.block)) h.symm

theorem freeHostForbiddenColor_ne_secondForeignHostForbiddenColor
    {kind : Kind} (ext : FourSupportExtension kind) :
    freeHostForbiddenColor ≠ secondForeignHostForbiddenColor ext := by
  exact fun h =>
    (blockRootColor_ne_zero (secondForeignBlock ext.block)) h.symm

theorem firstForeignHostForbiddenColor_ne_secondForeignHostForbiddenColor
    {kind : Kind} (ext : FourSupportExtension kind) :
    firstForeignHostForbiddenColor ext ≠
      secondForeignHostForbiddenColor ext := by
  exact blockRootColor_ne_of_block_ne
    (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne_second
      ext.block)

theorem freeHostForbiddenColor_ne_own {kind : Kind}
    (ext : FourSupportExtension kind) :
    freeHostForbiddenColor ≠ blockRootColor ext.block := by
  exact (blockRootColor_ne_zero ext.block).symm

theorem firstForeignHostForbiddenColor_ne_own {kind : Kind}
    (ext : FourSupportExtension kind) :
    firstForeignHostForbiddenColor ext ≠ blockRootColor ext.block := by
  exact blockRootColor_ne_of_block_ne
    (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne ext.block)

theorem secondForeignHostForbiddenColor_ne_own {kind : Kind}
    (ext : FourSupportExtension kind) :
    secondForeignHostForbiddenColor ext ≠ blockRootColor ext.block := by
  exact blockRootColor_ne_of_block_ne
    (ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock_ne ext.block)

/-- Equal restored-root colours can occur only within one of the three
groups, and each such group avoids its root-attachment colour internally. -/
theorem restoredRootHostAttachment_compatible {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext)
    {u v : Fin 14} (huv : u ≠ v)
    (hattachment : restoredRootHostAttachment ext u =
      restoredRootHostAttachment ext v) :
    ownNeighborhoodHostColoring enumerations u v ≠
      restoredRootHostAttachment ext u := by
  let cu := fourFiveFiveEquiv.symm u
  let cv := fourFiveFiveEquiv.symm v
  have hu : u = fourFiveFiveEquiv cu :=
    (fourFiveFiveEquiv.apply_symm_apply u).symm
  have hv : v = fourFiveFiveEquiv cv :=
    (fourFiveFiveEquiv.apply_symm_apply v).symm
  rw [hu, hv] at huv hattachment ⊢
  rcases cu with (left | second)
  · rcases left with (free | first)
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · have hfree : free ≠ free' := by
            intro h
            subst free'
            exact huv rfl
          simpa only [restoredRootHostAttachment_freeCoordinate,
            ownNeighborhoodHostColoring_freeCoordinate,
            freeHostForbiddenColor] using
              firstFourInsideColoring_ne_zero ext free free' hfree
        · exact (freeHostForbiddenColor_ne_firstForeignHostForbiddenColor
            ext (by simpa using hattachment)).elim
      · exact (freeHostForbiddenColor_ne_secondForeignHostForbiddenColor
          ext (by simpa using hattachment)).elim
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · exact (freeHostForbiddenColor_ne_firstForeignHostForbiddenColor
            ext (by simpa using hattachment.symm)).elim
        · have hfirst : first ≠ first' := by
            intro h
            subst first'
            exact huv rfl
          simpa only [restoredRootHostAttachment_firstForeignCoordinate,
            ownNeighborhoodHostColoring_firstForeignCoordinate,
            firstForeignHostForbiddenColor] using
              ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring_ne_root
                ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
                (firstForeignBlock ext.block)
                (enumerations.firstEmbedding first)
                (enumerations.firstEmbedding first')
                (enumerations.firstEmbedding.injective.ne hfirst)
      · exact
          (firstForeignHostForbiddenColor_ne_secondForeignHostForbiddenColor
            ext (by simpa using hattachment)).elim
  · rcases cv with (right | second')
    · rcases right with (free' | first')
      · exact (freeHostForbiddenColor_ne_secondForeignHostForbiddenColor
          ext (by simpa using hattachment.symm)).elim
      · exact
          (firstForeignHostForbiddenColor_ne_secondForeignHostForbiddenColor
            ext (by simpa using hattachment.symm)).elim
    · have hsecond : second ≠ second' := by
          intro h
          subst second'
          exact huv rfl
      simpa only [restoredRootHostAttachment_secondForeignCoordinate,
        ownNeighborhoodHostColoring_secondForeignCoordinate,
        secondForeignHostForbiddenColor] using
          ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring_ne_root
            ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
            (secondForeignBlock ext.block)
            (enumerations.secondEmbedding second)
            (enumerations.secondEmbedding second')
            (enumerations.secondEmbedding.injective.ne hsecond)

noncomputable def restoredRootHostK15 {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    EdgeColoring (Fin 15) (Fin 4) :=
  extendByLast (ownNeighborhoodHostColoring enumerations)
    (restoredRootHostAttachment ext) 0

theorem restoredRootHostK15_noMono {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    NoMonochromaticTriangle (restoredRootHostK15 enumerations) := by
  exact noMono_extendByLast
    (ownNeighborhoodHostColoring enumerations)
    (ownNeighborhoodHostColoring_noMono enumerations)
    (restoredRootHostAttachment ext) 0
    (fun _ _ huv hattachment =>
      restoredRootHostAttachment_compatible enumerations huv hattachment)

theorem restoredRootHostAttachment_ne_own {kind : Kind}
    (ext : FourSupportExtension kind) (i : Fin 14) :
    restoredRootHostAttachment ext i ≠ blockRootColor ext.block := by
  rw [← fourFiveFiveEquiv.apply_symm_apply i]
  generalize fourFiveFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · simpa using freeHostForbiddenColor_ne_own ext
    · simpa using firstForeignHostForbiddenColor_ne_own ext
  · simpa using secondForeignHostForbiddenColor_ne_own ext

theorem restoredRootHostK15_avoids_own {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext)
    (u v : Fin 15) (huv : u ≠ v) :
    restoredRootHostK15 enumerations u v ≠
      blockRootColor ext.block := by
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last => exact (huv rfl).elim
      | cast j =>
          change extendByLast (ownNeighborhoodHostColoring enumerations)
              (restoredRootHostAttachment ext) 0
              (Fin.last 14) j.castSucc ≠ _
          rw [extendByLast_last_old]
          exact restoredRootHostAttachment_ne_own ext j
  | cast i =>
      induction v using Fin.lastCases with
      | last =>
          change extendByLast (ownNeighborhoodHostColoring enumerations)
              (restoredRootHostAttachment ext) 0
              i.castSucc (Fin.last 14) ≠ _
          rw [extendByLast_old_last]
          exact restoredRootHostAttachment_ne_own ext i
      | cast j =>
          change extendByLast (ownNeighborhoodHostColoring enumerations)
              (restoredRootHostAttachment ext) 0
              i.castSucc j.castSucc ≠ _
          rw [extendByLast_old_old]
          apply ownNeighborhoodHostColoring_avoids_own enumerations i j
          intro hij
          apply huv
          simp [hij]

/-! ## Deleting the own colour and entering the checked K15 catalogue -/

noncomputable def restoredRootDecodedK15 {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    EdgeColoring (Fin 15) ThreeColor :=
  decodeNonBlockColoring (blockRootColor ext.block)
    (restoredRootHostK15 enumerations)

theorem restoredRootDecodedK15_noMono {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    NoMonochromaticTriangle
      (restoredRootDecodedK15 enumerations) := by
  exact decodeNonBlockColoring_noMono (blockRootColor ext.block)
    (restoredRootHostK15 enumerations)
    (restoredRootHostK15_noMono enumerations)
    (restoredRootHostK15_avoids_own enumerations)

/-- The restored-root colouring is one of the two fully checked critical
three-colour `K15` templates, up to independent vertex and colour relabelling. -/
theorem exists_weakEquiv_restoredRoot_k15Template {kind : Kind}
    {ext : FourSupportExtension kind}
    (enumerations : ForeignSupportEnumerations ext) :
    ∃ twisted : Bool, Nonempty
      (WeakColorEquiv (restoredRootDecodedK15 enumerations)
        (k15Template twisted)) := by
  obtain ⟨template, htemplate, ⟨equivalence⟩⟩ :=
    k15CriticalCatalogue_complete.2
      (restoredRootDecodedK15 enumerations)
      (restoredRootDecodedK15_noMono enumerations)
  simp [k15CriticalCatalogue] at htemplate
  rcases htemplate with rfl | rfl
  · exact ⟨false, ⟨by simpa [k15Template] using equivalence⟩⟩
  · exact ⟨true, ⟨by simpa [k15Template] using equivalence⟩⟩

/-- Existential form requiring only the original four-support extension. -/
theorem exists_catalogued_restoredRootK15 {kind : Kind}
    (ext : FourSupportExtension kind) :
    ∃ enumerations : ForeignSupportEnumerations ext,
      ∃ twisted : Bool, Nonempty
        (WeakColorEquiv (restoredRootDecodedK15 enumerations)
          (k15Template twisted)) := by
  obtain ⟨enumerations⟩ := exists_foreignSupportEnumerations ext
  exact ⟨enumerations,
    exists_weakEquiv_restoredRoot_k15Template enumerations⟩

#print axioms exists_foreignSupportEnumerations
#print axioms restoredRootHostK15_noMono
#print axioms restoredRootHostK15_avoids_own
#print axioms restoredRootDecodedK15_noMono
#print axioms exists_weakEquiv_restoredRoot_k15Template
#print axioms exists_catalogued_restoredRootK15

end ProfileDFourSupportRestoredRootK15
end R4333
