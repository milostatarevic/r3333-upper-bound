import R4333Lean.ProfileDHighOwnForeignC5Skeleton61
import R4333Lean.CriticalK15ColorPreservingClassification
import R4333Lean.CriticalTemplateMaximumSetIntersection

/-!
# Catalogue entrance for a degree-ten profile-D own neighbourhood

Assume the five-free-support branch and a selected endpoint of tail
own-degree ten.  The five retained free vertices and the two saturated
foreign supports form fifteen distinct own-colour neighbours of the selected
endpoint in the retained joined graph.  This file gives that statement an
explicit `Fin 15` labelling, pulls the joined colouring back along the
labelling, deletes the selected endpoint's own colour, and invokes the fully
checked critical `K15` catalogue.

The output retains the three labelled five-sets and transports their three
independence certificates to the catalogued template.  It is therefore a
semantic entrance for a separate classification of labelled partitions; no
finite-search assumption is introduced here.
-/

namespace R4333
namespace ProfileDDegreeTenNeighborhoodCatalogueEntrance61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension
abbrev ThreeC5Skeleton {kind : Kind} (ext : FiveSupportExtension kind) :=
  ProfileDHighOwnForeignC5Skeleton61.ThreeC5Skeleton ext

/-! ## A fixed labelling by three five-sets -/

/-- Coordinates for the free set, first foreign set, and second foreign set. -/
abbrev ThreeFiveCoordinates := (FiveVertex ⊕ FiveVertex) ⊕ FiveVertex

/-- The deterministic equivalence from three consecutive five-sets to
`Fin 15`. -/
def threeFiveEquiv : ThreeFiveCoordinates ≃ Fin 15 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl FiveVertex)).trans
    finSumFinEquiv

def freeLabel (a : FiveVertex) : Fin 15 :=
  threeFiveEquiv (.inl (.inl a))

def firstForeignLabel (a : FiveVertex) : Fin 15 :=
  threeFiveEquiv (.inl (.inr a))

def secondForeignLabel (a : FiveVertex) : Fin 15 :=
  threeFiveEquiv (.inr a)

def freeLabels : Finset (Fin 15) :=
  Finset.univ.image freeLabel

def firstForeignLabels : Finset (Fin 15) :=
  Finset.univ.image firstForeignLabel

def secondForeignLabels : Finset (Fin 15) :=
  Finset.univ.image secondForeignLabel

theorem freeLabel_injective : Function.Injective freeLabel := by
  intro a b hab
  exact Sum.inl.inj (Sum.inl.inj (threeFiveEquiv.injective hab))

theorem firstForeignLabel_injective : Function.Injective firstForeignLabel := by
  intro a b hab
  exact Sum.inr.inj (Sum.inl.inj (threeFiveEquiv.injective hab))

theorem secondForeignLabel_injective :
    Function.Injective secondForeignLabel := by
  intro a b hab
  exact Sum.inr.inj (threeFiveEquiv.injective hab)

@[simp] theorem freeLabels_card : freeLabels.card = 5 := by
  rw [freeLabels, Finset.card_image_of_injective _ freeLabel_injective]
  simp [FiveVertex]

@[simp] theorem firstForeignLabels_card : firstForeignLabels.card = 5 := by
  rw [firstForeignLabels,
    Finset.card_image_of_injective _ firstForeignLabel_injective]
  simp [FiveVertex]

@[simp] theorem secondForeignLabels_card : secondForeignLabels.card = 5 := by
  rw [secondForeignLabels,
    Finset.card_image_of_injective _ secondForeignLabel_injective]
  simp [FiveVertex]

theorem freeLabels_disjoint_firstForeignLabels :
    Disjoint freeLabels firstForeignLabels := by
  rw [Finset.disjoint_left]
  intro x hxFree hxFirst
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hxFree
  obtain ⟨b, _hb, hlabel⟩ := Finset.mem_image.mp hxFirst
  have houter := threeFiveEquiv.injective hlabel.symm
  have hinner : Sum.inl a = Sum.inr b := Sum.inl.inj houter
  cases hinner

theorem freeLabels_disjoint_secondForeignLabels :
    Disjoint freeLabels secondForeignLabels := by
  rw [Finset.disjoint_left]
  intro x hxFree hxSecond
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hxFree
  obtain ⟨b, _hb, hlabel⟩ := Finset.mem_image.mp hxSecond
  have houter := threeFiveEquiv.injective hlabel.symm
  cases houter

theorem firstForeignLabels_disjoint_secondForeignLabels :
    Disjoint firstForeignLabels secondForeignLabels := by
  rw [Finset.disjoint_left]
  intro x hxFirst hxSecond
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hxFirst
  obtain ⟨b, _hb, hlabel⟩ := Finset.mem_image.mp hxSecond
  have houter := threeFiveEquiv.injective hlabel.symm
  cases houter

theorem threeLabelSets_cover :
    (freeLabels ∪ firstForeignLabels) ∪ secondForeignLabels =
      Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  let coordinate := threeFiveEquiv.symm x
  have hcoordinate : threeFiveEquiv coordinate = x :=
    threeFiveEquiv.apply_symm_apply x
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · exact Finset.mem_union_left secondForeignLabels
        (Finset.mem_union_left firstForeignLabels
          (Finset.mem_image.mpr ⟨free, by simp, hcoordinate⟩))
    · exact Finset.mem_union_left secondForeignLabels
        (Finset.mem_union_right freeLabels
          (Finset.mem_image.mpr ⟨first, by simp, hcoordinate⟩))
  · exact Finset.mem_union_right (freeLabels ∪ firstForeignLabels)
      (Finset.mem_image.mpr ⟨second, by simp, hcoordinate⟩)

/-! ## The retained joined graph and its explicit neighbourhood embedding -/

abbrev RetainedJoinedVertex := Sum FiveVertex TailVertex

def retainedJoinedColoring {kind : Kind} (ext : FiveSupportExtension kind) :
    EdgeColoring RetainedJoinedVertex (Fin 4) :=
  joinColoring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rows

theorem retainedJoinedColoring_noMono {kind : Kind}
    (ext : FiveSupportExtension kind) :
    NoMonochromaticTriangle (retainedJoinedColoring ext) := by
  exact (noMono_joinColoring_iff _ _ _).2 ⟨
    ext.toDegreeFlooredFiveExtension.toFiveExtension.insideNoMono,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.noMono,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsAdmissible,
    ext.toDegreeFlooredFiveExtension.toFiveExtension.rowsPairCompatible⟩

def selectedEndpoint {kind : Kind} (ext : FiveSupportExtension kind) :
    RetainedJoinedVertex :=
  .inr (blockVertex ext.block ext.position.val)

/-- An embedding of the three abstract five-sets into the retained graph. -/
noncomputable def neighborhoodEmbeddingOnCoordinates {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    ThreeFiveCoordinates ↪ RetainedJoinedVertex where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr a) => .inr (blockVertex
        (firstForeignBlock ext.block)
        (skeleton.firstForeignCycle.embedding a).val)
    | .inr a => .inr (blockVertex
        (secondForeignBlock ext.block)
        (skeleton.secondForeignCycle.embedding a).val)
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
                    have hab : a = b := Sum.inl.inj hxy
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
                      blockVertex_fixed_injective
                        (firstForeignBlock ext.block) habVertex
                    have hab :=
                      skeleton.firstForeignCycle.embedding.injective habEmbedding
                    subst b
                    rfl
            | inr b =>
                have hvertex := Sum.inr.inj hxy
                exact (blockVertex_ne_of_block_ne
                  (firstForeignBlock ext.block)
                  (secondForeignBlock ext.block)
                  (firstForeignBlock_ne_second ext.block)
                  (skeleton.firstForeignCycle.embedding a).isLt
                  (skeleton.secondForeignCycle.embedding b).isLt
                  hvertex).elim
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
                  (firstForeignBlock_ne_second ext.block).symm
                  (skeleton.secondForeignCycle.embedding a).isLt
                  (skeleton.firstForeignCycle.embedding b).isLt
                  hvertex).elim
        | inr b =>
            have habVertex := Sum.inr.inj hxy
            have habEmbedding :=
              blockVertex_fixed_injective
                (secondForeignBlock ext.block) habVertex
            have hab :=
              skeleton.secondForeignCycle.embedding.injective habEmbedding
            subst b
            rfl

/-- The requested explicit `Fin 15` embedding. -/
noncomputable def neighborhoodEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    Fin 15 ↪ RetainedJoinedVertex :=
  (threeFiveEquiv.symm.toEmbedding).trans
    (neighborhoodEmbeddingOnCoordinates skeleton)

@[simp] theorem neighborhoodEmbedding_freeLabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    neighborhoodEmbedding skeleton (freeLabel a) = .inl a := by
  simp [neighborhoodEmbedding, freeLabel,
    neighborhoodEmbeddingOnCoordinates]

@[simp] theorem neighborhoodEmbedding_firstForeignLabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    neighborhoodEmbedding skeleton (firstForeignLabel a) =
      .inr (blockVertex (firstForeignBlock ext.block)
        (skeleton.firstForeignCycle.embedding a).val) := by
  simp [neighborhoodEmbedding, firstForeignLabel,
    neighborhoodEmbeddingOnCoordinates]

@[simp] theorem neighborhoodEmbedding_secondForeignLabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    neighborhoodEmbedding skeleton (secondForeignLabel a) =
      .inr (blockVertex (secondForeignBlock ext.block)
        (skeleton.secondForeignCycle.embedding a).val) := by
  simp [neighborhoodEmbedding, secondForeignLabel,
    neighborhoodEmbeddingOnCoordinates]

theorem saturatedForeignC5_embedding_mem {kind : Kind}
    {ext : FiveSupportExtension kind} {target : Fin 3}
    (cycle : SaturatedForeignC5 ext target) (a : FiveVertex) :
    cycle.embedding a ∈ foreignOwnSupport ext target := by
  rw [← cycle.embeddingRange]
  exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩

theorem selectedEndpoint_ne_free {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    selectedEndpoint ext ≠ (Sum.inl a : RetainedJoinedVertex) := by
  simp [selectedEndpoint]

theorem selectedEndpoint_ne_firstForeign {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    selectedEndpoint ext ≠
      .inr (blockVertex (firstForeignBlock ext.block)
        (skeleton.firstForeignCycle.embedding a).val) := by
  intro hvertices
  apply blockVertex_ne_of_block_ne ext.block
    (firstForeignBlock ext.block) (firstForeignBlock_ne ext.block).symm
    ext.position.isLt (skeleton.firstForeignCycle.embedding a).isLt
  exact Sum.inr.inj hvertices

theorem selectedEndpoint_ne_secondForeign {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    selectedEndpoint ext ≠
      .inr (blockVertex (secondForeignBlock ext.block)
        (skeleton.secondForeignCycle.embedding a).val) := by
  intro hvertices
  apply blockVertex_ne_of_block_ne ext.block
    (secondForeignBlock ext.block) (secondForeignBlock_ne ext.block).symm
    ext.position.isLt (skeleton.secondForeignCycle.embedding a).isLt
  exact Sum.inr.inj hvertices

theorem selectedEndpoint_color_free {kind : Kind}
    (ext : FiveSupportExtension kind) (a : FiveVertex) :
    retainedJoinedColoring ext (selectedEndpoint ext) (.inl a) =
      blockRootColor ext.block := by
  exact ext.allFiveOwn a

theorem selectedEndpoint_color_firstForeign {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    retainedJoinedColoring ext (selectedEndpoint ext)
      (.inr (blockVertex (firstForeignBlock ext.block)
        (skeleton.firstForeignCycle.embedding a).val)) =
      blockRootColor ext.block := by
  exact (mem_foreignOwnSupport ext (firstForeignBlock ext.block)
    (skeleton.firstForeignCycle.embedding a)).mp
      (saturatedForeignC5_embedding_mem
        skeleton.firstForeignCycle a)

theorem selectedEndpoint_color_secondForeign {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a : FiveVertex) :
    retainedJoinedColoring ext (selectedEndpoint ext)
      (.inr (blockVertex (secondForeignBlock ext.block)
        (skeleton.secondForeignCycle.embedding a).val)) =
      blockRootColor ext.block := by
  exact (mem_foreignOwnSupport ext (secondForeignBlock ext.block)
    (skeleton.secondForeignCycle.embedding a)).mp
      (saturatedForeignC5_embedding_mem
        skeleton.secondForeignCycle a)

theorem selectedEndpoint_ne_neighborhoodEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (i : Fin 15) :
    selectedEndpoint ext ≠ neighborhoodEmbedding skeleton i := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
        using selectedEndpoint_ne_free ext free
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates] using
        selectedEndpoint_ne_firstForeign skeleton first
  · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates] using
      selectedEndpoint_ne_secondForeign skeleton second

theorem selectedEndpoint_color_neighborhoodEmbedding {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (i : Fin 15) :
    retainedJoinedColoring ext (selectedEndpoint ext)
        (neighborhoodEmbedding skeleton i) = blockRootColor ext.block := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with (left | second)
  · rcases left with (free | first)
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates]
        using selectedEndpoint_color_free ext free
    · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates] using
        selectedEndpoint_color_firstForeign skeleton first
  · simpa [neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates] using
      selectedEndpoint_color_secondForeign skeleton second

theorem neighborhoodEmbedding_mem_ownColorNeighborhood {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (i : Fin 15) :
    neighborhoodEmbedding skeleton i ∈
      colorNeighborhood (retainedJoinedColoring ext)
        (blockRootColor ext.block) (selectedEndpoint ext) := by
  exact (mem_colorNeighborhood _ _ _ _).2 ⟨
    (selectedEndpoint_ne_neighborhoodEmbedding skeleton i).symm,
    selectedEndpoint_color_neighborhoodEmbedding skeleton i⟩

/-! ## Pullback to `Fin 15` and deletion of the own colour -/

noncomputable def ownNeighborhoodHostColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring (retainedJoinedColoring ext)
    (neighborhoodEmbedding skeleton)

theorem ownNeighborhoodHostColoring_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    NoMonochromaticTriangle (ownNeighborhoodHostColoring skeleton) := by
  exact noMono_pullback (retainedJoinedColoring ext)
    (neighborhoodEmbedding skeleton)
    (neighborhoodEmbedding skeleton).injective
    (retainedJoinedColoring_noMono ext)

theorem ownNeighborhoodHostColoring_avoids_own {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (u v : Fin 15) (huv : u ≠ v) :
    ownNeighborhoodHostColoring skeleton u v ≠ blockRootColor ext.block := by
  intro hedge
  apply retainedJoinedColoring_noMono ext
    (selectedEndpoint ext)
    (neighborhoodEmbedding skeleton u)
    (neighborhoodEmbedding skeleton v)
  · exact ⟨selectedEndpoint_ne_neighborhoodEmbedding skeleton u,
      selectedEndpoint_ne_neighborhoodEmbedding skeleton v,
      (neighborhoodEmbedding skeleton).injective.ne huv⟩
  · constructor
    · exact (selectedEndpoint_color_neighborhoodEmbedding skeleton u).trans
        (selectedEndpoint_color_neighborhoodEmbedding skeleton v).symm
    · exact (selectedEndpoint_color_neighborhoodEmbedding skeleton v).trans
        hedge.symm

noncomputable def encodedNeighborhoodColoring {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    EdgeColoring (Fin 15) ThreeColor :=
  decodeNonBlockColoring (blockRootColor ext.block)
    (ownNeighborhoodHostColoring skeleton)

theorem encodedNeighborhoodColoring_noMono {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    NoMonochromaticTriangle (encodedNeighborhoodColoring skeleton) := by
  exact decodeNonBlockColoring_noMono (blockRootColor ext.block)
    (ownNeighborhoodHostColoring skeleton)
    (ownNeighborhoodHostColoring_noMono skeleton)
    (ownNeighborhoodHostColoring_avoids_own skeleton)

/-- Direct application of the checked critical catalogue. -/
theorem exists_weakEquiv_k15Template {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    ∃ twisted : Bool,
      Nonempty (WeakColorEquiv (encodedNeighborhoodColoring skeleton)
        (k15Template twisted)) := by
  obtain ⟨template, htemplate, ⟨equiv⟩⟩ :=
    k15CriticalCatalogue_complete.2
      (encodedNeighborhoodColoring skeleton)
      (encodedNeighborhoodColoring_noMono skeleton)
  simp [k15CriticalCatalogue] at htemplate
  rcases htemplate with rfl | rfl
  · exact ⟨false, ⟨by simpa [k15Template] using equiv⟩⟩
  · exact ⟨true, ⟨by simpa [k15Template] using equiv⟩⟩

/-! ## The three labelled independent sets -/

def freeHostForbiddenColor : Fin 4 := 0

def firstForeignHostForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) : Fin 4 :=
  blockRootColor (firstForeignBlock ext.block)

def secondForeignHostForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) : Fin 4 :=
  blockRootColor (secondForeignBlock ext.block)

noncomputable def freeForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) : ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block) freeHostForbiddenColor

noncomputable def firstForeignForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) : ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block)
    (firstForeignHostForbiddenColor ext)

noncomputable def secondForeignForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) : ThreeColor :=
  decodeNonBlockColor (blockRootColor ext.block)
    (secondForeignHostForbiddenColor ext)

theorem blockRootColor_injective : Function.Injective blockRootColor := by
  intro source target hcolor
  exact Fin.succ_injective 3 hcolor

theorem blockRootColor_ne_of_block_ne {source target : Fin 3}
    (hne : source ≠ target) :
    blockRootColor source ≠ blockRootColor target :=
  blockRootColor_injective.ne hne

theorem freeHostForbiddenColor_ne_own {kind : Kind}
    (ext : FiveSupportExtension kind) :
    freeHostForbiddenColor ≠ blockRootColor ext.block := by
  exact (blockRootColor_ne_zero ext.block).symm

theorem firstForeignHostForbiddenColor_ne_own {kind : Kind}
    (ext : FiveSupportExtension kind) :
    firstForeignHostForbiddenColor ext ≠ blockRootColor ext.block := by
  exact blockRootColor_ne_of_block_ne (firstForeignBlock_ne ext.block)

theorem secondForeignHostForbiddenColor_ne_own {kind : Kind}
    (ext : FiveSupportExtension kind) :
    secondForeignHostForbiddenColor ext ≠ blockRootColor ext.block := by
  exact blockRootColor_ne_of_block_ne (secondForeignBlock_ne ext.block)

theorem decodeNonBlockColor_injective_of_ne
    (block q r : Fin 4) (hq : q ≠ block) (hr : r ≠ block)
    (hdecode : decodeNonBlockColor block q =
      decodeNonBlockColor block r) : q = r := by
  have hmapped := congrArg (canonicalPalette block) hdecode
  rw [canonicalPalette_decodeNonBlockColor block q hq,
    canonicalPalette_decodeNonBlockColor block r hr] at hmapped
  exact hmapped

@[simp] theorem ownNeighborhoodHostColoring_freeLabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a b : FiveVertex) :
    ownNeighborhoodHostColoring skeleton (freeLabel a) (freeLabel b) =
      ext.toDegreeFlooredFiveExtension.toFiveExtension.inside a b := by
  simp [ownNeighborhoodHostColoring, pullbackColoring,
    retainedJoinedColoring]

@[simp] theorem ownNeighborhoodHostColoring_firstForeignLabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a b : FiveVertex) :
    ownNeighborhoodHostColoring skeleton
        (firstForeignLabel a) (firstForeignLabel b) =
      tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
        (firstForeignBlock ext.block)
        (skeleton.firstForeignCycle.embedding a)
        (skeleton.firstForeignCycle.embedding b) := by
  simp [ownNeighborhoodHostColoring, pullbackColoring,
    retainedJoinedColoring, tailBlockColoring]

@[simp] theorem ownNeighborhoodHostColoring_secondForeignLabel {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (a b : FiveVertex) :
    ownNeighborhoodHostColoring skeleton
        (secondForeignLabel a) (secondForeignLabel b) =
      tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
        (secondForeignBlock ext.block)
        (skeleton.secondForeignCycle.embedding a)
        (skeleton.secondForeignCycle.embedding b) := by
  simp [ownNeighborhoodHostColoring, pullbackColoring,
    retainedJoinedColoring, tailBlockColoring]

theorem freeLabels_hostIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    IsColorIndependentSet (ownNeighborhoodHostColoring skeleton)
      freeHostForbiddenColor freeLabels := by
  intro x hx y hy hxy
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := fun hab => hxy (congrArg freeLabel hab)
  simpa [freeHostForbiddenColor] using
    ext.toDegreeFlooredFiveExtension.toFiveExtension.insideRootForbidden
      a b hab

theorem firstForeignLabels_hostIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    IsColorIndependentSet (ownNeighborhoodHostColoring skeleton)
      (firstForeignHostForbiddenColor ext) firstForeignLabels := by
  intro x hx y hy hxy
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := fun hab => hxy (congrArg firstForeignLabel hab)
  simpa [firstForeignHostForbiddenColor] using
    tailBlockColoring_ne_root
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
      (firstForeignBlock ext.block)
      (skeleton.firstForeignCycle.embedding a)
      (skeleton.firstForeignCycle.embedding b)
      (skeleton.firstForeignCycle.embedding.injective.ne hab)

theorem secondForeignLabels_hostIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    IsColorIndependentSet (ownNeighborhoodHostColoring skeleton)
      (secondForeignHostForbiddenColor ext) secondForeignLabels := by
  intro x hx y hy hxy
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := fun hab => hxy (congrArg secondForeignLabel hab)
  simpa [secondForeignHostForbiddenColor] using
    tailBlockColoring_ne_root
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
      (secondForeignBlock ext.block)
      (skeleton.secondForeignCycle.embedding a)
      (skeleton.secondForeignCycle.embedding b)
      (skeleton.secondForeignCycle.embedding.injective.ne hab)

theorem hostIndependent_implies_encodedIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext)
    (q : Fin 4) (hq : q ≠ blockRootColor ext.block)
    (S : Finset (Fin 15))
    (hS : IsColorIndependentSet
      (ownNeighborhoodHostColoring skeleton) q S) :
    IsColorIndependentSet (encodedNeighborhoodColoring skeleton)
      (decodeNonBlockColor (blockRootColor ext.block) q) S := by
  intro x hx y hy hxy hencoded
  apply hS x hx y hy hxy
  apply decodeNonBlockColor_injective_of_ne
    (blockRootColor ext.block)
    (ownNeighborhoodHostColoring skeleton x y) q
    (ownNeighborhoodHostColoring_avoids_own skeleton x y hxy) hq
  exact hencoded

theorem freeLabels_encodedIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    IsColorIndependentSet (encodedNeighborhoodColoring skeleton)
      (freeForbiddenColor ext) freeLabels := by
  exact hostIndependent_implies_encodedIndependent skeleton
    freeHostForbiddenColor (freeHostForbiddenColor_ne_own ext)
    freeLabels (freeLabels_hostIndependent skeleton)

theorem firstForeignLabels_encodedIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    IsColorIndependentSet (encodedNeighborhoodColoring skeleton)
      (firstForeignForbiddenColor ext) firstForeignLabels := by
  exact hostIndependent_implies_encodedIndependent skeleton
    (firstForeignHostForbiddenColor ext)
    (firstForeignHostForbiddenColor_ne_own ext)
    firstForeignLabels (firstForeignLabels_hostIndependent skeleton)

theorem secondForeignLabels_encodedIndependent {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    IsColorIndependentSet (encodedNeighborhoodColoring skeleton)
      (secondForeignForbiddenColor ext) secondForeignLabels := by
  exact hostIndependent_implies_encodedIndependent skeleton
    (secondForeignHostForbiddenColor ext)
    (secondForeignHostForbiddenColor_ne_own ext)
    secondForeignLabels (secondForeignLabels_hostIndependent skeleton)

theorem freeForbiddenColor_ne_firstForeignForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) :
    freeForbiddenColor ext ≠ firstForeignForbiddenColor ext := by
  intro hdecode
  have hhost := decodeNonBlockColor_injective_of_ne
    (blockRootColor ext.block)
    freeHostForbiddenColor (firstForeignHostForbiddenColor ext)
    (freeHostForbiddenColor_ne_own ext)
    (firstForeignHostForbiddenColor_ne_own ext) hdecode
  exact (blockRootColor_ne_zero (firstForeignBlock ext.block)) hhost.symm

theorem freeForbiddenColor_ne_secondForeignForbiddenColor {kind : Kind}
    (ext : FiveSupportExtension kind) :
    freeForbiddenColor ext ≠ secondForeignForbiddenColor ext := by
  intro hdecode
  have hhost := decodeNonBlockColor_injective_of_ne
    (blockRootColor ext.block)
    freeHostForbiddenColor (secondForeignHostForbiddenColor ext)
    (freeHostForbiddenColor_ne_own ext)
    (secondForeignHostForbiddenColor_ne_own ext) hdecode
  exact (blockRootColor_ne_zero (secondForeignBlock ext.block)) hhost.symm

theorem firstForeignForbiddenColor_ne_secondForeignForbiddenColor
    {kind : Kind} (ext : FiveSupportExtension kind) :
    firstForeignForbiddenColor ext ≠ secondForeignForbiddenColor ext := by
  intro hdecode
  have hhost := decodeNonBlockColor_injective_of_ne
    (blockRootColor ext.block)
    (firstForeignHostForbiddenColor ext)
    (secondForeignHostForbiddenColor ext)
    (firstForeignHostForbiddenColor_ne_own ext)
    (secondForeignHostForbiddenColor_ne_own ext) hdecode
  exact (blockRootColor_ne_of_block_ne
    (firstForeignBlock_ne_second ext.block)) hhost

theorem forbiddenColors_pairwiseDistinct {kind : Kind}
    (ext : FiveSupportExtension kind) :
    PairwiseDistinct (freeForbiddenColor ext)
      (firstForeignForbiddenColor ext)
      (secondForeignForbiddenColor ext) :=
  ⟨freeForbiddenColor_ne_firstForeignForbiddenColor ext,
    freeForbiddenColor_ne_secondForeignForbiddenColor ext,
    firstForeignForbiddenColor_ne_secondForeignForbiddenColor ext⟩

/-! ## A compositional catalogued-partition package -/

theorem image_disjoint_of_disjoint
    (vertex : Fin 15 ≃ Fin 15) (left right : Finset (Fin 15))
    (hdisjoint : Disjoint left right) :
    Disjoint (left.image vertex) (right.image vertex) := by
  rw [Finset.disjoint_left]
  intro x hxLeft hxRight
  obtain ⟨left0, hleft0, hleftImage⟩ := Finset.mem_image.mp hxLeft
  obtain ⟨right0, hright0, hrightImage⟩ := Finset.mem_image.mp hxRight
  have heq : left0 = right0 := vertex.injective
    (hleftImage.trans hrightImage.symm)
  exact (Finset.disjoint_left.mp hdisjoint) hleft0 (heq ▸ hright0)

theorem threeLabelImages_cover (vertex : Fin 15 ≃ Fin 15) :
    ((freeLabels.image vertex) ∪ (firstForeignLabels.image vertex)) ∪
        (secondForeignLabels.image vertex) = Finset.univ := by
  rw [← Finset.image_union, ← Finset.image_union, threeLabelSets_cover]
  exact Finset.image_univ_equiv vertex

/-- The exact semantic object handed to a labelled-partition classifier.
Its three displayed sets partition the template vertices, each has order
five, and each avoids its corresponding (pairwise distinct) template colour. -/
structure CataloguedDegreeTenNeighborhood {kind : Kind}
    (ext : FiveSupportExtension kind) (skeleton : ThreeC5Skeleton ext) where
  twisted : Bool
  equivalence : WeakColorEquiv
    (encodedNeighborhoodColoring skeleton) (k15Template twisted)
  freeTemplateCard :
    (freeLabels.image equivalence.vertex).card = 5
  firstForeignTemplateCard :
    (firstForeignLabels.image equivalence.vertex).card = 5
  secondForeignTemplateCard :
    (secondForeignLabels.image equivalence.vertex).card = 5
  freeTemplateDisjointFirstForeign :
    Disjoint (freeLabels.image equivalence.vertex)
      (firstForeignLabels.image equivalence.vertex)
  freeTemplateDisjointSecondForeign :
    Disjoint (freeLabels.image equivalence.vertex)
      (secondForeignLabels.image equivalence.vertex)
  firstForeignTemplateDisjointSecondForeign :
    Disjoint (firstForeignLabels.image equivalence.vertex)
      (secondForeignLabels.image equivalence.vertex)
  templateCover :
    ((freeLabels.image equivalence.vertex) ∪
      (firstForeignLabels.image equivalence.vertex)) ∪
        (secondForeignLabels.image equivalence.vertex) = Finset.univ
  templateForbiddenColorsPairwiseDistinct : PairwiseDistinct
    (equivalence.colors (freeForbiddenColor ext))
    (equivalence.colors (firstForeignForbiddenColor ext))
    (equivalence.colors (secondForeignForbiddenColor ext))
  freeTemplateIndependent :
    IsColorIndependentSet (k15Template twisted)
      (equivalence.colors (freeForbiddenColor ext))
      (freeLabels.image equivalence.vertex)
  firstForeignTemplateIndependent :
    IsColorIndependentSet (k15Template twisted)
      (equivalence.colors (firstForeignForbiddenColor ext))
      (firstForeignLabels.image equivalence.vertex)
  secondForeignTemplateIndependent :
    IsColorIndependentSet (k15Template twisted)
      (equivalence.colors (secondForeignForbiddenColor ext))
      (secondForeignLabels.image equivalence.vertex)

theorem exists_cataloguedDegreeTenNeighborhood {kind : Kind}
    {ext : FiveSupportExtension kind} (skeleton : ThreeC5Skeleton ext) :
    Nonempty (CataloguedDegreeTenNeighborhood ext skeleton) := by
  obtain ⟨twisted, ⟨equivalence⟩⟩ :=
    exists_weakEquiv_k15Template skeleton
  refine ⟨{
    twisted := twisted
    equivalence := equivalence
    freeTemplateCard := ?_
    firstForeignTemplateCard := ?_
    secondForeignTemplateCard := ?_
    freeTemplateDisjointFirstForeign := ?_
    freeTemplateDisjointSecondForeign := ?_
    firstForeignTemplateDisjointSecondForeign := ?_
    templateCover := ?_
    templateForbiddenColorsPairwiseDistinct := ?_
    freeTemplateIndependent := ?_
    firstForeignTemplateIndependent := ?_
    secondForeignTemplateIndependent := ?_
  }⟩
  · rw [Finset.card_image_of_injective _ equivalence.vertex.injective]
    exact freeLabels_card
  · rw [Finset.card_image_of_injective _ equivalence.vertex.injective]
    exact firstForeignLabels_card
  · rw [Finset.card_image_of_injective _ equivalence.vertex.injective]
    exact secondForeignLabels_card
  · exact image_disjoint_of_disjoint equivalence.vertex
      freeLabels firstForeignLabels freeLabels_disjoint_firstForeignLabels
  · exact image_disjoint_of_disjoint equivalence.vertex
      freeLabels secondForeignLabels freeLabels_disjoint_secondForeignLabels
  · exact image_disjoint_of_disjoint equivalence.vertex
      firstForeignLabels secondForeignLabels
      firstForeignLabels_disjoint_secondForeignLabels
  · exact threeLabelImages_cover equivalence.vertex
  · exact ⟨equivalence.colors.injective.ne
        (freeForbiddenColor_ne_firstForeignForbiddenColor ext),
      equivalence.colors.injective.ne
        (freeForbiddenColor_ne_secondForeignForbiddenColor ext),
      equivalence.colors.injective.ne
        (firstForeignForbiddenColor_ne_secondForeignForbiddenColor ext)⟩
  · exact equivalence.image_isColorIndependentSet
      (freeForbiddenColor ext) freeLabels
      (freeLabels_encodedIndependent skeleton)
  · exact equivalence.image_isColorIndependentSet
      (firstForeignForbiddenColor ext) firstForeignLabels
      (firstForeignLabels_encodedIndependent skeleton)
  · exact equivalence.image_isColorIndependentSet
      (secondForeignForbiddenColor ext) secondForeignLabels
      (secondForeignLabels_encodedIndependent skeleton)

#print axioms retainedJoinedColoring_noMono
#print axioms neighborhoodEmbedding_mem_ownColorNeighborhood
#print axioms encodedNeighborhoodColoring_noMono
#print axioms exists_weakEquiv_k15Template
#print axioms exists_cataloguedDegreeTenNeighborhood

end ProfileDDegreeTenNeighborhoodCatalogueEntrance61
end R4333
