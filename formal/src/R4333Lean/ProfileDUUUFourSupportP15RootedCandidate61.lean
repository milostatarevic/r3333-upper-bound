import R4333Lean.ProfileDUUUFourSupportP15SemanticBase61
import R4333Lean.ProfileDUUUFourSupportP15SemanticCatalogueFinite61

/-!
# Rooted catalogue entrance for UUU/block two/position fifteen

This module turns an arbitrary strongly normalized semantic P15 branch into
one of the finite rooted label choices used by the factorized catalogue.  It
stops before applying either support-stabilizer reduction or the residual
leaf lookup.
-/

namespace R4333
namespace ProfileDUUUFourSupportP15RootedCandidate61

open SingleRootStarCNF
open ProfileDFourSupportRestoredRootK15
open ProfileDUUUFourSupportP15SupportPair61
open ProfileDUUUFourSupportP15SemanticBase61
open ProfileDUUUFourSupportP0OrbitData61
open ProfileDUUUFourSupportP15SemanticCatalogueData61
open ProfileDUUUFourSupportP15SemanticCatalogueFinite61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev RootCase :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.RootCase
abbrev LabelAction :=
  ProfileDUUUFourSupportP15SemanticCatalogueData61.LabelAction
abbrev SupportRepresentative :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.SupportRepresentative

abbrev sourceFreeVertex :=
  ProfileDUUUFourSupportP0SemanticOrbit61.sourceFreeVertex
abbrev sourceFirstVertex :=
  ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex
abbrev sourceSecondVertex :=
  ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex

/-! ## Palette-three rooted host normalization -/

theorem colorDegree_zero_eq_of_hostNormalization
    (source : EdgeColoring (Fin 15) (Fin 4))
    (twisted : Bool) (vertex : Fin 15 ≃ Fin 15)
    (hnormalizes : ∀ u v, u ≠ v →
      source (vertex u) (vertex v) =
        canonicalPalette 3 (k15Template twisted u v))
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
      apply SingleRootStarWitness61.canonicalPalette_injective 3
      exact hencoded.trans (by decide)

/-- A palette-preserving `K15` normalization whose template root is exactly
the restored semantic root.  The omitted host colour is the P15 own colour
three. -/
structure RootedHostNormalization (normalized : NormalizedSupportPair) where
  root : RootCase
  vertex : Equiv.Perm (Fin 15)
  normalizes : ∀ u v, u ≠ v →
    restoredRootHostK15 (canonicalEnumerations normalized)
        (vertex u) (vertex v) =
      canonicalPalette 3 (k15Template (rootTwisted root) u v)
  rootImage : vertex (rootVertex root) = Fin.last 14

theorem exists_rootedHostNormalization (normalized : NormalizedSupportPair) :
    Nonempty (RootedHostNormalization normalized) := by
  let source := restoredRootHostK15 (canonicalEnumerations normalized)
  obtain ⟨twisted, vertex, hnormalizes⟩ :=
    exists_colorPreserving_hostK15Template 3 source
      (restoredRootHostK15_noMono (canonicalEnumerations normalized))
      (by
        intro u v huv
        change restoredRootHostK15 (canonicalEnumerations normalized)
          u v ≠ (3 : Fin 4)
        simpa [ProfileDColumnOwnColorIncidence61.blockRootColor] using
          restoredRootHostK15_avoids_own
            (canonicalEnumerations normalized) u v huv)
  let sourceRoot : Fin 15 := vertex.symm (Fin.last 14)
  have hdegree : colorDegree (k15Template twisted) 0 sourceRoot = 4 := by
    calc
      colorDegree (k15Template twisted) 0 sourceRoot =
          colorDegree source 0 (vertex sourceRoot) :=
        colorDegree_zero_eq_of_hostNormalization
          source twisted vertex hnormalizes sourceRoot
      _ = colorDegree source 0 (Fin.last 14) := by
        rw [show vertex sourceRoot = Fin.last 14 by simp [sourceRoot]]
      _ = 4 := restoredRootHostK15_root_degree_free normalized
  obtain ⟨root, htwisted, hroot⟩ :=
    ProfileDUUUFourSupportP0SemanticOrbit61.rootCase_complete
      twisted sourceRoot hdegree
  refine ⟨{
    root := root
    vertex := vertex
    normalizes := ?_
    rootImage := ?_
  }⟩
  · intro u v huv
    rw [htwisted]
    exact hnormalizes u v huv
  · rw [hroot]
    simp [sourceRoot]

/-! ## Recovery of the rooted `4|5|5` groups -/

theorem RootedHostNormalization.root_ne_sourceFreeVertex
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 4) :
    rootVertex normal.root ≠ sourceFreeVertex normal.vertex p := by
  intro h
  have himage := congrArg normal.vertex h
  rw [normal.rootImage] at himage
  simp only [sourceFreeVertex,
    ProfileDUUUFourSupportP0SemanticOrbit61.sourceFreeVertex,
    Equiv.apply_symm_apply] at himage
  exact Fin.castSucc_ne_last (freeLabel p) himage.symm

theorem RootedHostNormalization.root_ne_sourceFirstVertex
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    rootVertex normal.root ≠ sourceFirstVertex normal.vertex p := by
  intro h
  have himage := congrArg normal.vertex h
  rw [normal.rootImage] at himage
  simp only [ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex,
    Equiv.apply_symm_apply] at himage
  exact Fin.castSucc_ne_last (firstForeignLabel p) himage.symm

theorem RootedHostNormalization.root_ne_sourceSecondVertex
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    rootVertex normal.root ≠ sourceSecondVertex normal.vertex p := by
  intro h
  have himage := congrArg normal.vertex h
  rw [normal.rootImage] at himage
  simp only [ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex,
    Equiv.apply_symm_apply] at himage
  exact Fin.castSucc_ne_last (secondForeignLabel p) himage.symm

theorem RootedHostNormalization.sourceFreeVertex_color
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 4) :
    k15Template (rootTwisted normal.root) (rootVertex normal.root)
        (sourceFreeVertex normal.vertex p) = 0 := by
  apply SingleRootStarWitness61.canonicalPalette_injective 3
  have hnormal := normal.normalizes _ _
    (normal.root_ne_sourceFreeVertex p)
  calc
    canonicalPalette 3
        (k15Template (rootTwisted normal.root) (rootVertex normal.root)
          (sourceFreeVertex normal.vertex p)) =
        restoredRootHostK15 (canonicalEnumerations normalized)
          (normal.vertex (rootVertex normal.root))
          (normal.vertex (sourceFreeVertex normal.vertex p)) := hnormal.symm
    _ = restoredRootHostK15 (canonicalEnumerations normalized)
          (Fin.last 14) (freeLabel p).castSucc := by
      rw [normal.rootImage]
      simp only [sourceFreeVertex,
        ProfileDUUUFourSupportP0SemanticOrbit61.sourceFreeVertex,
        Equiv.apply_symm_apply]
    _ = freeHostForbiddenColor := by
      rw [restoredRootHostK15, extendByLast_last_old]
      simpa [freeLabel] using
        restoredRootHostAttachment_freeCoordinate
          (semantic normalized.branch) p
    _ = canonicalPalette 3 0 := by decide

theorem RootedHostNormalization.sourceFirstVertex_color
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    k15Template (rootTwisted normal.root) (rootVertex normal.root)
        (sourceFirstVertex normal.vertex p) = 1 := by
  apply SingleRootStarWitness61.canonicalPalette_injective 3
  have hnormal := normal.normalizes _ _
    (normal.root_ne_sourceFirstVertex p)
  calc
    canonicalPalette 3
        (k15Template (rootTwisted normal.root) (rootVertex normal.root)
          (sourceFirstVertex normal.vertex p)) =
        restoredRootHostK15 (canonicalEnumerations normalized)
          (normal.vertex (rootVertex normal.root))
          (normal.vertex (sourceFirstVertex normal.vertex p)) := hnormal.symm
    _ = restoredRootHostK15 (canonicalEnumerations normalized)
          (Fin.last 14) (firstForeignLabel p).castSucc := by
      rw [normal.rootImage]
      simp only [sourceFirstVertex,
        ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex,
        Equiv.apply_symm_apply]
    _ = firstForeignHostForbiddenColor (semantic normalized.branch) := by
      rw [restoredRootHostK15, extendByLast_last_old]
      simpa [firstForeignLabel] using
        restoredRootHostAttachment_firstForeignCoordinate
          (semantic normalized.branch) p
    _ = canonicalPalette 3 1 := by rfl

theorem RootedHostNormalization.sourceSecondVertex_color
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    k15Template (rootTwisted normal.root) (rootVertex normal.root)
        (sourceSecondVertex normal.vertex p) = 2 := by
  apply SingleRootStarWitness61.canonicalPalette_injective 3
  have hnormal := normal.normalizes _ _
    (normal.root_ne_sourceSecondVertex p)
  calc
    canonicalPalette 3
        (k15Template (rootTwisted normal.root) (rootVertex normal.root)
          (sourceSecondVertex normal.vertex p)) =
        restoredRootHostK15 (canonicalEnumerations normalized)
          (normal.vertex (rootVertex normal.root))
          (normal.vertex (sourceSecondVertex normal.vertex p)) := hnormal.symm
    _ = restoredRootHostK15 (canonicalEnumerations normalized)
          (Fin.last 14) (secondForeignLabel p).castSucc := by
      rw [normal.rootImage]
      simp only [sourceSecondVertex,
        ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex,
        Equiv.apply_symm_apply]
    _ = secondForeignHostForbiddenColor (semantic normalized.branch) := by
      rw [restoredRootHostK15, extendByLast_last_old]
      simpa [secondForeignLabel] using
        restoredRootHostAttachment_secondForeignCoordinate
          (semantic normalized.branch) p
    _ = canonicalPalette 3 2 := by rfl

theorem RootedHostNormalization.freeGroup_position
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 4) :
    rootFreeGroupVertex normal.root
        (rootFreeGroupPosition normal.root
          (sourceFreeVertex normal.vertex p)) =
      sourceFreeVertex normal.vertex p := by
  exact rootFreeGroupVertex_position_of_color normal.root _
    (normal.root_ne_sourceFreeVertex p).symm
    (by simpa [k15Template] using normal.sourceFreeVertex_color p)

theorem RootedHostNormalization.firstGroup_position
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    rootFirstGroupVertex normal.root
        (rootFirstGroupPosition normal.root
          (sourceFirstVertex normal.vertex p)) =
      sourceFirstVertex normal.vertex p := by
  exact rootFirstGroupVertex_position_of_color normal.root _
    (normal.root_ne_sourceFirstVertex p).symm
    (by simpa [k15Template] using normal.sourceFirstVertex_color p)

theorem RootedHostNormalization.secondGroup_position
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    rootSecondGroupVertex normal.root
        (rootSecondGroupPosition normal.root
          (sourceSecondVertex normal.vertex p)) =
      sourceSecondVertex normal.vertex p := by
  exact rootSecondGroupVertex_position_of_color normal.root _
    (normal.root_ne_sourceSecondVertex p).symm
    (by simpa [k15Template] using normal.sourceSecondVertex_color p)

def RootedHostNormalization.freePositionMap
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 4) : Fin 4 :=
  rootFreeGroupPosition normal.root (sourceFreeVertex normal.vertex p)

def RootedHostNormalization.firstPositionMap
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) : Fin 5 :=
  rootFirstGroupPosition normal.root (sourceFirstVertex normal.vertex p)

def RootedHostNormalization.secondPositionMap
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) : Fin 5 :=
  rootSecondGroupPosition normal.root (sourceSecondVertex normal.vertex p)

theorem RootedHostNormalization.freePositionMap_injective
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    Function.Injective normal.freePositionMap := by
  intro left right h
  apply ProfileDUUUFourSupportP0SemanticOrbit61.sourceFreeVertex_injective
    normal.vertex
  calc
    sourceFreeVertex normal.vertex left =
        rootFreeGroupVertex normal.root (normal.freePositionMap left) :=
      (normal.freeGroup_position left).symm
    _ = rootFreeGroupVertex normal.root (normal.freePositionMap right) :=
      congrArg (rootFreeGroupVertex normal.root) h
    _ = sourceFreeVertex normal.vertex right :=
      normal.freeGroup_position right

theorem RootedHostNormalization.firstPositionMap_injective
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    Function.Injective normal.firstPositionMap := by
  intro left right h
  apply ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex_injective
    normal.vertex
  calc
    sourceFirstVertex normal.vertex left =
        rootFirstGroupVertex normal.root (normal.firstPositionMap left) :=
      (normal.firstGroup_position left).symm
    _ = rootFirstGroupVertex normal.root (normal.firstPositionMap right) :=
      congrArg (rootFirstGroupVertex normal.root) h
    _ = sourceFirstVertex normal.vertex right :=
      normal.firstGroup_position right

theorem RootedHostNormalization.secondPositionMap_injective
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    Function.Injective normal.secondPositionMap := by
  intro left right h
  apply ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex_injective
    normal.vertex
  calc
    sourceSecondVertex normal.vertex left =
        rootSecondGroupVertex normal.root (normal.secondPositionMap left) :=
      (normal.secondGroup_position left).symm
    _ = rootSecondGroupVertex normal.root (normal.secondPositionMap right) :=
      congrArg (rootSecondGroupVertex normal.root) h
    _ = sourceSecondVertex normal.vertex right :=
      normal.secondGroup_position right

theorem RootedHostNormalization.freePositionMap_bijective
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    Function.Bijective normal.freePositionMap := by
  exact (Fintype.bijective_iff_injective_and_card
    normal.freePositionMap).2 ⟨normal.freePositionMap_injective, by simp⟩

theorem RootedHostNormalization.firstPositionMap_bijective
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    Function.Bijective normal.firstPositionMap := by
  exact (Fintype.bijective_iff_injective_and_card
    normal.firstPositionMap).2 ⟨normal.firstPositionMap_injective, by simp⟩

theorem RootedHostNormalization.secondPositionMap_bijective
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    Function.Bijective normal.secondPositionMap := by
  exact (Fintype.bijective_iff_injective_and_card
    normal.secondPositionMap).2 ⟨normal.secondPositionMap_injective, by simp⟩

noncomputable def RootedHostNormalization.freePositionEquiv
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective normal.freePositionMap normal.freePositionMap_bijective

noncomputable def RootedHostNormalization.firstPositionEquiv
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective normal.firstPositionMap normal.firstPositionMap_bijective

noncomputable def RootedHostNormalization.secondPositionEquiv
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective normal.secondPositionMap normal.secondPositionMap_bijective

theorem RootedHostNormalization.freePositionEquiv_group
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 4) :
    rootFreeGroupVertex normal.root (normal.freePositionEquiv p) =
      sourceFreeVertex normal.vertex p := normal.freeGroup_position p

theorem RootedHostNormalization.firstPositionEquiv_group
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    rootFirstGroupVertex normal.root (normal.firstPositionEquiv p) =
      sourceFirstVertex normal.vertex p := normal.firstGroup_position p

theorem RootedHostNormalization.secondPositionEquiv_group
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) (p : Fin 5) :
    rootSecondGroupVertex normal.root (normal.secondPositionEquiv p) =
      sourceSecondVertex normal.vertex p := normal.secondGroup_position p

/-! ## Compatibility with the two physical P15 supports -/

theorem RootedHostNormalization.firstPositionEquiv_compatible
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    FirstCompatibility normalized.first normal.root
      normal.firstPositionEquiv := by
  intro left right hne
  rw [normal.firstPositionEquiv_group, normal.firstPositionEquiv_group]
  rw [← normal.normalizes _ _
    ((ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex_injective
      normal.vertex).ne hne)]
  simp only [ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex,
    Equiv.apply_symm_apply]
  rw [restoredRootHostK15, extendByLast_old_old]
  rw [show firstForeignLabel left =
      fourFiveFiveEquiv (.inl (.inr left)) by rfl,
    show firstForeignLabel right =
      fourFiveFiveEquiv (.inl (.inr right)) by rfl,
    ownNeighborhoodHostColoring_firstForeignCoordinate]
  simp only [semantic_block]
  change normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (ProfileDTripleJoinReduction.blockVertex 0
        ((canonicalEnumerations normalized).firstEmbedding left).val)
      (ProfileDTripleJoinReduction.blockVertex 0
        ((canonicalEnumerations normalized).firstEmbedding right).val) = _
  rw [canonicalEnumerations_firstEmbedding,
    canonicalEnumerations_firstEmbedding]
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      0 (by rfl)
      ((canonicalEnumerations normalized).firstEmbedding left)
      ((canonicalEnumerations normalized).firstEmbedding right)
      ((canonicalEnumerations normalized).firstEmbedding.injective.ne hne)
  rw [canonicalEnumerations_firstEmbedding,
    canonicalEnumerations_firstEmbedding] at hedge
  simpa [ProfileDTripleJoinReduction.Kind.twisted] using hedge

theorem RootedHostNormalization.secondPositionEquiv_compatible
    {normalized : NormalizedSupportPair}
    (normal : RootedHostNormalization normalized) :
    SecondCompatibility normalized.second normal.root
      normal.secondPositionEquiv := by
  intro left right hne
  rw [normal.secondPositionEquiv_group, normal.secondPositionEquiv_group]
  rw [← normal.normalizes _ _
    ((ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex_injective
      normal.vertex).ne hne)]
  simp only [ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex,
    Equiv.apply_symm_apply]
  rw [restoredRootHostK15, extendByLast_old_old]
  rw [show secondForeignLabel left = fourFiveFiveEquiv (.inr left) by rfl,
    show secondForeignLabel right = fourFiveFiveEquiv (.inr right) by rfl,
    ownNeighborhoodHostColoring_secondForeignCoordinate]
  simp only [semantic_block]
  change normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (ProfileDTripleJoinReduction.blockVertex 1
        ((canonicalEnumerations normalized).secondEmbedding left).val)
      (ProfileDTripleJoinReduction.blockVertex 1
        ((canonicalEnumerations normalized).secondEmbedding right).val) = _
  rw [canonicalEnumerations_secondEmbedding,
    canonicalEnumerations_secondEmbedding]
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      normalized.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      1 (by rfl)
      ((canonicalEnumerations normalized).secondEmbedding left)
      ((canonicalEnumerations normalized).secondEmbedding right)
      ((canonicalEnumerations normalized).secondEmbedding.injective.ne hne)
  rw [canonicalEnumerations_secondEmbedding,
    canonicalEnumerations_secondEmbedding] at hedge
  simpa [ProfileDTripleJoinReduction.Kind.twisted] using hedge

/-! ## Raw finite rooted candidates -/

def candidateVertex (firstSupport secondSupport : SupportRepresentative)
    (root : RootCase) (free : FreeLabelAction)
    (first second : LabelAction) : Fin 14 -> Fin 15 :=
  fun p => match matrixCoordinate p with
    | .inl (.inl a) =>
        rootFreeGroupVertex root (freeLabelPermutation free a)
    | .inl (.inr a) =>
        rootFirstGroupVertex root
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.firstCompatiblePerm
            firstSupport root first a)
    | .inr a =>
        rootSecondGroupVertex root
          (ProfileDUUUFourSupportP15SemanticCatalogueData61.secondCompatiblePerm
            secondSupport root second a)

def candidateColor (firstSupport secondSupport : SupportRepresentative)
    (root : RootCase) (free : FreeLabelAction)
    (first second : LabelAction) (left right : Fin 14) : Fin 4 :=
  canonicalPalette 3 (k15Template (rootTwisted root)
    (candidateVertex firstSupport secondSupport root free first second left)
    (candidateVertex firstSupport secondSupport root free first second right))

structure RootedCandidateParameters (normalized : NormalizedSupportPair) where
  normalization : RootedHostNormalization normalized
  free : FreeLabelAction
  first : LabelAction
  second : LabelAction
  freeGroup : ∀ p : Fin 4,
    rootFreeGroupVertex normalization.root
        (freeLabelPermutation free p) =
      sourceFreeVertex normalization.vertex p
  firstGroup : ∀ p : Fin 5,
    rootFirstGroupVertex normalization.root
        (ProfileDUUUFourSupportP15SemanticCatalogueData61.firstCompatiblePerm
          normalized.first normalization.root first p) =
      sourceFirstVertex normalization.vertex p
  secondGroup : ∀ p : Fin 5,
    rootSecondGroupVertex normalization.root
        (ProfileDUUUFourSupportP15SemanticCatalogueData61.secondCompatiblePerm
          normalized.second normalization.root second p) =
      sourceSecondVertex normalization.vertex p

theorem exists_rootedCandidateParameters
    (normalized : NormalizedSupportPair) :
    Nonempty (RootedCandidateParameters normalized) := by
  obtain ⟨normal⟩ := exists_rootedHostNormalization normalized
  obtain ⟨free, hfree⟩ :=
    ProfileDUUUFourSupportP0SemanticOrbit61.freeLabelPermutation_complete
      normal.freePositionEquiv
  obtain ⟨first, hfirst⟩ :=
    firstCompatiblePerm_complete normalized.first normal.root
      normal.firstPositionEquiv normal.firstPositionEquiv_compatible
  obtain ⟨second, hsecond⟩ :=
    secondCompatiblePerm_complete normalized.second normal.root
      normal.secondPositionEquiv normal.secondPositionEquiv_compatible
  refine ⟨{
    normalization := normal
    free := free
    first := first
    second := second
    freeGroup := ?_
    firstGroup := ?_
    secondGroup := ?_
  }⟩
  · intro p
    rw [← hfree p]
    exact normal.freePositionEquiv_group p
  · intro p
    rw [← hfirst p]
    exact normal.firstPositionEquiv_group p
  · intro p
    rw [← hsecond p]
    exact normal.secondPositionEquiv_group p

theorem RootedCandidateParameters.candidateVertex_eq_source
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized) (p : Fin 14) :
    candidateVertex normalized.first normalized.second
        parameters.normalization.root parameters.free parameters.first
        parameters.second p =
      parameters.normalization.vertex.symm p.castSucc := by
  rw [← matrixCoordinateIndex_coordinate p]
  generalize matrixCoordinate p = coordinate
  rcases coordinate with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · rw [show matrixCoordinateIndex (.inl (.inl freePosition)) =
          fourFiveFiveEquiv (.inl (.inl freePosition)) by
          exact matrixCoordinateIndex_eq_equiv _]
      simp only [candidateVertex, matrixCoordinate_eq_equiv_symm,
        Equiv.symm_apply_apply, parameters.freeGroup,
        sourceFreeVertex,
        ProfileDUUUFourSupportP0SemanticOrbit61.sourceFreeVertex, freeLabel]
    · rw [show matrixCoordinateIndex (.inl (.inr firstPosition)) =
          fourFiveFiveEquiv (.inl (.inr firstPosition)) by
          exact matrixCoordinateIndex_eq_equiv _]
      simp only [candidateVertex, matrixCoordinate_eq_equiv_symm,
        Equiv.symm_apply_apply, parameters.firstGroup,
        sourceFirstVertex,
        ProfileDUUUFourSupportP0SemanticOrbit61.sourceFirstVertex,
        firstForeignLabel]
  · rw [show matrixCoordinateIndex (.inr secondPosition) =
        fourFiveFiveEquiv (.inr secondPosition) by
        exact matrixCoordinateIndex_eq_equiv _]
    simp only [candidateVertex, matrixCoordinate_eq_equiv_symm,
      Equiv.symm_apply_apply, parameters.secondGroup,
      sourceSecondVertex,
      ProfileDUUUFourSupportP0SemanticOrbit61.sourceSecondVertex,
      secondForeignLabel]

theorem RootedCandidateParameters.matrix_eq_candidateColor
    {normalized : NormalizedSupportPair}
    (parameters : RootedCandidateParameters normalized)
    (left right : Fin 14) (hne : left ≠ right) :
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized left) (physicalVertex normalized right) =
      candidateColor normalized.first normalized.second
        parameters.normalization.root parameters.free parameters.first
        parameters.second left right := by
  let source := restoredRootHostK15 (canonicalEnumerations normalized)
  let leftCandidate := candidateVertex normalized.first normalized.second
    parameters.normalization.root parameters.free parameters.first
    parameters.second left
  let rightCandidate := candidateVertex normalized.first normalized.second
    parameters.normalization.root parameters.free parameters.first
    parameters.second right
  have hcandidates : leftCandidate ≠ rightCandidate := by
    rw [show leftCandidate =
        parameters.normalization.vertex.symm left.castSucc by
          exact parameters.candidateVertex_eq_source left,
      show rightCandidate =
        parameters.normalization.vertex.symm right.castSucc by
          exact parameters.candidateVertex_eq_source right]
    exact parameters.normalization.vertex.symm.injective.ne
      (Fin.castSuccEmb.injective.ne hne)
  calc
    ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
        (physicalVertex normalized left) (physicalVertex normalized right) =
        ownNeighborhoodHostColoring (canonicalEnumerations normalized)
          left right := physicalMatrix_eq_ownNeighborhood normalized left right
    _ = source left.castSucc right.castSucc := by
      dsimp only [source]
      rw [restoredRootHostK15, extendByLast_old_old]
    _ = source
        (parameters.normalization.vertex leftCandidate)
        (parameters.normalization.vertex rightCandidate) := by
      rw [show leftCandidate =
          parameters.normalization.vertex.symm left.castSucc by
            exact parameters.candidateVertex_eq_source left,
        show rightCandidate =
          parameters.normalization.vertex.symm right.castSucc by
            exact parameters.candidateVertex_eq_source right]
      simp
    _ = candidateColor normalized.first normalized.second
        parameters.normalization.root parameters.free parameters.first
        parameters.second left right :=
      parameters.normalization.normalizes leftCandidate rightCandidate
        hcandidates

#print axioms exists_rootedHostNormalization
#print axioms RootedHostNormalization.freePositionEquiv_group
#print axioms RootedHostNormalization.firstPositionEquiv_compatible
#print axioms RootedHostNormalization.secondPositionEquiv_compatible
#print axioms exists_rootedCandidateParameters
#print axioms RootedCandidateParameters.candidateVertex_eq_source
#print axioms RootedCandidateParameters.matrix_eq_candidateColor

end ProfileDUUUFourSupportP15RootedCandidate61
end R4333
