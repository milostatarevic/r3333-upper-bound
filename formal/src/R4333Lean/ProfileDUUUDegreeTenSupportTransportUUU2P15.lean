import R4333Lean.ProfileDUUUDegreeTenSupportClassificationUUU2P15
import R4333Lean.ProfileDUUUDegreeTenEndToEndSemanticUUU0P2

/-!
# Semantic support transport for UUU / block two / position fifteen

An arbitrary exact degree-ten branch has two colour-two independent five-sets
in the two foreign `K15` blocks.  The checked strong normalizers transport the
branch to the authoritative ordered coordinates for one of the nine pairs
over representatives `0`, `1`, and `4`.
-/

namespace R4333
namespace ProfileDUUUDegreeTenSupportTransportUUU2P15

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixTransport61
open ProfileDUUUDegreeTenSupportOrbits61
open ProfileDUUUDegreeTenSupportOrbitsB2P15
open ProfileDUUUDegreeTenSupportClassificationUUU2P15
open ProfileDUUUDegreeTenEndToEndSemanticUUU0P2
open ProfileDDegreeTenMatrixLeafDataUUU2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition

abbrev MatrixFiveVertex :=
  ProfileDHighOwnFiveRowSplit61.FiveVertex

def normalizedSupportRepresentative (index : Fin 11) :
    SupportRepresentative :=
  dataRepresentativeOfIndex (q2SupportRepresentative index)

theorem normalizedSupportRepresentative_positions (index : Fin 11) :
    (support (normalizedSupportRepresentative index)).positions =
      q2Support (q2SupportRepresentative index) := by
  exact dataSupport_eq_q2Support_of_representative _
    (q2SupportRepresentative_mem index)

theorem q2SupportEquiv_symm_preserves
    (index : Fin 11) (left right : Fin 15) (hne : left ≠ right) :
    k15Template false ((q2SupportEquiv index).symm left)
        ((q2SupportEquiv index).symm right) =
      k15Template false left right := by
  have h := (q2SupportMap_preserves index
    ((q2SupportEquiv index).symm left)
    ((q2SupportEquiv index).symm right)
    ((q2SupportEquiv index).symm.injective.ne hne)).symm
  change k15Template false ((q2SupportEquiv index).symm left)
      ((q2SupportEquiv index).symm right) =
    k15Template false
      (q2SupportEquiv index ((q2SupportEquiv index).symm left))
      (q2SupportEquiv index ((q2SupportEquiv index).symm right)) at h
  simpa using h

noncomputable def supportNormalizerTailPerm
    (firstIndex secondIndex : Fin 11) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (q2SupportEquiv firstIndex).symm
        (q2SupportEquiv secondIndex).symm)
      (Equiv.refl (Fin 16))).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

@[simp] theorem supportNormalizerTailPerm_blockZero
    (firstIndex secondIndex : Fin 11) (position : Fin 15) :
    supportNormalizerTailPerm firstIndex secondIndex
        (ProfileDTripleJoinReduction.blockVertex 0 position.val) =
      ProfileDTripleJoinReduction.blockVertex 0
        ((q2SupportEquiv firstIndex).symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp only [supportNormalizerTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero _

@[simp] theorem supportNormalizerTailPerm_blockOne
    (firstIndex secondIndex : Fin 11) (position : Fin 15) :
    supportNormalizerTailPerm firstIndex secondIndex
        (ProfileDTripleJoinReduction.blockVertex 1 position.val) =
      ProfileDTripleJoinReduction.blockVertex 1
        ((q2SupportEquiv secondIndex).symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [supportNormalizerTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

@[simp] theorem supportNormalizerTailPerm_blockTwo
    (firstIndex secondIndex : Fin 11) (position : Fin 16) :
    supportNormalizerTailPerm firstIndex secondIndex
        (ProfileDTripleJoinReduction.blockVertex 2 position.val) =
      ProfileDTripleJoinReduction.blockVertex 2 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp [supportNormalizerTailPerm]

theorem supportNormalizer_templateCanonical
    (tail : ProfileDTripleJoinReduction.Witness .uuu)
    (firstIndex secondIndex : Fin 11) :
    ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex target left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex target right)) =
        SingleRootStarCNF.canonicalPalette (Fin.succ target)
          (SingleRootStarCNF.templateColor (blockSize target)
            (Kind.twisted .uuu target) left right) := by
  intro target left right hleft hright hlr
  fin_cases target
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 0 left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 0 right)) =
        SingleRootStarCNF.canonicalPalette 1
          (SingleRootStarCNF.templateColor 15 false left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 0 left =
        ProfileDTripleJoinReduction.blockVertex 0 leftFin.val by rfl,
      supportNormalizerTailPerm_blockZero,
      show ProfileDTripleJoinReduction.blockVertex 0 right =
        ProfileDTripleJoinReduction.blockVertex 0 rightFin.val by rfl,
      supportNormalizerTailPerm_blockZero]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 0 (by decide)
          ((q2SupportEquiv firstIndex).symm leftFin)
          ((q2SupportEquiv firstIndex).symm rightFin)
          ((q2SupportEquiv firstIndex).symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (0 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 0
            ((q2SupportEquiv firstIndex).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 0
            ((q2SupportEquiv firstIndex).symm rightFin).val) =
          SingleRootStarCNF.canonicalPalette 1
            (k15Template false
              ((q2SupportEquiv firstIndex).symm leftFin)
              ((q2SupportEquiv firstIndex).symm rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 1
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 1)
          (q2SupportEquiv_symm_preserves firstIndex leftFin rightFin hne)
      _ = _ := by
        simp [blockSize, SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 1 left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 1 right)) =
        SingleRootStarCNF.canonicalPalette 2
          (SingleRootStarCNF.templateColor 15 false left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 1 left =
        ProfileDTripleJoinReduction.blockVertex 1 leftFin.val by rfl,
      supportNormalizerTailPerm_blockOne,
      show ProfileDTripleJoinReduction.blockVertex 1 right =
        ProfileDTripleJoinReduction.blockVertex 1 rightFin.val by rfl,
      supportNormalizerTailPerm_blockOne]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 1 (by decide)
          ((q2SupportEquiv secondIndex).symm leftFin)
          ((q2SupportEquiv secondIndex).symm rightFin)
          ((q2SupportEquiv secondIndex).symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1
            ((q2SupportEquiv secondIndex).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 1
            ((q2SupportEquiv secondIndex).symm rightFin).val) =
          SingleRootStarCNF.canonicalPalette 2
            (k15Template false
              ((q2SupportEquiv secondIndex).symm leftFin)
              ((q2SupportEquiv secondIndex).symm rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 2
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 2)
          (q2SupportEquiv_symm_preserves secondIndex leftFin rightFin hne)
      _ = _ := by
        simp [blockSize, SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 16 at hleft
    change right < 16 at hright
    change
      tail.coloring
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 2 left))
          (supportNormalizerTailPerm firstIndex secondIndex
            (ProfileDTripleJoinReduction.blockVertex 2 right)) =
        SingleRootStarCNF.canonicalPalette 3
          (SingleRootStarCNF.templateColor 16 false left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show ProfileDTripleJoinReduction.blockVertex 2 left =
        ProfileDTripleJoinReduction.blockVertex 2 leftFin.val by rfl,
      supportNormalizerTailPerm_blockTwo,
      show ProfileDTripleJoinReduction.blockVertex 2 right =
        ProfileDTripleJoinReduction.blockVertex 2 rightFin.val by rfl,
      supportNormalizerTailPerm_blockTwo]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        tail 2 (by decide) leftFin rightFin hne
    have htwisted : Kind.uuu.twisted (2 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    simpa [SingleRootStarCNF.templateColor, SingleRootStarCNF.fin16,
      leftFin, rightFin, Nat.mod_eq_of_lt hleft,
      Nat.mod_eq_of_lt hright] using hedge

theorem firstNormalizer_positions
    {sourceCoordinates : MatrixCoordinates 2}
    (firstIndex : Fin 11)
    (hsource : sourceCoordinates.first.positions = q2Support firstIndex)
    (p : Fin 15) :
    p ∈ (support (normalizedSupportRepresentative firstIndex)).positions ↔
      (q2SupportEquiv firstIndex).symm p ∈
        sourceCoordinates.first.positions := by
  have htarget := normalizedSupportRepresentative_positions firstIndex
  constructor
  · intro hp
    have hpRep : p ∈ q2Support (q2SupportRepresentative firstIndex) :=
      htarget ▸ hp
    have hpImage : p ∈ (q2Support firstIndex).image
        (q2SupportMap firstIndex) :=
      (q2SupportMap_image firstIndex).symm ▸ hpRep
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    have hqeq : (q2SupportEquiv firstIndex).symm p = q := by
      apply (q2SupportEquiv firstIndex).injective
      rw [Equiv.apply_symm_apply]
      exact hqp.symm
    exact hsource.symm ▸ (hqeq.symm ▸ hq)
  · intro hp
    have hpSource : (q2SupportEquiv firstIndex).symm p ∈
        q2Support firstIndex := hsource ▸ hp
    have hpImage : p ∈ (q2Support firstIndex).image
        (q2SupportMap firstIndex) := by
      apply Finset.mem_image.mpr
      refine ⟨(q2SupportEquiv firstIndex).symm p, hpSource, ?_⟩
      exact (q2SupportEquiv firstIndex).apply_symm_apply p
    have hpRep : p ∈ q2Support (q2SupportRepresentative firstIndex) :=
      q2SupportMap_image firstIndex ▸ hpImage
    exact htarget.symm ▸ hpRep

theorem secondNormalizer_positions
    {sourceCoordinates : MatrixCoordinates 2}
    (secondIndex : Fin 11)
    (hsource : sourceCoordinates.second.positions = q2Support secondIndex)
    (p : Fin 15) :
    p ∈ (support (normalizedSupportRepresentative secondIndex)).positions ↔
      (q2SupportEquiv secondIndex).symm p ∈
        sourceCoordinates.second.positions := by
  have htarget := normalizedSupportRepresentative_positions secondIndex
  constructor
  · intro hp
    have hpRep : p ∈ q2Support (q2SupportRepresentative secondIndex) :=
      htarget ▸ hp
    have hpImage : p ∈ (q2Support secondIndex).image
        (q2SupportMap secondIndex) :=
      (q2SupportMap_image secondIndex).symm ▸ hpRep
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    have hqeq : (q2SupportEquiv secondIndex).symm p = q := by
      apply (q2SupportEquiv secondIndex).injective
      rw [Equiv.apply_symm_apply]
      exact hqp.symm
    exact hsource.symm ▸ (hqeq.symm ▸ hq)
  · intro hp
    have hpSource : (q2SupportEquiv secondIndex).symm p ∈
        q2Support secondIndex := hsource ▸ hp
    have hpImage : p ∈ (q2Support secondIndex).image
        (q2SupportMap secondIndex) := by
      apply Finset.mem_image.mpr
      refine ⟨(q2SupportEquiv secondIndex).symm p, hpSource, ?_⟩
      exact (q2SupportEquiv secondIndex).apply_symm_apply p
    have hpRep : p ∈ q2Support (q2SupportRepresentative secondIndex) :=
      q2SupportMap_image secondIndex ▸ hpImage
    exact htarget.symm ▸ hpRep

noncomputable def firstSupportPositionPerm
    (sourceCoordinates : MatrixCoordinates 2) (firstIndex : Fin 11)
    (hsource : sourceCoordinates.first.positions = q2Support firstIndex) :
    Equiv.Perm MatrixFiveVertex :=
  by
    simp only [ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
      blockSize] at hsource ⊢
    exact orderedSupportPositionPerm sourceCoordinates.first
      (support (normalizedSupportRepresentative firstIndex))
      (q2SupportEquiv firstIndex).symm
      (firstNormalizer_positions firstIndex hsource)

noncomputable def secondSupportPositionPerm
    (sourceCoordinates : MatrixCoordinates 2) (secondIndex : Fin 11)
    (hsource : sourceCoordinates.second.positions = q2Support secondIndex) :
    Equiv.Perm MatrixFiveVertex :=
  by
    simp only [ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
      blockSize] at hsource ⊢
    exact orderedSupportPositionPerm sourceCoordinates.second
      (support (normalizedSupportRepresentative secondIndex))
      (q2SupportEquiv secondIndex).symm
      (secondNormalizer_positions secondIndex hsource)

theorem firstSupportPositionPerm_embedding
    (sourceCoordinates : MatrixCoordinates 2) (firstIndex : Fin 11)
    (hsource : sourceCoordinates.first.positions = q2Support firstIndex)
    (a : MatrixFiveVertex) :
    (q2SupportEquiv firstIndex).symm
        ((support (normalizedSupportRepresentative firstIndex)).embedding a) =
      sourceCoordinates.first.embedding
        (firstSupportPositionPerm sourceCoordinates firstIndex hsource a) := by
  exact orderedSupportPositionPerm_embedding _ _ _ _ a

theorem secondSupportPositionPerm_embedding
    (sourceCoordinates : MatrixCoordinates 2) (secondIndex : Fin 11)
    (hsource : sourceCoordinates.second.positions = q2Support secondIndex)
    (a : MatrixFiveVertex) :
    (q2SupportEquiv secondIndex).symm
        ((support (normalizedSupportRepresentative secondIndex)).embedding a) =
      sourceCoordinates.second.embedding
        (secondSupportPositionPerm sourceCoordinates secondIndex hsource a) := by
  exact orderedSupportPositionPerm_embedding _ _ _ _ a

@[simp] theorem matrixCoordinates_vertex_blockZero
    (coordinates : MatrixCoordinates 2) (a : MatrixFiveVertex) :
    coordinates.vertex
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 a) =
      freeVertex a := by
  rw [catalogBlockZero_eq_freeMatrixIndex]
  exact coordinates.vertex_free a

@[simp] theorem matrixCoordinates_vertex_blockOne
    (coordinates : MatrixCoordinates 2) (a : MatrixFiveVertex) :
    coordinates.vertex
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 a) =
      tailVertex
        (ProfileDTripleJoinReduction.blockVertex 0
          (coordinates.first.embedding a).val) := by
  rw [catalogBlockOne_eq_firstForeignMatrixIndex]
  simpa [ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock] using
    coordinates.vertex_first a

@[simp] theorem matrixCoordinates_vertex_blockTwo
    (coordinates : MatrixCoordinates 2) (a : MatrixFiveVertex) :
    coordinates.vertex
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 a) =
      tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1
          (coordinates.second.embedding a).val) := by
  rw [catalogBlockTwo_eq_secondForeignMatrixIndex]
  simpa [ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock] using
    coordinates.vertex_second a

noncomputable def supportNormalizationMatrixPerm
    (sourceCoordinates : MatrixCoordinates 2)
    (firstIndex secondIndex : Fin 11)
    (hfirst : sourceCoordinates.first.positions = q2Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = q2Support secondIndex) :
    Equiv.Perm (Fin 15) :=
  matrixBlockPerm (Equiv.refl _)
    (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
    (secondSupportPositionPerm sourceCoordinates secondIndex hsecond)

theorem supportNormalization_coordinates_covariant
    (sourceCoordinates : MatrixCoordinates 2)
    (firstIndex secondIndex : Fin 11)
    (hfirst : sourceCoordinates.first.positions = q2Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = q2Support secondIndex)
    (i : Fin 15) :
    totalVertexPerm (supportNormalizerTailPerm firstIndex secondIndex)
        ((coordinatesFor (normalizedSupportRepresentative firstIndex)
          (normalizedSupportRepresentative secondIndex)).vertex i) =
      sourceCoordinates.vertex
        (supportNormalizationMatrixPerm sourceCoordinates firstIndex
          secondIndex hfirst hsecond i) := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixCoordinates_vertex_blockZero,
        totalVertexPerm_free]
      change freeVertex position =
        sourceCoordinates.vertex
          (matrixBlockPerm (Equiv.refl _)
            (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
            (secondSupportPositionPerm sourceCoordinates secondIndex hsecond)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position))
      rw [matrixBlockPerm_blockZero, matrixCoordinates_vertex_blockZero]
      rfl
    · rw [threeFiveEquiv_blockOne, matrixCoordinates_vertex_blockOne,
        totalVertexPerm_tail, supportNormalizerTailPerm_blockZero]
      change tailVertex
          (ProfileDTripleJoinReduction.blockVertex 0
            ((q2SupportEquiv firstIndex).symm
              ((support (normalizedSupportRepresentative firstIndex)).embedding
                position)).val) =
        sourceCoordinates.vertex
          (matrixBlockPerm (Equiv.refl _)
            (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
            (secondSupportPositionPerm sourceCoordinates secondIndex hsecond)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position))
      rw [matrixBlockPerm_blockOne, matrixCoordinates_vertex_blockOne,
        firstSupportPositionPerm_embedding]
  · rw [threeFiveEquiv_blockTwo, matrixCoordinates_vertex_blockTwo,
      totalVertexPerm_tail, supportNormalizerTailPerm_blockOne]
    change tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1
          ((q2SupportEquiv secondIndex).symm
            ((support (normalizedSupportRepresentative secondIndex)).embedding
              position)).val) =
      sourceCoordinates.vertex
        (matrixBlockPerm (Equiv.refl _)
          (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
          (secondSupportPositionPerm sourceCoordinates secondIndex hsecond)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position))
    rw [matrixBlockPerm_blockTwo, matrixCoordinates_vertex_blockTwo,
      secondSupportPositionPerm_embedding]

noncomputable def supportNormalizedMatrix
    (sourceCoordinates : MatrixCoordinates 2)
    (sourceMatrix : EdgeColoring (Fin 15) (Fin 4))
    (firstIndex secondIndex : Fin 11)
    (hfirst : sourceCoordinates.first.positions = q2Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = q2Support secondIndex) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring sourceMatrix
    (supportNormalizationMatrixPerm sourceCoordinates firstIndex secondIndex
      hfirst hsecond)

noncomputable def normalizeExactDegreeTenSupports
    {sourceCoordinates : MatrixCoordinates 2}
    {sourceMatrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      sourceCoordinates sourceMatrix)
    (firstIndex secondIndex : Fin 11)
    (hfirst : sourceCoordinates.first.positions = q2Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = q2Support secondIndex) :
    ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor (normalizedSupportRepresentative firstIndex)
        (normalizedSupportRepresentative secondIndex))
      (supportNormalizedMatrix sourceCoordinates sourceMatrix firstIndex
        secondIndex hfirst hsecond) :=
  transportExactDegreeTenMatrixBranch exact
    (supportNormalizerTailPerm firstIndex secondIndex)
    (supportNormalizer_templateCanonical
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      firstIndex secondIndex)
    (by rw [supportNormalizerTailPerm_blockTwo])
    (q2SupportEquiv firstIndex).symm
    (q2SupportEquiv secondIndex).symm
    (supportNormalizationMatrixPerm sourceCoordinates firstIndex secondIndex
      hfirst hsecond)
    (supportNormalizerTailPerm_blockZero firstIndex secondIndex)
    (supportNormalizerTailPerm_blockOne firstIndex secondIndex)
    (firstNormalizer_positions firstIndex hfirst)
    (secondNormalizer_positions secondIndex hsecond)
    (supportNormalization_coordinates_covariant sourceCoordinates firstIndex
      secondIndex hfirst hsecond)
    (matrixBlockPerm_preserves_cross_group _ _ _)
    (by intro left right _; rfl)

/-- Every arbitrary exact branch transports to exact authoritative support
coordinates for a pair of the three checked representatives. -/
theorem exists_normalizedExactBranch_of_exact
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∃ firstIndex secondIndex : Fin 11,
      ∃ hfirst : coordinates.first.positions = q2Support firstIndex,
        ∃ hsecond : coordinates.second.positions = q2Support secondIndex,
          Nonempty
            (ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
              (coordinatesFor (normalizedSupportRepresentative firstIndex)
                (normalizedSupportRepresentative secondIndex))
              (supportNormalizedMatrix coordinates matrix firstIndex secondIndex
                hfirst hsecond)) := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex exact
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex exact
  exact ⟨firstIndex, secondIndex, hfirst, hsecond,
    ⟨normalizeExactDegreeTenSupports exact firstIndex secondIndex
      hfirst hsecond⟩⟩

#print axioms q2SupportEquiv_symm_preserves
#print axioms supportNormalizer_templateCanonical
#print axioms normalizeExactDegreeTenSupports

end ProfileDUUUDegreeTenSupportTransportUUU2P15
end R4333
