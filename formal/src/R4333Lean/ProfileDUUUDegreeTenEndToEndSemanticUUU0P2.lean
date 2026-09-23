import R4333Lean.ProfileDUUUDegreeTenSupportClassificationUUU0P2
import R4333Lean.ProfileDUUUDegreeTenCatalogSemanticCompleteness61
import R4333Lean.ProfileDUUUDegreeTenSupportOrbits61
import R4333Lean.ProfileDDegreeTenMatrixTransport61
import R4333Lean.ProfileDUUUDegreeTenCatalogLeafConnector61

/-!
# End-to-end semantic coverage of the UUU/block-zero degree-ten branch

This module contains no LRAT imports.  It normalizes arbitrary exact support
coordinates, classifies the resulting K15 cross matrix, and transports it to
one of the ten authoritative representative semantic leaves.
-/

namespace R4333
namespace ProfileDUUUDegreeTenEndToEndSemanticUUU0P2

open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixTransport61
open ProfileDUUUDegreeTenSupportOrbits61
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogSemanticCompleteness61
open ProfileDUUUDegreeTenCatalogLeafConnector61
open ProfileDDegreeTenMatrixLeafTenDataUUU0P2
open ProfileDDegreeTenRepresentativeLeafBridge61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafTenDataUUU0P2.selectedPosition

theorem orderedFiveSupport_card {n : Nat} (support : OrderedFiveSupport n) :
    support.positions.card = 5 := by
  calc
    support.positions.card =
        (Finset.univ : Finset
          ProfileDHighOwnFiveRowSplit61.FiveVertex).card := by
      exact Finset.card_image_of_injective _ support.embedding.injective
    _ = 5 := by simp

theorem firstSupport_templateIndependent
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    IsColorIndependentSet (k15Template false) 1
      coordinates.first.positions := by
  intro left hleft right hright hlr hcolor
  let tail := exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hleftOwn := (exact.firstSupportExact left).mp hleft
  have hrightOwn := (exact.firstSupportExact right).mp hright
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      tail 1 (by decide) left right hlr
  have hedgeOwn :
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1 left.val)
          (ProfileDTripleJoinReduction.blockVertex 1 right.val) = 1 := by
    rw [hedge]
    change SingleRootStarCNF.canonicalPalette 2
      (k15Template false left right) = 1
    rw [hcolor]
    decide
  apply tail.noMono
    (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val)
    (ProfileDTripleJoinReduction.blockVertex 1 left.val)
    (ProfileDTripleJoinReduction.blockVertex 1 right.val)
  · exact ⟨
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 1
        (by decide) SelectedPosition.isLt left.isLt,
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 1
        (by decide) SelectedPosition.isLt right.isLt,
      (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 1).ne hlr⟩
  · exact ⟨hleftOwn.trans hrightOwn.symm,
      hrightOwn.trans hedgeOwn.symm⟩

theorem secondSupport_templateIndependent
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    IsColorIndependentSet (k16Template false) 1
      coordinates.second.positions := by
  intro left hleft right hright hlr hcolor
  let tail := exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hleftOwn := (exact.secondSupportExact left).mp hleft
  have hrightOwn := (exact.secondSupportExact right).mp hright
  have hedge :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
      tail 2 (by decide) left right hlr
  have hedgeOwn :
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 2 left.val)
          (ProfileDTripleJoinReduction.blockVertex 2 right.val) = 1 := by
    rw [hedge]
    change SingleRootStarCNF.canonicalPalette 3
      (k16Template false left right) = 1
    rw [hcolor]
    decide
  apply tail.noMono
    (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val)
    (ProfileDTripleJoinReduction.blockVertex 2 left.val)
    (ProfileDTripleJoinReduction.blockVertex 2 right.val)
  · exact ⟨
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 2
        (by decide) SelectedPosition.isLt left.isLt,
      ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne 0 2
        (by decide) SelectedPosition.isLt right.isLt,
      (ProfileDColumnOwnColorIncidence61.blockVertex_fixed_injective 2).ne hlr⟩
  · exact ⟨hleftOwn.trans hrightOwn.symm,
      hrightOwn.trans hedgeOwn.symm⟩

theorem exists_firstSupportIndex
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ i : Fin 11, coordinates.first.positions = u15Support i := by
  have hmem : coordinates.first.positions ∈
      CriticalK15PartitionClassification.independentFiveSets false 1 :=
    (CriticalK15PartitionClassification.mem_independentFiveSets_iff
      false 1 coordinates.first.positions).2
      ⟨orderedFiveSupport_card coordinates.first,
        firstSupport_templateIndependent exact⟩
  rw [u15SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

theorem exists_secondSupportIndex
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ i : Fin 16, coordinates.second.positions = u16Support i := by
  have hmem : coordinates.second.positions ∈ u16IndependentFiveSets := by
    unfold u16IndependentFiveSets
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, orderedFiveSupport_card coordinates.second⟩
    · exact (colorViolationCount_eq_zero_iff _ _ _).2
        (secondSupport_templateIndependent exact)
  rw [u16SupportFamily_complete] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩

noncomputable def supportNormalizerTailPerm
    (firstIndex : Fin 11) (secondIndex : Fin 16) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (Equiv.refl (Fin 15))
        (u15SupportEquiv firstIndex).symm)
      (u16SupportEquiv secondIndex).symm).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

@[simp] theorem supportNormalizerTailPerm_blockZero
    (firstIndex : Fin 11) (secondIndex : Fin 16) (position : Fin 15) :
    supportNormalizerTailPerm firstIndex secondIndex
        (ProfileDTripleJoinReduction.blockVertex 0 position.val) =
      ProfileDTripleJoinReduction.blockVertex 0 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp [supportNormalizerTailPerm]

@[simp] theorem supportNormalizerTailPerm_blockOne
    (firstIndex : Fin 11) (secondIndex : Fin 16) (position : Fin 15) :
    supportNormalizerTailPerm firstIndex secondIndex
        (ProfileDTripleJoinReduction.blockVertex 1 position.val) =
      ProfileDTripleJoinReduction.blockVertex 1
        ((u15SupportEquiv firstIndex).symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [supportNormalizerTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

@[simp] theorem supportNormalizerTailPerm_blockTwo
    (firstIndex : Fin 11) (secondIndex : Fin 16) (position : Fin 16) :
    supportNormalizerTailPerm firstIndex secondIndex
        (ProfileDTripleJoinReduction.blockVertex 2 position.val) =
      ProfileDTripleJoinReduction.blockVertex 2
        ((u16SupportEquiv secondIndex).symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp only [supportNormalizerTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo _

theorem u15SupportEquiv_symm_preserves
    (i : Fin 11) (left right : Fin 15) (hlr : left ≠ right) :
    k15Template false ((u15SupportEquiv i).symm left)
        ((u15SupportEquiv i).symm right) =
      k15Template false left right := by
  have h := (u15SupportMap_preserves i
    ((u15SupportEquiv i).symm left)
    ((u15SupportEquiv i).symm right)
    ((u15SupportEquiv i).symm.injective.ne hlr)).symm
  change k15Template false ((u15SupportEquiv i).symm left)
      ((u15SupportEquiv i).symm right) =
    k15Template false
      (u15SupportEquiv i ((u15SupportEquiv i).symm left))
      (u15SupportEquiv i ((u15SupportEquiv i).symm right)) at h
  simpa using h

theorem u16SupportEquiv_symm_preserves
    (i : Fin 16) (left right : Fin 16) (hlr : left ≠ right) :
    k16Template false ((u16SupportEquiv i).symm left)
        ((u16SupportEquiv i).symm right) =
      k16Template false left right := by
  have h := (u16SupportMap_preserves i
    ((u16SupportEquiv i).symm left)
    ((u16SupportEquiv i).symm right)
    ((u16SupportEquiv i).symm.injective.ne hlr)).symm
  change k16Template false ((u16SupportEquiv i).symm left)
      ((u16SupportEquiv i).symm right) =
    k16Template false
      (u16SupportEquiv i ((u16SupportEquiv i).symm left))
      (u16SupportEquiv i ((u16SupportEquiv i).symm right)) at h
  simpa using h

theorem supportNormalizer_templateCanonical
    (tail : ProfileDTripleJoinReduction.Witness .uuu)
    (firstIndex : Fin 11) (secondIndex : Fin 16) :
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
    let leftFin : Fin 15 := ⟨left, by simpa [blockSize] using hleft⟩
    let rightFin : Fin 15 := ⟨right, by simpa [blockSize] using hright⟩
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
        tail 0 (by decide) leftFin rightFin hne
    have htwisted : Kind.uuu.twisted (0 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    simpa [blockSize, SingleRootStarCNF.templateColor,
      SingleRootStarCNF.fin15, leftFin, rightFin,
      Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hedge
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
    let leftFin : Fin 15 := ⟨left, by simpa [blockSize] using hleft⟩
    let rightFin : Fin 15 := ⟨right, by simpa [blockSize] using hright⟩
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
          ((u15SupportEquiv firstIndex).symm leftFin)
          ((u15SupportEquiv firstIndex).symm rightFin)
          ((u15SupportEquiv firstIndex).symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1
            ((u15SupportEquiv firstIndex).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 1
            ((u15SupportEquiv firstIndex).symm rightFin).val) =
          SingleRootStarCNF.canonicalPalette 2
            (k15Template false
              ((u15SupportEquiv firstIndex).symm leftFin)
              ((u15SupportEquiv firstIndex).symm rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 2
            (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 2)
          (u15SupportEquiv_symm_preserves firstIndex leftFin rightFin hne)
      _ = SingleRootStarCNF.canonicalPalette 2
            (SingleRootStarCNF.templateColor 15 false left right) := by
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
    let leftFin : Fin 16 := ⟨left, by simpa [blockSize] using hleft⟩
    let rightFin : Fin 16 := ⟨right, by simpa [blockSize] using hright⟩
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
        tail 2 (by decide)
          ((u16SupportEquiv secondIndex).symm leftFin)
          ((u16SupportEquiv secondIndex).symm rightFin)
          ((u16SupportEquiv secondIndex).symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (2 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 2
            ((u16SupportEquiv secondIndex).symm leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 2
            ((u16SupportEquiv secondIndex).symm rightFin).val) =
          SingleRootStarCNF.canonicalPalette 3
            (k16Template false
              ((u16SupportEquiv secondIndex).symm leftFin)
              ((u16SupportEquiv secondIndex).symm rightFin)) := by
        simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 3
            (k16Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 3)
          (u16SupportEquiv_symm_preserves secondIndex leftFin rightFin hne)
      _ = SingleRootStarCNF.canonicalPalette 3
            (SingleRootStarCNF.templateColor 16 false left right) := by
        simp [blockSize, SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin16, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]

/-! ## Canonical support coordinates and induced position permutations -/

def normalizedSupportKind (i : Fin 11) : SupportKind :=
  match (u15SupportRepresentative i).val with
  | 0 => .support0
  | 2 => .support2
  | _ => .support7

theorem supportIndex_normalizedSupportKind (i : Fin 11) :
    ProfileDUUUDegreeTenCatalogOrbits61.supportIndex
        (normalizedSupportKind i) =
      u15SupportRepresentative i := by
  fin_cases i <;> decide

def canonicalCoordinates : SupportKind → MatrixCoordinates 0
  | .support0 => ProfileDDegreeTenMatrixLeafUUU0S0M25.matrixCoordinates
  | .support2 => ProfileDDegreeTenMatrixLeafTenDataUUU0.matrixCoordinatesSupportTwo
  | .support7 => ProfileDDegreeTenMatrixLeafTenDataUUU0.matrixCoordinatesSupportSeven

theorem canonicalCoordinates_first_positions (kind : SupportKind) :
    (canonicalCoordinates kind).first.positions =
      u15Support
        (ProfileDUUUDegreeTenCatalogOrbits61.supportIndex kind) := by
  cases kind <;> decide

theorem canonicalCoordinates_second_positions (kind : SupportKind) :
    (canonicalCoordinates kind).second.positions = u16Support 0 := by
  cases kind <;> decide

noncomputable def orderedFiveSupportEquiv {n : Nat}
    (support : OrderedFiveSupport n) :
    ProfileDHighOwnFiveRowSplit61.FiveVertex ≃
      {p : Fin n // p ∈ support.positions} :=
  Equiv.ofBijective
    (fun a =>
      ⟨support.embedding a, by
        unfold OrderedFiveSupport.positions
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩)
    ⟨by
      intro left right heq
      exact support.embedding.injective (congrArg Subtype.val heq),
    by
      rintro ⟨p, hp⟩
      unfold OrderedFiveSupport.positions at hp
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hp
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha⟩

noncomputable def supportSubtypeEquiv {n : Nat}
    (source target : OrderedFiveSupport n)
    (localPerm : Equiv.Perm (Fin n))
    (hpositions : ∀ p,
      p ∈ target.positions ↔ localPerm p ∈ source.positions) :
    {p : Fin n // p ∈ target.positions} ≃
      {p : Fin n // p ∈ source.positions} where
  toFun p := ⟨localPerm p, (hpositions p).mp p.property⟩
  invFun p := ⟨localPerm.symm p, (hpositions (localPerm.symm p)).mpr (by
    simpa using p.property)⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; simp

noncomputable def orderedSupportPositionPerm {n : Nat}
    (source target : OrderedFiveSupport n)
    (localPerm : Equiv.Perm (Fin n))
    (hpositions : ∀ p,
      p ∈ target.positions ↔ localPerm p ∈ source.positions) :
    Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex :=
  (orderedFiveSupportEquiv target).trans
    ((supportSubtypeEquiv source target localPerm hpositions).trans
      (orderedFiveSupportEquiv source).symm)

theorem orderedSupportPositionPerm_embedding {n : Nat}
    (source target : OrderedFiveSupport n)
    (localPerm : Equiv.Perm (Fin n))
    (hpositions : ∀ p,
      p ∈ target.positions ↔ localPerm p ∈ source.positions)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    localPerm (target.embedding a) =
      source.embedding
        (orderedSupportPositionPerm source target localPerm hpositions a) := by
  unfold orderedSupportPositionPerm
  have h := congrArg Subtype.val
    ((orderedFiveSupportEquiv source).apply_symm_apply
      (supportSubtypeEquiv source target localPerm hpositions
        (orderedFiveSupportEquiv target a)))
  dsimp [orderedFiveSupportEquiv, supportSubtypeEquiv] at h
  simpa [Equiv.trans_apply, orderedFiveSupportEquiv,
    supportSubtypeEquiv] using h.symm

/-! ## Blockwise permutations of the labelled fifteen-vertex host -/

abbrev ThreeFiveCoordinates :=
  (ProfileDHighOwnFiveRowSplit61.FiveVertex ⊕
    ProfileDHighOwnFiveRowSplit61.FiveVertex) ⊕
      ProfileDHighOwnFiveRowSplit61.FiveVertex

def threeFiveEquiv : ThreeFiveCoordinates ≃ Fin 15 :=
  (Equiv.sumCongr finSumFinEquiv
    (Equiv.refl ProfileDHighOwnFiveRowSplit61.FiveVertex)).trans
      finSumFinEquiv

@[simp] theorem threeFiveEquiv_blockZero
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    threeFiveEquiv (.inl (.inl position)) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position := by
  apply Fin.ext
  change (finSumFinEquiv
    (Sum.inl (finSumFinEquiv (Sum.inl position)))).val = _
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
  simp [ProfileDUUUDegreeTenCatalogOrbits61.blockVertex]
  omega

@[simp] theorem threeFiveEquiv_blockOne
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    threeFiveEquiv (.inl (.inr position)) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position := by
  apply Fin.ext
  change (finSumFinEquiv
    (Sum.inl (finSumFinEquiv (Sum.inr position)))).val = _
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp [ProfileDUUUDegreeTenCatalogOrbits61.blockVertex]
  omega

@[simp] theorem threeFiveEquiv_blockTwo
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    threeFiveEquiv (.inr position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position := by
  apply Fin.ext
  change (finSumFinEquiv (Sum.inr position)).val = _
  rw [finSumFinEquiv_apply_right]
  simp [ProfileDUUUDegreeTenCatalogOrbits61.blockVertex]
  omega

noncomputable def matrixBlockPerm
    (p0 p1 p2 : Equiv.Perm
      ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    Equiv.Perm (Fin 15) :=
  threeFiveEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.sumCongr p0 p1) p2).trans threeFiveEquiv)

@[simp] theorem matrixBlockPerm_blockZero
    (p0 p1 p2 : Equiv.Perm
      ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    matrixBlockPerm p0 p1 p2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 (p0 position) := by
  calc
    matrixBlockPerm p0 p1 p2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position) =
      matrixBlockPerm p0 p1 p2 (threeFiveEquiv (.inl (.inl position))) := by
        rw [threeFiveEquiv_blockZero]
    _ = threeFiveEquiv (.inl (.inl (p0 position))) := by
      simp only [matrixBlockPerm, Equiv.trans_apply,
        Equiv.symm_apply_apply]
      rfl
    _ = _ := threeFiveEquiv_blockZero _

@[simp] theorem matrixBlockPerm_blockOne
    (p0 p1 p2 : Equiv.Perm
      ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    matrixBlockPerm p0 p1 p2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 (p1 position) := by
  calc
    matrixBlockPerm p0 p1 p2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position) =
      matrixBlockPerm p0 p1 p2 (threeFiveEquiv (.inl (.inr position))) := by
        rw [threeFiveEquiv_blockOne]
    _ = threeFiveEquiv (.inl (.inr (p1 position))) := by
      simp only [matrixBlockPerm, Equiv.trans_apply,
        Equiv.symm_apply_apply]
      rfl
    _ = _ := threeFiveEquiv_blockOne _

@[simp] theorem matrixBlockPerm_blockTwo
    (p0 p1 p2 : Equiv.Perm
      ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    matrixBlockPerm p0 p1 p2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 (p2 position) := by
  calc
    matrixBlockPerm p0 p1 p2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position) =
      matrixBlockPerm p0 p1 p2 (threeFiveEquiv (.inr position)) := by
        rw [threeFiveEquiv_blockTwo]
    _ = threeFiveEquiv (.inr (p2 position)) := by
      simp only [matrixBlockPerm, Equiv.trans_apply,
        Equiv.symm_apply_apply]
      rfl
    _ = _ := threeFiveEquiv_blockTwo _

@[simp] theorem catalogBlockVertex_group
    (block : Fin 3)
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex
      block position).val / 5 = block.val := by
  fin_cases block <;> fin_cases position <;> decide

theorem matrixBlockPerm_preserves_group
    (p0 p1 p2 : Equiv.Perm
      ProfileDHighOwnFiveRowSplit61.FiveVertex) (i : Fin 15) :
    (matrixBlockPerm p0 p1 p2 i).val / 5 = i.val / 5 := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixBlockPerm_blockZero]
      simp
    · rw [threeFiveEquiv_blockOne, matrixBlockPerm_blockOne]
      simp
  · rw [threeFiveEquiv_blockTwo, matrixBlockPerm_blockTwo]
    simp

theorem matrixBlockPerm_preserves_cross_group
    (p0 p1 p2 : Equiv.Perm
      ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (left right : Fin 15)
    (hgroups : left.val / 5 ≠ right.val / 5) :
    (matrixBlockPerm p0 p1 p2 left).val / 5 ≠
      (matrixBlockPerm p0 p1 p2 right).val / 5 := by
  simpa [matrixBlockPerm_preserves_group] using hgroups

@[simp] theorem catalogBlockZero_eq_freeMatrixIndex
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position =
      freeMatrixIndex position := by
  apply Fin.ext
  simp [ProfileDUUUDegreeTenCatalogOrbits61.blockVertex,
    freeMatrixIndex]
  omega

@[simp] theorem catalogBlockOne_eq_firstForeignMatrixIndex
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position =
      firstForeignMatrixIndex position := by
  apply Fin.ext
  simp [ProfileDUUUDegreeTenCatalogOrbits61.blockVertex,
    firstForeignMatrixIndex]
  omega

@[simp] theorem catalogBlockTwo_eq_secondForeignMatrixIndex
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position =
      secondForeignMatrixIndex position := by
  apply Fin.ext
  simp [ProfileDUUUDegreeTenCatalogOrbits61.blockVertex,
    secondForeignMatrixIndex]
  omega

/-! ## Support normalization of an exact branch -/

theorem firstNormalizer_positions
    {sourceCoordinates : MatrixCoordinates 0}
    (firstIndex : Fin 11)
    (hsource : sourceCoordinates.first.positions = u15Support firstIndex)
    (p : Fin 15) :
    p ∈ (canonicalCoordinates (normalizedSupportKind firstIndex)).first.positions ↔
      (u15SupportEquiv firstIndex).symm p ∈
        sourceCoordinates.first.positions := by
  have htarget :
      (canonicalCoordinates
        (normalizedSupportKind firstIndex)).first.positions =
        u15Support (u15SupportRepresentative firstIndex) :=
    (canonicalCoordinates_first_positions
      (normalizedSupportKind firstIndex)).trans
        (congrArg u15Support (supportIndex_normalizedSupportKind firstIndex))
  constructor
  · intro hp
    have hpRep : p ∈ u15Support (u15SupportRepresentative firstIndex) :=
      htarget ▸ hp
    have hpImage : p ∈ (u15Support firstIndex).image
        (u15SupportMap firstIndex) :=
      (u15SupportMap_image firstIndex).symm ▸ hpRep
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    have hqeq : (u15SupportEquiv firstIndex).symm p = q := by
      apply (u15SupportEquiv firstIndex).injective
      rw [Equiv.apply_symm_apply]
      exact hqp.symm
    exact hsource.symm ▸ (hqeq.symm ▸ hq)
  · intro hp
    have hpSource : (u15SupportEquiv firstIndex).symm p ∈
        u15Support firstIndex := hsource ▸ hp
    have hpImage : p ∈ (u15Support firstIndex).image
        (u15SupportMap firstIndex) := by
      apply Finset.mem_image.mpr
      refine ⟨(u15SupportEquiv firstIndex).symm p, hpSource, ?_⟩
      exact (u15SupportEquiv firstIndex).apply_symm_apply p
    have hpRep : p ∈ u15Support (u15SupportRepresentative firstIndex) :=
      u15SupportMap_image firstIndex ▸ hpImage
    exact htarget.symm ▸ hpRep

theorem secondNormalizer_positions
    {sourceCoordinates : MatrixCoordinates 0}
    (firstIndex : Fin 11)
    (secondIndex : Fin 16)
    (hsource : sourceCoordinates.second.positions = u16Support secondIndex)
    (p : Fin 16) :
    p ∈ (canonicalCoordinates (normalizedSupportKind firstIndex)).second.positions ↔
      (u16SupportEquiv secondIndex).symm p ∈
        sourceCoordinates.second.positions := by
  have htarget :
      (canonicalCoordinates
        (normalizedSupportKind firstIndex)).second.positions = u16Support 0 :=
    canonicalCoordinates_second_positions _
  constructor
  · intro hp
    have hpRep : p ∈ u16Support 0 := htarget ▸ hp
    have hpImage : p ∈ (u16Support secondIndex).image
        (u16SupportMap secondIndex) :=
      (u16SupportMap_image secondIndex).symm ▸ hpRep
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
    have hqeq : (u16SupportEquiv secondIndex).symm p = q := by
      apply (u16SupportEquiv secondIndex).injective
      rw [Equiv.apply_symm_apply]
      exact hqp.symm
    exact hsource.symm ▸ (hqeq.symm ▸ hq)
  · intro hp
    have hpSource : (u16SupportEquiv secondIndex).symm p ∈
        u16Support secondIndex := hsource ▸ hp
    have hpImage : p ∈ (u16Support secondIndex).image
        (u16SupportMap secondIndex) := by
      apply Finset.mem_image.mpr
      refine ⟨(u16SupportEquiv secondIndex).symm p, hpSource, ?_⟩
      exact (u16SupportEquiv secondIndex).apply_symm_apply p
    have hpRep : p ∈ u16Support 0 :=
      u16SupportMap_image secondIndex ▸ hpImage
    exact htarget.symm ▸ hpRep

noncomputable def firstSupportPositionPerm
    (sourceCoordinates : MatrixCoordinates 0) (firstIndex : Fin 11)
    (hsource : sourceCoordinates.first.positions = u15Support firstIndex) :
    Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex :=
  by
    simp only [ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
      blockSize] at hsource ⊢
    exact orderedSupportPositionPerm sourceCoordinates.first
      (canonicalCoordinates (normalizedSupportKind firstIndex)).first
      (u15SupportEquiv firstIndex).symm
      (firstNormalizer_positions firstIndex hsource)

noncomputable def secondSupportPositionPerm
    (sourceCoordinates : MatrixCoordinates 0) (firstIndex : Fin 11)
    (secondIndex : Fin 16)
    (hsource : sourceCoordinates.second.positions = u16Support secondIndex) :
    Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex :=
  by
    simp only [ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
      blockSize] at hsource ⊢
    exact orderedSupportPositionPerm sourceCoordinates.second
      (canonicalCoordinates (normalizedSupportKind firstIndex)).second
      (u16SupportEquiv secondIndex).symm
      (secondNormalizer_positions firstIndex secondIndex hsource)

theorem firstSupportPositionPerm_embedding
    (sourceCoordinates : MatrixCoordinates 0) (firstIndex : Fin 11)
    (hsource : sourceCoordinates.first.positions = u15Support firstIndex)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    (u15SupportEquiv firstIndex).symm
        ((canonicalCoordinates
          (normalizedSupportKind firstIndex)).first.embedding a) =
      sourceCoordinates.first.embedding
        (firstSupportPositionPerm sourceCoordinates firstIndex hsource a) := by
  exact orderedSupportPositionPerm_embedding _ _ _ _ a

theorem secondSupportPositionPerm_embedding
    (sourceCoordinates : MatrixCoordinates 0) (firstIndex : Fin 11)
    (secondIndex : Fin 16)
    (hsource : sourceCoordinates.second.positions = u16Support secondIndex)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    (u16SupportEquiv secondIndex).symm
        ((canonicalCoordinates
          (normalizedSupportKind firstIndex)).second.embedding a) =
      sourceCoordinates.second.embedding
        (secondSupportPositionPerm sourceCoordinates firstIndex secondIndex
          hsource a) := by
  exact orderedSupportPositionPerm_embedding _ _ _ _ a

@[simp] theorem matrixCoordinates_vertex_blockZero
    (coordinates : MatrixCoordinates 0)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    coordinates.vertex
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 a) =
      freeVertex a := by
  rw [catalogBlockZero_eq_freeMatrixIndex]
  exact coordinates.vertex_free a

@[simp] theorem matrixCoordinates_vertex_blockOne
    (coordinates : MatrixCoordinates 0)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    coordinates.vertex
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 a) =
      tailVertex
        (ProfileDTripleJoinReduction.blockVertex 1
          (coordinates.first.embedding a).val) := by
  rw [catalogBlockOne_eq_firstForeignMatrixIndex]
  simpa [ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock] using
    coordinates.vertex_first a

@[simp] theorem matrixCoordinates_vertex_blockTwo
    (coordinates : MatrixCoordinates 0)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    coordinates.vertex
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 a) =
      tailVertex
        (ProfileDTripleJoinReduction.blockVertex 2
          (coordinates.second.embedding a).val) := by
  rw [catalogBlockTwo_eq_secondForeignMatrixIndex]
  simpa [ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock] using
    coordinates.vertex_second a

noncomputable def supportNormalizationMatrixPerm
    (sourceCoordinates : MatrixCoordinates 0)
    (firstIndex : Fin 11) (secondIndex : Fin 16)
    (hfirst : sourceCoordinates.first.positions = u15Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = u16Support secondIndex) :
    Equiv.Perm (Fin 15) :=
  matrixBlockPerm (Equiv.refl _)
    (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
    (secondSupportPositionPerm sourceCoordinates firstIndex secondIndex hsecond)

theorem supportNormalization_coordinates_covariant
    (sourceCoordinates : MatrixCoordinates 0)
    (firstIndex : Fin 11) (secondIndex : Fin 16)
    (hfirst : sourceCoordinates.first.positions = u15Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = u16Support secondIndex)
    (i : Fin 15) :
    totalVertexPerm (supportNormalizerTailPerm firstIndex secondIndex)
        ((canonicalCoordinates
          (normalizedSupportKind firstIndex)).vertex i) =
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
            (secondSupportPositionPerm sourceCoordinates firstIndex secondIndex
              hsecond)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position))
      rw [matrixBlockPerm_blockZero, matrixCoordinates_vertex_blockZero]
      rfl
    · rw [threeFiveEquiv_blockOne, matrixCoordinates_vertex_blockOne,
        totalVertexPerm_tail, supportNormalizerTailPerm_blockOne]
      change tailVertex
          (ProfileDTripleJoinReduction.blockVertex 1
            ((u15SupportEquiv firstIndex).symm
              ((canonicalCoordinates
                (normalizedSupportKind firstIndex)).first.embedding
                  position)).val) =
        sourceCoordinates.vertex
          (matrixBlockPerm (Equiv.refl _)
            (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
            (secondSupportPositionPerm sourceCoordinates firstIndex secondIndex
              hsecond)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position))
      rw [matrixBlockPerm_blockOne, matrixCoordinates_vertex_blockOne,
        firstSupportPositionPerm_embedding]
  · rw [threeFiveEquiv_blockTwo, matrixCoordinates_vertex_blockTwo,
      totalVertexPerm_tail, supportNormalizerTailPerm_blockTwo]
    change tailVertex
        (ProfileDTripleJoinReduction.blockVertex 2
          ((u16SupportEquiv secondIndex).symm
            ((canonicalCoordinates
              (normalizedSupportKind firstIndex)).second.embedding
                position)).val) =
      sourceCoordinates.vertex
        (matrixBlockPerm (Equiv.refl _)
          (firstSupportPositionPerm sourceCoordinates firstIndex hfirst)
          (secondSupportPositionPerm sourceCoordinates firstIndex secondIndex
            hsecond)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position))
    rw [matrixBlockPerm_blockTwo, matrixCoordinates_vertex_blockTwo,
      secondSupportPositionPerm_embedding]

noncomputable def supportNormalizedMatrix
    (sourceCoordinates : MatrixCoordinates 0)
    (sourceMatrix : EdgeColoring (Fin 15) (Fin 4))
    (firstIndex : Fin 11) (secondIndex : Fin 16)
    (hfirst : sourceCoordinates.first.positions = u15Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = u16Support secondIndex) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring sourceMatrix
    (supportNormalizationMatrixPerm sourceCoordinates firstIndex secondIndex
      hfirst hsecond)

noncomputable def normalizeExactDegreeTenSupports
    {sourceCoordinates : MatrixCoordinates 0}
    {sourceMatrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      sourceCoordinates sourceMatrix)
    (firstIndex : Fin 11) (secondIndex : Fin 16)
    (hfirst : sourceCoordinates.first.positions = u15Support firstIndex)
    (hsecond : sourceCoordinates.second.positions = u16Support secondIndex) :
    ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates (normalizedSupportKind firstIndex))
      (supportNormalizedMatrix sourceCoordinates sourceMatrix firstIndex
        secondIndex hfirst hsecond) :=
  transportExactDegreeTenMatrixBranch exact
    (supportNormalizerTailPerm firstIndex secondIndex)
    (supportNormalizer_templateCanonical
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      firstIndex secondIndex)
    (by rw [supportNormalizerTailPerm_blockZero])
    (u15SupportEquiv firstIndex).symm
    (u16SupportEquiv secondIndex).symm
    (supportNormalizationMatrixPerm sourceCoordinates firstIndex secondIndex
      hfirst hsecond)
    (supportNormalizerTailPerm_blockOne firstIndex secondIndex)
    (supportNormalizerTailPerm_blockTwo firstIndex secondIndex)
    (firstNormalizer_positions firstIndex hfirst)
    (secondNormalizer_positions firstIndex secondIndex hsecond)
    (supportNormalization_coordinates_covariant sourceCoordinates firstIndex
      secondIndex hfirst hsecond)
    (matrixBlockPerm_preserves_cross_group _ _ _)
    (by intro left right _; rfl)

/-! ## The semantic host induced by normalized coordinates -/

def exactHost
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) : EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring
    (totalColoring
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension)
    coordinates.vertex

theorem exactHost_noMono
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    NoMonochromaticTriangle (exactHost exact) := by
  exact noMono_pullback _ coordinates.vertex coordinates.vertex.injective
    (totalColoring_noMono
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension)

theorem selectedTotalVertex_ne_matrixVertex
    (coordinates : MatrixCoordinates 0) (i : Fin 15) :
    tailVertex
        (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val) ≠
      coordinates.vertex i := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixCoordinates_vertex_blockZero]
      intro h
      have := congrArg splitVertex h
      simp at this
    · rw [threeFiveEquiv_blockOne, matrixCoordinates_vertex_blockOne]
      exact tailVertex_injective.ne
        (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
          0 1 (by decide) SelectedPosition.isLt (by
            have hp := (coordinates.first.embedding position).isLt
            change (coordinates.first.embedding position).val < 15 at hp
            exact hp))
  · rw [threeFiveEquiv_blockTwo, matrixCoordinates_vertex_blockTwo]
    exact tailVertex_injective.ne
      (ProfileDColumnOwnColorIncidence61.blockVertex_ne_of_block_ne
        0 2 (by decide) SelectedPosition.isLt (by
          have hp := (coordinates.second.embedding position).isLt
          change (coordinates.second.embedding position).val < 16 at hp
          exact hp))

theorem selected_to_matrixVertex_ownColor
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) (i : Fin 15) :
    totalColoring
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
        (tailVertex
          (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val))
        (coordinates.vertex i) = 1 := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixCoordinates_vertex_blockZero]
      rw [(totalColoring
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension).color_symm,
        totalColoring_free_tail]
      change exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
          position
          (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val) = 1
      exact exact.branch.allFiveOwn position
    · rw [threeFiveEquiv_blockOne, matrixCoordinates_vertex_blockOne,
        totalColoring_tail_tail]
      apply (exact.firstSupportExact
        (coordinates.first.embedding position)).mp
      unfold OrderedFiveSupport.positions
      exact Finset.mem_image.mpr
        ⟨position, Finset.mem_univ _, rfl⟩
  · rw [threeFiveEquiv_blockTwo, matrixCoordinates_vertex_blockTwo,
      totalColoring_tail_tail]
    apply (exact.secondSupportExact
      (coordinates.second.embedding position)).mp
    unfold OrderedFiveSupport.positions
    exact Finset.mem_image.mpr
      ⟨position, Finset.mem_univ _, rfl⟩

theorem exactHost_avoids_ownColor
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∀ u v, u ≠ v → exactHost exact u v ≠ 1 := by
  intro u v huv hcolor
  let selected := tailVertex
    (ProfileDTripleJoinReduction.blockVertex 0 SelectedPosition.val)
  apply totalColoring_noMono
    exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
    selected (coordinates.vertex u) (coordinates.vertex v)
  · exact ⟨selectedTotalVertex_ne_matrixVertex coordinates u,
      selectedTotalVertex_ne_matrixVertex coordinates v,
      coordinates.vertex.injective.ne huv⟩
  · exact ⟨
      (selected_to_matrixVertex_ownColor exact u).trans
        (selected_to_matrixVertex_ownColor exact v).symm,
      (selected_to_matrixVertex_ownColor exact v).trans hcolor.symm⟩

theorem catalogRowZero_blockZero_internal
    (kind : SupportKind)
    (left right : ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hne : left ≠ right) :
    decodeRemainingColor 0 (!canonicalCycleWord.coloring left right) =
      catalogMatrixColor kind 0
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 left)
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 right) := by
  cases kind <;> fin_cases left <;> fin_cases right <;>
    simp_all <;> decide

theorem catalogRowZero_blockOne_internal
    (kind : SupportKind)
    (left right : ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hne : left ≠ right) :
    SingleRootStarCNF.canonicalPalette 2
        (k15Template false
          ((canonicalCoordinates kind).first.embedding left)
          ((canonicalCoordinates kind).first.embedding right)) =
      catalogMatrixColor kind 0
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 left)
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 right) := by
  cases kind <;> fin_cases left <;> fin_cases right <;>
    simp_all <;> decide

theorem catalogRowZero_blockTwo_internal
    (kind : SupportKind)
    (left right : ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hne : left ≠ right) :
    SingleRootStarCNF.canonicalPalette 3
        (k16Template false
          ((canonicalCoordinates kind).second.embedding left)
          ((canonicalCoordinates kind).second.embedding right)) =
      catalogMatrixColor kind 0
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 left)
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 right) := by
  cases kind <;> fin_cases left <;> fin_cases right <;>
    simp_all <;> decide

theorem exactHost_hasCanonicalInternalBlocks
    (kind : SupportKind)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) matrix) :
    HasCanonicalInternalBlocks kind (exactHost exact) := by
  intro group left right hne
  fin_cases group
  · change
      totalColoring
          exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
          ((canonicalCoordinates kind).vertex
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 left))
          ((canonicalCoordinates kind).vertex
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 right)) =
        catalogMatrixColor kind 0
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 left)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 right)
    rw [matrixCoordinates_vertex_blockZero,
      matrixCoordinates_vertex_blockZero, totalColoring_free_free,
      exact.branch.insideCanonical left right hne]
    exact catalogRowZero_blockZero_internal kind left right hne
  · change
      totalColoring
          exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
          ((canonicalCoordinates kind).vertex
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 left))
          ((canonicalCoordinates kind).vertex
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 right)) =
        catalogMatrixColor kind 0
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 left)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 right)
    rw [matrixCoordinates_vertex_blockOne,
      matrixCoordinates_vertex_blockOne, totalColoring_tail_tail]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
        1 (by decide)
        ((canonicalCoordinates kind).first.embedding left)
        ((canonicalCoordinates kind).first.embedding right)
        ((canonicalCoordinates kind).first.embedding.injective.ne hne)
    have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    exact hedge.trans (catalogRowZero_blockOne_internal kind left right hne)
  · change
      totalColoring
          exact.branch.toDegreeFlooredFiveExtension.toFiveExtension
          ((canonicalCoordinates kind).vertex
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 left))
          ((canonicalCoordinates kind).vertex
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 right)) =
        catalogMatrixColor kind 0
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 left)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 right)
    rw [matrixCoordinates_vertex_blockTwo,
      matrixCoordinates_vertex_blockTwo, totalColoring_tail_tail]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
        2 (by decide)
        ((canonicalCoordinates kind).second.embedding left)
        ((canonicalCoordinates kind).second.embedding right)
        ((canonicalCoordinates kind).second.embedding.injective.ne hne)
    have htwisted : Kind.uuu.twisted (2 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    exact hedge.trans (catalogRowZero_blockTwo_internal kind left right hne)

theorem catalogEquation_on_cross_indices
    (kind : SupportKind) (c : EdgeColoring (Fin 15) (Fin 4))
    (i : Fin 600)
    (hcatalog : ∀ leftBlock rightBlock : Fin 3,
      leftBlock ≠ rightBlock → ∀ left right : Fin 5,
        c (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right) =
          catalogMatrixColor kind i
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right))
    (left right : Fin 15) (hgroups : left.val / 5 ≠ right.val / 5) :
    c left right = catalogMatrixColor kind i left right := by
  have hleft : left = threeFiveEquiv (threeFiveEquiv.symm left) :=
    (threeFiveEquiv.apply_symm_apply left).symm
  have hright : right = threeFiveEquiv (threeFiveEquiv.symm right) :=
    (threeFiveEquiv.apply_symm_apply right).symm
  rw [hleft, hright] at hgroups ⊢
  generalize threeFiveEquiv.symm left = leftCoordinate at hgroups ⊢
  generalize threeFiveEquiv.symm right = rightCoordinate at hgroups ⊢
  rcases leftCoordinate with leftPart | leftPosition
  · rcases leftPart with leftPosition | leftPosition
    · rcases rightCoordinate with rightPart | rightPosition
      · rcases rightPart with rightPosition | rightPosition
        · exfalso
          rw [threeFiveEquiv_blockZero, threeFiveEquiv_blockZero] at hgroups
          apply hgroups
          rw [catalogBlockVertex_group, catalogBlockVertex_group]
        · rw [threeFiveEquiv_blockZero, threeFiveEquiv_blockOne]
          exact hcatalog 0 1 (by decide) leftPosition rightPosition
      · rw [threeFiveEquiv_blockZero, threeFiveEquiv_blockTwo]
        exact hcatalog 0 2 (by decide) leftPosition rightPosition
    · rcases rightCoordinate with rightPart | rightPosition
      · rcases rightPart with rightPosition | rightPosition
        · rw [threeFiveEquiv_blockOne, threeFiveEquiv_blockZero]
          exact hcatalog 1 0 (by decide) leftPosition rightPosition
        · exfalso
          rw [threeFiveEquiv_blockOne, threeFiveEquiv_blockOne] at hgroups
          apply hgroups
          rw [catalogBlockVertex_group, catalogBlockVertex_group]
      · rw [threeFiveEquiv_blockOne, threeFiveEquiv_blockTwo]
        exact hcatalog 1 2 (by decide) leftPosition rightPosition
  · rcases rightCoordinate with rightPart | rightPosition
    · rcases rightPart with rightPosition | rightPosition
      · rw [threeFiveEquiv_blockTwo, threeFiveEquiv_blockZero]
        exact hcatalog 2 0 (by decide) leftPosition rightPosition
      · rw [threeFiveEquiv_blockTwo, threeFiveEquiv_blockOne]
        exact hcatalog 2 1 (by decide) leftPosition rightPosition
    · exfalso
      rw [threeFiveEquiv_blockTwo, threeFiveEquiv_blockTwo] at hgroups
      apply hgroups
      rw [catalogBlockVertex_group, catalogBlockVertex_group]

def catalogEdgeColoring (kind : SupportKind) (i : Fin 600) :
    EdgeColoring (Fin 15) (Fin 4) where
  color := catalogMatrixColor kind i
  color_symm := catalogMatrixColor_symm kind i

noncomputable def exactBranchWithCatalogMatrix
    (kind : SupportKind)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) matrix)
    (i : Fin 600)
    (hcatalog : ∀ left right : Fin 15,
      left.val / 5 ≠ right.val / 5 →
        exactHost exact left right = catalogMatrixColor kind i left right) :
    ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) (catalogEdgeColoring kind i) where
  branch := exact.branch
  tailOwnDegreeTen := exact.tailOwnDegreeTen
  firstSupportExact := exact.firstSupportExact
  secondSupportExact := exact.secondSupportExact
  matrixExact := by
    intro left right hgroups
    exact hcatalog left right hgroups

theorem exists_catalogExactBranch_of_normalized
    (kind : SupportKind)
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) matrix) :
    ∃ i : Fin 600,
      Nonempty (ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
        (canonicalCoordinates kind) (catalogEdgeColoring kind i)) := by
  obtain ⟨i, hcatalog⟩ :=
    exists_catalogMatrix_of_normalizedHost kind (exactHost exact)
      (exactHost_noMono exact) (exactHost_avoids_ownColor exact)
      (exactHost_hasCanonicalInternalBlocks kind exact)
  refine ⟨i, ⟨exactBranchWithCatalogMatrix kind exact i ?_⟩⟩
  intro left right hgroups
  exact catalogEquation_on_cross_indices kind (exactHost exact) i hcatalog
    left right hgroups

theorem exists_catalogExactBranch_of_exact
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ kind : SupportKind, ∃ i : Fin 600,
      Nonempty (ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
        (canonicalCoordinates kind) (catalogEdgeColoring kind i)) := by
  obtain ⟨firstIndex, hfirst⟩ := exists_firstSupportIndex exact
  obtain ⟨secondIndex, hsecond⟩ := exists_secondSupportIndex exact
  let normalized := normalizeExactDegreeTenSupports exact firstIndex secondIndex
    hfirst hsecond
  obtain ⟨i, ⟨hexact⟩⟩ :=
    exists_catalogExactBranch_of_normalized
      (normalizedSupportKind firstIndex) normalized
  exact ⟨normalizedSupportKind firstIndex, i, ⟨hexact⟩⟩

/-! ## Relabeling the retained free five-cycle -/

noncomputable def totalFreeVertexPerm
    (perm : Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    Equiv.Perm ProfileDHighOwnFiveSupportC5CNF.TotalVertex :=
  totalDecompEquiv.trans
    ((Equiv.sumCongr perm (Equiv.refl ProfileDRowExtension.TailVertex)).trans
      totalDecompEquiv.symm)

@[simp] theorem totalFreeVertexPerm_free
    (perm : Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (a : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    totalFreeVertexPerm perm (freeVertex a) = freeVertex (perm a) := by
  simp [totalFreeVertexPerm, totalDecompEquiv, mergeVertex]

@[simp] theorem totalFreeVertexPerm_tail
    (perm : Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (x : ProfileDRowExtension.TailVertex) :
    totalFreeVertexPerm perm (tailVertex x) = tailVertex x := by
  simp [totalFreeVertexPerm, totalDecompEquiv, mergeVertex]

noncomputable def transportCanonicalBranchByFreePerm
    {kind : ProfileDTripleJoinReduction.Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (perm : Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hinside : ∀ a b, a ≠ b →
      branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (perm a) (perm b) =
        decodeRemainingColor block (!canonicalCycleWord.coloring a b)) :
    CanonicalBranch kind block position where
  toDegreeFlooredFiveExtension :=
    transportDegreeFlooredFiveExtension perm
      branch.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro a
    exact branch.allFiveOwn (perm a)
  insideCanonical := hinside
  tailOwnDegreeLower := branch.tailOwnDegreeLower
  tailOwnDegreeUpper := branch.tailOwnDegreeUpper

theorem totalColoring_transportCanonicalBranchByFreePerm
    {kind : ProfileDTripleJoinReduction.Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position)
    (perm : Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hinside : ∀ a b, a ≠ b →
      branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (perm a) (perm b) =
        decodeRemainingColor block (!canonicalCycleWord.coloring a b))
    (left right : ProfileDHighOwnFiveSupportC5CNF.TotalVertex) :
    totalColoring
        (transportCanonicalBranchByFreePerm branch perm hinside).toDegreeFlooredFiveExtension.toFiveExtension
        left right =
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        (totalFreeVertexPerm perm left) (totalFreeVertexPerm perm right) := by
  rw [← mergeVertex_splitVertex left, ← mergeVertex_splitVertex right]
  generalize splitVertex left = leftPart
  generalize splitVertex right = rightPart
  cases leftPart <;> cases rightPart <;>
    simp [transportCanonicalBranchByFreePerm,
      transportDegreeFlooredFiveExtension, transportFiveExtension,
      totalFreeVertexPerm, totalDecompEquiv, totalColoring,
      pullbackColoring, mergeVertex]

noncomputable def transportExactDegreeTenMatrixBranchByFreePerm
    {kind : ProfileDTripleJoinReduction.Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    {coordinates : MatrixCoordinates block}
    {sourceMatrix targetMatrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch kind block position
      coordinates sourceMatrix)
    (perm : Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hinside : ∀ a b, a ≠ b →
      exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (perm a) (perm b) =
        decodeRemainingColor block (!canonicalCycleWord.coloring a b))
    (matrixPerm : Equiv.Perm (Fin 15))
    (hmatrixCoordinates : ∀ i,
      totalFreeVertexPerm perm (coordinates.vertex i) =
        coordinates.vertex (matrixPerm i))
    (hmatrixGroups : ∀ left right,
      left.val / 5 ≠ right.val / 5 →
        (matrixPerm left).val / 5 ≠ (matrixPerm right).val / 5)
    (hmatrix : ∀ left right,
      left.val / 5 ≠ right.val / 5 →
        sourceMatrix (matrixPerm left) (matrixPerm right) =
          targetMatrix left right) :
    ExactDegreeTenMatrixBranch kind block position
      coordinates targetMatrix where
  branch := transportCanonicalBranchByFreePerm exact.branch perm hinside
  tailOwnDegreeTen := exact.tailOwnDegreeTen
  firstSupportExact := exact.firstSupportExact
  secondSupportExact := exact.secondSupportExact
  matrixExact := by
    intro left right hgroups
    rw [totalColoring_transportCanonicalBranchByFreePerm,
      hmatrixCoordinates, hmatrixCoordinates]
    exact (exact.matrixExact (matrixPerm left) (matrixPerm right)
      (hmatrixGroups left right hgroups)).trans
        (hmatrix left right hgroups)

noncomputable def freeActionEquiv (a : Fin 10) :
    Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex :=
  Equiv.ofBijective (freeAction a) (freeAction_bijective a)

theorem freeAction_preserves_canonicalCycle
    (a : Fin 10)
    (left right : ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hne : left ≠ right) :
    canonicalCycleWord.coloring (freeAction a left) (freeAction a right) =
      canonicalCycleWord.coloring left right := by
  fin_cases a <;> fin_cases left <;> fin_cases right <;>
    simp_all <;> decide

theorem freeAction_insideCanonical
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (kind : SupportKind)
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) matrix)
    (a : Fin 10)
    (left right : ProfileDHighOwnFiveRowSplit61.FiveVertex)
    (hne : left ≠ right) :
    exact.branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
        (freeActionEquiv a left) (freeActionEquiv a right) =
      decodeRemainingColor 0 (!canonicalCycleWord.coloring left right) := by
  rw [exact.branch.insideCanonical _ _
    ((freeActionEquiv a).injective.ne hne)]
  congr 2
  change canonicalCycleWord.coloring (freeAction a left)
      (freeAction a right) = canonicalCycleWord.coloring left right
  exact freeAction_preserves_canonicalCycle a left right hne

noncomputable def freeMatrixPerm (a : Fin 10) : Equiv.Perm (Fin 15) :=
  matrixBlockPerm (freeActionEquiv a) (Equiv.refl _) (Equiv.refl _)

theorem freeMatrixPerm_coordinates_covariant
    (kind : SupportKind) (a : Fin 10) (i : Fin 15) :
    totalFreeVertexPerm (freeActionEquiv a)
        ((canonicalCoordinates kind).vertex i) =
      (canonicalCoordinates kind).vertex (freeMatrixPerm a i) := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixCoordinates_vertex_blockZero,
        totalFreeVertexPerm_free]
      change freeVertex (freeActionEquiv a position) =
        (canonicalCoordinates kind).vertex
          (matrixBlockPerm (freeActionEquiv a) (Equiv.refl _)
            (Equiv.refl _)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position))
      rw [matrixBlockPerm_blockZero, matrixCoordinates_vertex_blockZero]
    · rw [threeFiveEquiv_blockOne, matrixCoordinates_vertex_blockOne,
        totalFreeVertexPerm_tail]
      change tailVertex
          (ProfileDTripleJoinReduction.blockVertex 1
            ((canonicalCoordinates kind).first.embedding position).val) =
        (canonicalCoordinates kind).vertex
          (matrixBlockPerm (freeActionEquiv a) (Equiv.refl _)
            (Equiv.refl _)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position))
      rw [matrixBlockPerm_blockOne, matrixCoordinates_vertex_blockOne]
      rfl
  · rw [threeFiveEquiv_blockTwo, matrixCoordinates_vertex_blockTwo,
      totalFreeVertexPerm_tail]
    change tailVertex
        (ProfileDTripleJoinReduction.blockVertex 2
          ((canonicalCoordinates kind).second.embedding position).val) =
      (canonicalCoordinates kind).vertex
        (matrixBlockPerm (freeActionEquiv a) (Equiv.refl _)
          (Equiv.refl _)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position))
    rw [matrixBlockPerm_blockTwo, matrixCoordinates_vertex_blockTwo]
    rfl

noncomputable def freeRelabeledCatalogMatrix
    (kind : SupportKind) (i : Fin 600) (a : Fin 10) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring (catalogEdgeColoring kind i) (freeMatrixPerm a)

noncomputable def relabelCatalogExactByFreeAction
    (kind : SupportKind) (i : Fin 600)
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) (catalogEdgeColoring kind i))
    (a : Fin 10) :
    ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) (freeRelabeledCatalogMatrix kind i a) :=
  transportExactDegreeTenMatrixBranchByFreePerm exact (freeActionEquiv a)
    (freeAction_insideCanonical kind exact a)
    (freeMatrixPerm a)
    (freeMatrixPerm_coordinates_covariant kind a)
    (matrixBlockPerm_preserves_cross_group _ _ _)
    (by intro left right _; rfl)

/-! ## Tail stabilizers of the two normalized foreign supports -/

noncomputable def tailStabilizerPerm
    (kind : SupportKind) (a1 a2 : Fin 10) :
    Equiv.Perm ProfileDRowExtension.TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr (Equiv.refl (Fin 15))
        (u15StabilizerEquiv kind a1))
      (u16StabilizerEquiv a2)).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

@[simp] theorem tailStabilizerPerm_blockZero
    (kind : SupportKind) (a1 a2 : Fin 10) (position : Fin 15) :
    tailStabilizerPerm kind a1 a2
        (ProfileDTripleJoinReduction.blockVertex 0 position.val) =
      ProfileDTripleJoinReduction.blockVertex 0 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp [tailStabilizerPerm]

@[simp] theorem tailStabilizerPerm_blockOne
    (kind : SupportKind) (a1 a2 : Fin 10) (position : Fin 15) :
    tailStabilizerPerm kind a1 a2
        (ProfileDTripleJoinReduction.blockVertex 1 position.val) =
      ProfileDTripleJoinReduction.blockVertex 1
        (u15StabilizerEquiv kind a1 position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [tailStabilizerPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

@[simp] theorem tailStabilizerPerm_blockTwo
    (kind : SupportKind) (a1 a2 : Fin 10) (position : Fin 16) :
    tailStabilizerPerm kind a1 a2
        (ProfileDTripleJoinReduction.blockVertex 2 position.val) =
      ProfileDTripleJoinReduction.blockVertex 2
        (u16StabilizerEquiv a2 position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp only [tailStabilizerPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo _

theorem u15StabilizerEquiv_preserves
    (kind : SupportKind) (a : Fin 10)
    (left right : Fin 15) (hne : left ≠ right) :
    k15Template false (u15StabilizerEquiv kind a left)
        (u15StabilizerEquiv kind a right) =
      k15Template false left right := by
  exact u15StabilizerMap_preserves kind a left right hne

theorem u16StabilizerEquiv_preserves
    (a : Fin 10) (left right : Fin 16) (hne : left ≠ right) :
    k16Template false (u16StabilizerEquiv a left)
        (u16StabilizerEquiv a right) =
      k16Template false left right := by
  exact u16StabilizerMap_preserves a left right hne

theorem tailStabilizer_templateCanonical
    (tail : ProfileDTripleJoinReduction.Witness .uuu)
    (kind : SupportKind) (a1 a2 : Fin 10) :
    ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      tail.coloring
          (tailStabilizerPerm kind a1 a2
            (ProfileDTripleJoinReduction.blockVertex target left))
          (tailStabilizerPerm kind a1 a2
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
          (tailStabilizerPerm kind a1 a2
            (ProfileDTripleJoinReduction.blockVertex 0 left))
          (tailStabilizerPerm kind a1 a2
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
      tailStabilizerPerm_blockZero,
      show ProfileDTripleJoinReduction.blockVertex 0 right =
        ProfileDTripleJoinReduction.blockVertex 0 rightFin.val by rfl,
      tailStabilizerPerm_blockZero]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 0 (by decide) leftFin rightFin hne
    have htwisted : Kind.uuu.twisted (0 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    simpa [SingleRootStarCNF.templateColor,
      SingleRootStarCNF.fin15, leftFin, rightFin,
      Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hedge
  · change left < 15 at hleft
    change right < 15 at hright
    change
      tail.coloring
          (tailStabilizerPerm kind a1 a2
            (ProfileDTripleJoinReduction.blockVertex 1 left))
          (tailStabilizerPerm kind a1 a2
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
      tailStabilizerPerm_blockOne,
      show ProfileDTripleJoinReduction.blockVertex 1 right =
        ProfileDTripleJoinReduction.blockVertex 1 rightFin.val by rfl,
      tailStabilizerPerm_blockOne]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
        tail 1 (by decide) (u15StabilizerEquiv kind a1 leftFin)
          (u15StabilizerEquiv kind a1 rightFin)
          ((u15StabilizerEquiv kind a1).injective.ne hne)
    have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 1
            (u15StabilizerEquiv kind a1 leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 1
            (u15StabilizerEquiv kind a1 rightFin).val) =
        SingleRootStarCNF.canonicalPalette 2
          (k15Template false (u15StabilizerEquiv kind a1 leftFin)
            (u15StabilizerEquiv kind a1 rightFin)) := by simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 2
          (k15Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 2)
          (u15StabilizerEquiv_preserves kind a1 leftFin rightFin hne)
      _ = SingleRootStarCNF.canonicalPalette 2
          (SingleRootStarCNF.templateColor 15 false left right) := by
        simp [SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 16 at hleft
    change right < 16 at hright
    change
      tail.coloring
          (tailStabilizerPerm kind a1 a2
            (ProfileDTripleJoinReduction.blockVertex 2 left))
          (tailStabilizerPerm kind a1 a2
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
      tailStabilizerPerm_blockTwo,
      show ProfileDTripleJoinReduction.blockVertex 2 right =
        ProfileDTripleJoinReduction.blockVertex 2 rightFin.val by rfl,
      tailStabilizerPerm_blockTwo]
    have hedge :=
      ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK16
        tail 2 (by decide) (u16StabilizerEquiv a2 leftFin)
          (u16StabilizerEquiv a2 rightFin)
          ((u16StabilizerEquiv a2).injective.ne hne)
    have htwisted : Kind.uuu.twisted (2 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (ProfileDTripleJoinReduction.blockVertex 2
            (u16StabilizerEquiv a2 leftFin).val)
          (ProfileDTripleJoinReduction.blockVertex 2
            (u16StabilizerEquiv a2 rightFin).val) =
        SingleRootStarCNF.canonicalPalette 3
          (k16Template false (u16StabilizerEquiv a2 leftFin)
            (u16StabilizerEquiv a2 rightFin)) := by simpa using hedge
      _ = SingleRootStarCNF.canonicalPalette 3
          (k16Template false leftFin rightFin) :=
        congrArg (SingleRootStarCNF.canonicalPalette 3)
          (u16StabilizerEquiv_preserves a2 leftFin rightFin hne)
      _ = SingleRootStarCNF.canonicalPalette 3
          (SingleRootStarCNF.templateColor 16 false left right) := by
        simp [SingleRootStarCNF.templateColor,
          SingleRootStarCNF.fin16, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]

theorem u15Action_bijective (kind : SupportKind) (a : Fin 10) :
    Function.Bijective (u15Action kind a) := by
  cases kind <;> fin_cases a <;> decide

theorem u16Action_bijective (a : Fin 10) :
    Function.Bijective (u16Action a) := by
  fin_cases a <;> decide

noncomputable def u15ActionEquiv (kind : SupportKind) (a : Fin 10) :
    Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex :=
  Equiv.ofBijective (u15Action kind a) (u15Action_bijective kind a)

noncomputable def u16ActionEquiv (a : Fin 10) :
    Equiv.Perm ProfileDHighOwnFiveRowSplit61.FiveVertex :=
  Equiv.ofBijective (u16Action a) (u16Action_bijective a)

theorem canonicalCoordinates_first_embedding_eq_supportVertex
    (kind : SupportKind)
    (p : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    (canonicalCoordinates kind).first.embedding p =
      u15SupportVertex kind p := by
  cases kind <;> fin_cases p <;> decide

theorem canonicalCoordinates_second_embedding_eq_supportVertex
    (kind : SupportKind)
    (p : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    (canonicalCoordinates kind).second.embedding p =
      u16SupportZeroVertex p := by
  cases kind <;> fin_cases p <;> decide

theorem u15StabilizerEquiv_canonicalEmbedding
    (kind : SupportKind) (a : Fin 10)
    (p : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    u15StabilizerEquiv kind a
        ((canonicalCoordinates kind).first.embedding p) =
      (canonicalCoordinates kind).first.embedding (u15ActionEquiv kind a p) := by
  rw [canonicalCoordinates_first_embedding_eq_supportVertex,
    canonicalCoordinates_first_embedding_eq_supportVertex]
  exact u15StabilizerMap_induces kind a p

theorem u16StabilizerEquiv_canonicalEmbedding
    (kind : SupportKind) (a : Fin 10)
    (p : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    u16StabilizerEquiv a
        ((canonicalCoordinates kind).second.embedding p) =
      (canonicalCoordinates kind).second.embedding (u16ActionEquiv a p) := by
  rw [canonicalCoordinates_second_embedding_eq_supportVertex,
    canonicalCoordinates_second_embedding_eq_supportVertex]
  exact u16StabilizerMap_induces a p

theorem tailStabilizer_first_positions
    (kind : SupportKind) (a : Fin 10) (p : Fin 15) :
    p ∈ (canonicalCoordinates kind).first.positions ↔
      u15StabilizerEquiv kind a p ∈
        (canonicalCoordinates kind).first.positions := by
  cases kind <;> fin_cases a <;> fin_cases p <;> decide

theorem tailStabilizer_second_positions
    (kind : SupportKind) (a : Fin 10) (p : Fin 16) :
    p ∈ (canonicalCoordinates kind).second.positions ↔
      u16StabilizerEquiv a p ∈
        (canonicalCoordinates kind).second.positions := by
  cases kind <;> fin_cases a <;> fin_cases p <;> decide

noncomputable def tailMatrixPerm
    (kind : SupportKind) (a1 a2 : Fin 10) : Equiv.Perm (Fin 15) :=
  matrixBlockPerm (Equiv.refl _) (u15ActionEquiv kind a1)
    (u16ActionEquiv a2)

theorem tailMatrixPerm_coordinates_covariant
    (kind : SupportKind) (a1 a2 : Fin 10) (i : Fin 15) :
    totalVertexPerm (tailStabilizerPerm kind a1 a2)
        ((canonicalCoordinates kind).vertex i) =
      (canonicalCoordinates kind).vertex (tailMatrixPerm kind a1 a2 i) := by
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixCoordinates_vertex_blockZero,
        totalVertexPerm_free]
      change freeVertex position =
        (canonicalCoordinates kind).vertex
          (matrixBlockPerm (Equiv.refl _) (u15ActionEquiv kind a1)
            (u16ActionEquiv a2)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position))
      rw [matrixBlockPerm_blockZero, matrixCoordinates_vertex_blockZero]
      rfl
    · rw [threeFiveEquiv_blockOne, matrixCoordinates_vertex_blockOne,
        totalVertexPerm_tail, tailStabilizerPerm_blockOne]
      change tailVertex
          (ProfileDTripleJoinReduction.blockVertex 1
            (u15StabilizerEquiv kind a1
              ((canonicalCoordinates kind).first.embedding position)).val) =
        (canonicalCoordinates kind).vertex
          (matrixBlockPerm (Equiv.refl _) (u15ActionEquiv kind a1)
            (u16ActionEquiv a2)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position))
      rw [matrixBlockPerm_blockOne, matrixCoordinates_vertex_blockOne,
        u15StabilizerEquiv_canonicalEmbedding]
  · rw [threeFiveEquiv_blockTwo, matrixCoordinates_vertex_blockTwo,
      totalVertexPerm_tail, tailStabilizerPerm_blockTwo]
    change tailVertex
        (ProfileDTripleJoinReduction.blockVertex 2
          (u16StabilizerEquiv a2
            ((canonicalCoordinates kind).second.embedding position)).val) =
      (canonicalCoordinates kind).vertex
        (matrixBlockPerm (Equiv.refl _) (u15ActionEquiv kind a1)
          (u16ActionEquiv a2)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position))
    rw [matrixBlockPerm_blockTwo, matrixCoordinates_vertex_blockTwo,
      u16StabilizerEquiv_canonicalEmbedding]

noncomputable def combinedMatrixPerm
    (kind : SupportKind) (a0 a1 a2 : Fin 10) : Equiv.Perm (Fin 15) :=
  matrixBlockPerm (freeActionEquiv a0) (u15ActionEquiv kind a1)
    (u16ActionEquiv a2)

theorem freeMatrixPerm_tailMatrixPerm
    (kind : SupportKind) (a0 a1 a2 : Fin 10) (i : Fin 15) :
    freeMatrixPerm a0 (tailMatrixPerm kind a1 a2 i) =
      combinedMatrixPerm kind a0 a1 a2 i := by
  change
    matrixBlockPerm (freeActionEquiv a0) (Equiv.refl _) (Equiv.refl _)
        (matrixBlockPerm (Equiv.refl _) (u15ActionEquiv kind a1)
          (u16ActionEquiv a2) i) =
      matrixBlockPerm (freeActionEquiv a0) (u15ActionEquiv kind a1)
        (u16ActionEquiv a2) i
  rw [← threeFiveEquiv.apply_symm_apply i]
  generalize threeFiveEquiv.symm i = coordinate
  rcases coordinate with left | position
  · rcases left with position | position
    · rw [threeFiveEquiv_blockZero, matrixBlockPerm_blockZero,
        matrixBlockPerm_blockZero, matrixBlockPerm_blockZero]
      rfl
    · rw [threeFiveEquiv_blockOne, matrixBlockPerm_blockOne,
        matrixBlockPerm_blockOne, matrixBlockPerm_blockOne]
      rfl
  · rw [threeFiveEquiv_blockTwo, matrixBlockPerm_blockTwo,
      matrixBlockPerm_blockTwo, matrixBlockPerm_blockTwo]
    rfl

theorem combinedMatrixPerm_blockVertex
    (kind : SupportKind) (a0 a1 a2 : Fin 10)
    (block : Fin 3)
    (position : ProfileDHighOwnFiveRowSplit61.FiveVertex) :
    combinedMatrixPerm kind a0 a1 a2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex block position) =
      ProfileDUUUDegreeTenCatalogOrbits61.blockVertex block
        (blockAction kind a0 a1 a2 block position) := by
  fin_cases block
  · change
      matrixBlockPerm (freeActionEquiv a0) (u15ActionEquiv kind a1)
          (u16ActionEquiv a2)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0 position) =
        ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 0
          (freeAction a0 position)
    rw [matrixBlockPerm_blockZero]
    rfl
  · change
      matrixBlockPerm (freeActionEquiv a0) (u15ActionEquiv kind a1)
          (u16ActionEquiv a2)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1 position) =
        ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 1
          (u15Action kind a1 position)
    rw [matrixBlockPerm_blockOne]
    rfl
  · change
      matrixBlockPerm (freeActionEquiv a0) (u15ActionEquiv kind a1)
          (u16ActionEquiv a2)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2 position) =
        ProfileDUUUDegreeTenCatalogOrbits61.blockVertex 2
          (u16Action a2 position)
    rw [matrixBlockPerm_blockTwo]
    rfl

noncomputable def combinedRelabeledCatalogMatrix
    (kind : SupportKind) (i : Fin 600) (a0 a1 a2 : Fin 10) :
    EdgeColoring (Fin 15) (Fin 4) :=
  pullbackColoring (catalogEdgeColoring kind i)
    (combinedMatrixPerm kind a0 a1 a2)

theorem orbitEquation_all_block_orientations
    (kind : SupportKind) (i representative : Fin 600)
    (a0 a1 a2 : Fin 10)
    (horbit : ∀ leftBlock rightBlock : Fin 3, ∀ left right : Fin 5,
      leftBlock < rightBlock →
        catalogMatrixColor kind i
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock
              (blockAction kind a0 a1 a2 leftBlock left))
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock
              (blockAction kind a0 a1 a2 rightBlock right)) =
          catalogMatrixColor kind representative
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right))
    (leftBlock rightBlock : Fin 3) (hblocks : leftBlock ≠ rightBlock)
    (left right : Fin 5) :
    combinedRelabeledCatalogMatrix kind i a0 a1 a2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right) =
      catalogMatrixColor kind representative
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right) := by
  change catalogMatrixColor kind i
      (combinedMatrixPerm kind a0 a1 a2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left))
      (combinedMatrixPerm kind a0 a1 a2
        (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right)) = _
  rw [combinedMatrixPerm_blockVertex, combinedMatrixPerm_blockVertex]
  by_cases hlt : leftBlock < rightBlock
  · exact horbit leftBlock rightBlock left right hlt
  · have hgt : rightBlock < leftBlock := by
      exact lt_of_le_of_ne (not_lt.mp hlt) hblocks.symm
    calc
      catalogMatrixColor kind i
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock
            (blockAction kind a0 a1 a2 leftBlock left))
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock
            (blockAction kind a0 a1 a2 rightBlock right)) =
        catalogMatrixColor kind i
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock
            (blockAction kind a0 a1 a2 rightBlock right))
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock
            (blockAction kind a0 a1 a2 leftBlock left)) :=
        catalogMatrixColor_symm _ _ _ _
      _ = catalogMatrixColor kind representative
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left) :=
        horbit rightBlock leftBlock right left hgt
      _ = catalogMatrixColor kind representative
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
          (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right) :=
        catalogMatrixColor_symm _ _ _ _

theorem orbitEquation_on_cross_indices
    (kind : SupportKind) (i representative : Fin 600)
    (a0 a1 a2 : Fin 10)
    (horbit : ∀ leftBlock rightBlock : Fin 3, ∀ left right : Fin 5,
      leftBlock < rightBlock →
        catalogMatrixColor kind i
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock
              (blockAction kind a0 a1 a2 leftBlock left))
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock
              (blockAction kind a0 a1 a2 rightBlock right)) =
          catalogMatrixColor kind representative
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right))
    (left right : Fin 15) (hgroups : left.val / 5 ≠ right.val / 5) :
    combinedRelabeledCatalogMatrix kind i a0 a1 a2 left right =
      catalogMatrixColor kind representative left right := by
  exact catalogEquation_on_cross_indices kind
    (combinedRelabeledCatalogMatrix kind i a0 a1 a2) representative
    (orbitEquation_all_block_orientations kind i representative a0 a1 a2
      horbit) left right hgroups

noncomputable def normalizeCatalogExactToRepresentative
    (kind : SupportKind) (i representative : Fin 600)
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) (catalogEdgeColoring kind i))
    (a0 a1 a2 : Fin 10)
    (horbit : ∀ leftBlock rightBlock : Fin 3, ∀ left right : Fin 5,
      leftBlock < rightBlock →
        catalogMatrixColor kind i
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock
              (blockAction kind a0 a1 a2 leftBlock left))
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock
              (blockAction kind a0 a1 a2 rightBlock right)) =
          catalogMatrixColor kind representative
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex leftBlock left)
            (ProfileDUUUDegreeTenCatalogOrbits61.blockVertex rightBlock right)) :
    ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) (catalogEdgeColoring kind representative) :=
  let freeExact := relabelCatalogExactByFreeAction kind i exact a0
  transportExactDegreeTenMatrixBranch freeExact
    (tailStabilizerPerm kind a1 a2)
    (tailStabilizer_templateCanonical
      freeExact.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
      kind a1 a2)
    (by rw [tailStabilizerPerm_blockZero])
    (u15StabilizerEquiv kind a1)
    (u16StabilizerEquiv a2)
    (tailMatrixPerm kind a1 a2)
    (tailStabilizerPerm_blockOne kind a1 a2)
    (tailStabilizerPerm_blockTwo kind a1 a2)
    (tailStabilizer_first_positions kind a1)
    (tailStabilizer_second_positions kind a2)
    (tailMatrixPerm_coordinates_covariant kind a1 a2)
    (matrixBlockPerm_preserves_cross_group _ _ _)
    (by
      intro left right hgroups
      change catalogMatrixColor kind i
          (freeMatrixPerm a0 (tailMatrixPerm kind a1 a2 left))
          (freeMatrixPerm a0 (tailMatrixPerm kind a1 a2 right)) =
        catalogMatrixColor kind representative left right
      rw [freeMatrixPerm_tailMatrixPerm, freeMatrixPerm_tailMatrixPerm]
      exact orbitEquation_on_cross_indices kind i representative a0 a1 a2
        horbit left right hgroups)

theorem exists_representativeCatalogExactBranch
    (kind : SupportKind) (i : Fin 600)
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates kind) (catalogEdgeColoring kind i)) :
    ∃ representative ∈ representativeSet kind,
      Nonempty (ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
        (canonicalCoordinates kind)
        (catalogEdgeColoring kind representative)) := by
  obtain ⟨representative, hrep, a0, a1, a2, horbit⟩ :=
    exists_catalog_normalization kind i
  exact ⟨representative, hrep,
    ⟨normalizeCatalogExactToRepresentative kind i representative exact
      a0 a1 a2 horbit⟩⟩

/-! ## Identification with one of the ten authoritative semantic leaves -/

theorem canonicalCoordinates_leafSupportKind
    (leaf : ProfileDDegreeTenMatrixLeafTenDataUUU0P2.Leaf) :
    canonicalCoordinates (leafSupportKind leaf) = coordinates leaf := by
  cases leaf <;> rfl

noncomputable def catalogRepresentativeExactToLeaf
    (leaf : ProfileDDegreeTenMatrixLeafTenDataUUU0P2.Leaf)
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      (canonicalCoordinates (leafSupportKind leaf))
      (catalogEdgeColoring (leafSupportKind leaf)
        (leafCatalogIndex leaf))) :
    ProfileDDegreeTenMatrixLeafTenDataUUU0P2.RepresentativeExactBranch leaf := by
  change ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
    (coordinates leaf) (matrix leaf)
  rw [← canonicalCoordinates_leafSupportKind leaf]
  exact {
    branch := exact.branch
    tailOwnDegreeTen := exact.tailOwnDegreeTen
    firstSupportExact := exact.firstSupportExact
    secondSupportExact := exact.secondSupportExact
    matrixExact := by
      intro left right hgroups
      exact (exact.matrixExact left right hgroups).trans
        (catalogMatrixColor_eq_leafMatrix_of_cross_group
          leaf left right hgroups)
  }

/-- End-to-end semantic coverage, stopping immediately before LRAT imports:
every exact UUU/block-zero/position-two degree-ten branch transports to one
of the ten authoritative representative exact branches. -/
theorem exists_representativeExactBranch_of_exact
    {coordinates : MatrixCoordinates 0}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 0 SelectedPosition
      coordinates matrix) :
    ∃ leaf : ProfileDDegreeTenMatrixLeafTenDataUUU0P2.Leaf,
      Nonempty
        (ProfileDDegreeTenMatrixLeafTenDataUUU0P2.RepresentativeExactBranch leaf) := by
  obtain ⟨kind, i, ⟨catalogExact⟩⟩ :=
    exists_catalogExactBranch_of_exact exact
  obtain ⟨representative, hrep, ⟨representativeExact⟩⟩ :=
    exists_representativeCatalogExactBranch kind i catalogExact
  obtain ⟨leaf, hkind, hindex⟩ :=
    exists_leaf_of_representative kind representative hrep
  subst kind
  subst representative
  exact ⟨leaf, ⟨catalogRepresentativeExactToLeaf leaf representativeExact⟩⟩

#print axioms exists_firstSupportIndex
#print axioms exists_secondSupportIndex
#print axioms supportNormalizer_templateCanonical
#print axioms normalizeExactDegreeTenSupports
#print axioms exists_catalogExactBranch_of_exact
#print axioms exists_representativeCatalogExactBranch
#print axioms exists_representativeExactBranch_of_exact

end ProfileDUUUDegreeTenEndToEndSemanticUUU0P2
end R4333
