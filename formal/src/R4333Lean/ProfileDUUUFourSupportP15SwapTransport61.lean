import R4333Lean.ProfileDUUUFourSupportP15MatrixOnlyLeaves61
import R4333Lean.ProfileDUUUFourSupportBlockTwoSwap61
import R4333Lean.ProfileDUUUFourSupportP15SemanticTransport61

/-!
# Semantic swap transport for the P15 ordered leaves

This module turns the global equal-K15 block swap into a normalized P15
support pair.  The two local K15 maps built into the global symmetry are
undone inside their target blocks, so the swapped branch again uses the
literal canonical support embeddings.

The final finite local witness is handled below this global boundary.  No
SAT result or certificate premise occurs here.
-/

namespace R4333
namespace ProfileDUUUFourSupportP15SwapTransport61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourSupportForeignSupports61
open ProfileDFourSupportRestoredRootK15
open ProfileDFourRowKindSymmetry
open ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61
open ProfileDUUUFourSupportP15SupportPair61
open ProfileDUUUFourSupportP15SemanticBase61
open ProfileDUUUFourSupportBlockTwoSwap61
open ProfileDUUUFourSupportP15SwapData61
open ProfileDUUUFourSupportP15SwapFiniteCoverage61
open ProfileDUUUFourSupportP15MatrixOnlyLeaves61
open ProfileDUUUFourSupportP15SemanticTransport61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev OrderedLeaf := ProfileDUUUFourSupportP15SwapData61.OrderedLeaf
abbrev Branch := ProfileDUUUFourSupportP15SupportPair61.Branch
abbrev TailVertex := ProfileDRowExtension.TailVertex

/-! ## Undo the local K15 maps built into the global block swap -/

noncomputable def swapRestoreTailPerm : Equiv.Perm TailVertex :=
  ProfileDFourRowKindSymmetry.tailDecompEquiv.symm.trans
    ((Equiv.sumCongr
      (Equiv.sumCongr swapBlockZeroPositionEquiv.symm
        swapBlockOnePositionEquiv.symm)
      (Equiv.refl (Fin 16))).trans
        ProfileDFourRowKindSymmetry.tailDecompEquiv)

@[simp] theorem swapRestoreTailPerm_blockZero (position : Fin 15) :
    swapRestoreTailPerm (blockVertex 0 position.val) =
      blockVertex 0 (swapBlockZeroPositionEquiv.symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero position]
  simp only [swapRestoreTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockZero _

@[simp] theorem swapRestoreTailPerm_blockOne (position : Fin 15) :
    swapRestoreTailPerm (blockVertex 1 position.val) =
      blockVertex 1 (swapBlockOnePositionEquiv.symm position).val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne position]
  simp only [swapRestoreTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact ProfileDFourRowKindSymmetry.tailDecompEquiv_blockOne _

@[simp] theorem swapRestoreTailPerm_blockTwo (position : Fin 16) :
    swapRestoreTailPerm (blockVertex 2 position.val) =
      blockVertex 2 position.val := by
  rw [← ProfileDFourRowKindSymmetry.tailDecompEquiv_blockTwo position]
  simp only [swapRestoreTailPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  rfl

theorem labelPerm_zero_apply (q : Fin 3) :
    ProfileDFourRowKindSymmetry.labelPerm 0 q = q := by
  apply SingleRootStarWitness61.canonicalPalette_injective 1
  have h := ProfileDFourRowKindSymmetry.hostColorPerm_canonicalPalette
    (0 : Fin 3) q
  change hostColorPerm (canonicalPalette 2 q) =
    canonicalPalette 1 (ProfileDFourRowKindSymmetry.labelPerm 0 q) at h
  rw [← h]
  fin_cases q <;> decide

theorem labelPerm_one_apply (q : Fin 3) :
    ProfileDFourRowKindSymmetry.labelPerm 1 q = q := by
  apply SingleRootStarWitness61.canonicalPalette_injective 2
  have h := ProfileDFourRowKindSymmetry.hostColorPerm_canonicalPalette
    (1 : Fin 3) q
  change hostColorPerm (canonicalPalette 1 q) =
    canonicalPalette 2 (ProfileDFourRowKindSymmetry.labelPerm 1 q) at h
  rw [← h]
  fin_cases q <;> decide

theorem labelPerm_zero_eq_refl :
    ProfileDFourRowKindSymmetry.labelPerm 0 = Equiv.refl (Fin 3) := by
  apply Equiv.ext
  intro q
  exact labelPerm_zero_apply q

theorem labelPerm_one_eq_refl :
    ProfileDFourRowKindSymmetry.labelPerm 1 = Equiv.refl (Fin 3) := by
  apply Equiv.ext
  intro q
  exact labelPerm_one_apply q

theorem swapBlockZeroPositionEquiv_symm_preserves
    (left right : Fin 15) (hne : left ≠ right) :
    k15Template false (swapBlockZeroPositionEquiv.symm left)
        (swapBlockZeroPositionEquiv.symm right) =
      k15Template false left right := by
  have h := ProfileDFourRowKindSymmetry.localK15Zero_preserves .uuu
    (swapBlockZeroPositionEquiv.symm left)
    (swapBlockZeroPositionEquiv.symm right)
    (swapBlockZeroPositionEquiv.symm.injective.ne hne)
  change k15Template false
      (swapBlockZeroPositionEquiv
        (swapBlockZeroPositionEquiv.symm left))
      (swapBlockZeroPositionEquiv
        (swapBlockZeroPositionEquiv.symm right)) = _ at h
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    labelPerm_zero_eq_refl] at h
  change k15Template false left right =
    k15Template false (swapBlockZeroPositionEquiv.symm left)
      (swapBlockZeroPositionEquiv.symm right) at h
  exact h.symm

theorem swapBlockOnePositionEquiv_symm_preserves
    (left right : Fin 15) (hne : left ≠ right) :
    k15Template false (swapBlockOnePositionEquiv.symm left)
        (swapBlockOnePositionEquiv.symm right) =
      k15Template false left right := by
  have h := ProfileDFourRowKindSymmetry.localK15One_preserves .uuu
    (swapBlockOnePositionEquiv.symm left)
    (swapBlockOnePositionEquiv.symm right)
    (swapBlockOnePositionEquiv.symm.injective.ne hne)
  change k15Template false
      (swapBlockOnePositionEquiv
        (swapBlockOnePositionEquiv.symm left))
      (swapBlockOnePositionEquiv
        (swapBlockOnePositionEquiv.symm right)) = _ at h
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    labelPerm_one_eq_refl] at h
  change k15Template false left right =
    k15Template false (swapBlockOnePositionEquiv.symm left)
      (swapBlockOnePositionEquiv.symm right) at h
  exact h.symm

theorem swapRestore_templateCanonical (tail : Witness .uuu) :
    ∀ (target : Fin 3) (left right : Nat),
      left < blockSize target → right < blockSize target → left < right →
      tail.coloring
          (swapRestoreTailPerm (blockVertex target left))
          (swapRestoreTailPerm (blockVertex target right)) =
        canonicalPalette (Fin.succ target)
          (templateColor (blockSize target)
            (Kind.twisted .uuu target) left right) := by
  intro target left right hleft hright hlr
  fin_cases target
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        (swapRestoreTailPerm (blockVertex 0 left))
        (swapRestoreTailPerm (blockVertex 0 right)) =
      canonicalPalette 1 (templateColor 15 false left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show blockVertex 0 left = blockVertex 0 leftFin.val by rfl,
      swapRestoreTailPerm_blockZero,
      show blockVertex 0 right = blockVertex 0 rightFin.val by rfl,
      swapRestoreTailPerm_blockZero]
    have hedge := witness_internal_eq_canonicalK15 tail 0 (by decide)
      (swapBlockZeroPositionEquiv.symm leftFin)
      (swapBlockZeroPositionEquiv.symm rightFin)
      (swapBlockZeroPositionEquiv.symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (0 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (blockVertex 0 (swapBlockZeroPositionEquiv.symm leftFin).val)
          (blockVertex 0 (swapBlockZeroPositionEquiv.symm rightFin).val) =
        canonicalPalette 1
          (k15Template false (swapBlockZeroPositionEquiv.symm leftFin)
            (swapBlockZeroPositionEquiv.symm rightFin)) := by simpa using hedge
      _ = canonicalPalette 1 (k15Template false leftFin rightFin) :=
        congrArg (canonicalPalette 1)
          (swapBlockZeroPositionEquiv_symm_preserves leftFin rightFin hne)
      _ = _ := by
        simp [templateColor, fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 15 at hleft
    change right < 15 at hright
    change tail.coloring
        (swapRestoreTailPerm (blockVertex 1 left))
        (swapRestoreTailPerm (blockVertex 1 right)) =
      canonicalPalette 2 (templateColor 15 false left right)
    let leftFin : Fin 15 := ⟨left, hleft⟩
    let rightFin : Fin 15 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show blockVertex 1 left = blockVertex 1 leftFin.val by rfl,
      swapRestoreTailPerm_blockOne,
      show blockVertex 1 right = blockVertex 1 rightFin.val by rfl,
      swapRestoreTailPerm_blockOne]
    have hedge := witness_internal_eq_canonicalK15 tail 1 (by decide)
      (swapBlockOnePositionEquiv.symm leftFin)
      (swapBlockOnePositionEquiv.symm rightFin)
      (swapBlockOnePositionEquiv.symm.injective.ne hne)
    have htwisted : Kind.uuu.twisted (1 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    calc
      tail.coloring
          (blockVertex 1 (swapBlockOnePositionEquiv.symm leftFin).val)
          (blockVertex 1 (swapBlockOnePositionEquiv.symm rightFin).val) =
        canonicalPalette 2
          (k15Template false (swapBlockOnePositionEquiv.symm leftFin)
            (swapBlockOnePositionEquiv.symm rightFin)) := by simpa using hedge
      _ = canonicalPalette 2 (k15Template false leftFin rightFin) :=
        congrArg (canonicalPalette 2)
          (swapBlockOnePositionEquiv_symm_preserves leftFin rightFin hne)
      _ = _ := by
        simp [templateColor, fin15, leftFin, rightFin,
          Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  · change left < 16 at hleft
    change right < 16 at hright
    change tail.coloring
        (swapRestoreTailPerm (blockVertex 2 left))
        (swapRestoreTailPerm (blockVertex 2 right)) =
      canonicalPalette 3 (templateColor 16 false left right)
    let leftFin : Fin 16 := ⟨left, hleft⟩
    let rightFin : Fin 16 := ⟨right, hright⟩
    have hne : leftFin ≠ rightFin := by
      intro h
      have := congrArg Fin.val h
      simp [leftFin, rightFin] at this
      omega
    rw [show blockVertex 2 left = blockVertex 2 leftFin.val by rfl,
      swapRestoreTailPerm_blockTwo,
      show blockVertex 2 right = blockVertex 2 rightFin.val by rfl,
      swapRestoreTailPerm_blockTwo]
    have hedge := witness_internal_eq_canonicalK16 tail 2 (by decide)
      leftFin rightFin hne
    have htwisted : Kind.uuu.twisted (2 : Fin 3) = false := by rfl
    rw [htwisted] at hedge
    simpa [templateColor, fin16, leftFin, rightFin,
      Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hedge

/-! ## A normalized branch after the global swap -/

noncomputable def swapRestoredBranch (branch : Branch) : Branch :=
  let swapped := swapNormalizeFourSupportBlockTwo SelectedPosition branch
  {
    toDegreeFlooredFiveExtension :=
      transportDegreeFlooredFiveByTailPerm
        swapped.toDegreeFlooredFiveExtension swapRestoreTailPerm
        (swapRestore_templateCanonical
          swapped.toDegreeFlooredFiveExtension.toFiveExtension.tail)
    firstFourOwn := by
      intro row
      change swapped.toDegreeFlooredFiveExtension.toFiveExtension.rows
        row.castSucc
        (swapRestoreTailPerm (blockVertex 2 SelectedPosition.val)) = 3
      rw [swapRestoreTailPerm_blockTwo]
      exact swapped.firstFourOwn row
    fifthNotOwn := by
      change swapped.toDegreeFlooredFiveExtension.toFiveExtension.rows
        (Fin.last 4)
        (swapRestoreTailPerm (blockVertex 2 SelectedPosition.val)) ≠ 3
      rw [swapRestoreTailPerm_blockTwo]
      exact swapped.fifthNotOwn
    tailOwnDegreeEqTen := by
      change colorDegree
        (relabelVertices
          swapped.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          swapRestoreTailPerm)
        3 (blockVertex 2 SelectedPosition.val) = 10
      rw [colorDegree_relabelVertices, swapRestoreTailPerm_blockTwo]
      exact swapped.tailOwnDegreeEqTen
  }

theorem swapRestoredBranch_blockZeroSupport_image (branch : Branch) :
    foreignOwnSupport (swapRestoredBranch branch).toSemantic 0 =
      (foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic 0).image
        swapBlockZeroPositionEquiv := by
  ext position
  rw [mem_foreignOwnSupport]
  change
    (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (swapRestoreTailPerm (blockVertex 2 SelectedPosition.val))
        (swapRestoreTailPerm (blockVertex 0 position.val)) = 3 ↔ _
  rw [swapRestoreTailPerm_blockTwo, swapRestoreTailPerm_blockZero]
  constructor
  · intro hcolor
    refine Finset.mem_image.mpr ⟨swapBlockZeroPositionEquiv.symm position,
      ?_, by simp⟩
    apply (mem_foreignOwnSupport
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic 0
      (swapBlockZeroPositionEquiv.symm position)).mpr
    change
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 2 SelectedPosition.val)
          (blockVertex 0 (swapBlockZeroPositionEquiv.symm position).val) = 3
    exact hcolor
  · intro hposition
    obtain ⟨source, hsource, hsourcePosition⟩ :=
      Finset.mem_image.mp hposition
    have hcolor := (mem_foreignOwnSupport
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic 0
      source).mp hsource
    change
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 2 SelectedPosition.val)
          (blockVertex 0 source.val) = 3 at hcolor
    have heq : swapBlockZeroPositionEquiv.symm position = source := by
      exact swapBlockZeroPositionEquiv.symm_apply_eq.mpr
        hsourcePosition.symm
    simpa [heq,
      ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
      using hcolor

theorem swapRestoredBranch_firstSupport (branch : Branch) :
    firstForeignOwnSupport (semantic (swapRestoredBranch branch)) =
      secondForeignOwnSupport (semantic branch) := by
  change foreignOwnSupport (semantic (swapRestoredBranch branch)) 0 =
    foreignOwnSupport (semantic branch) 1
  calc
    foreignOwnSupport (semantic (swapRestoredBranch branch)) 0 =
        (foreignOwnSupport
          (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic
            0).image swapBlockZeroPositionEquiv := by
              exact swapRestoredBranch_blockZeroSupport_image branch
    _ = ((foreignOwnSupport branch.toSemantic 1).image
          swapBlockZeroPositionEquiv.symm).image
            swapBlockZeroPositionEquiv := by
      rw [foreignOwnSupport_swapNormalize_blockZero_eq_image]
    _ = foreignOwnSupport (semantic branch) 1 := by
      ext position
      simp [ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]

theorem swapRestoredBranch_blockOneSupport_image (branch : Branch) :
    foreignOwnSupport (swapRestoredBranch branch).toSemantic 1 =
      (foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic 1).image
        swapBlockOnePositionEquiv := by
  ext position
  rw [mem_foreignOwnSupport]
  change
    (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (swapRestoreTailPerm (blockVertex 2 SelectedPosition.val))
        (swapRestoreTailPerm (blockVertex 1 position.val)) = 3 ↔ _
  rw [swapRestoreTailPerm_blockTwo, swapRestoreTailPerm_blockOne]
  constructor
  · intro hcolor
    refine Finset.mem_image.mpr ⟨swapBlockOnePositionEquiv.symm position,
      ?_, by simp⟩
    apply (mem_foreignOwnSupport
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic 1
      (swapBlockOnePositionEquiv.symm position)).mpr
    change
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 2 SelectedPosition.val)
          (blockVertex 1 (swapBlockOnePositionEquiv.symm position).val) = 3
    exact hcolor
  · intro hposition
    obtain ⟨source, hsource, hsourcePosition⟩ :=
      Finset.mem_image.mp hposition
    have hcolor := (mem_foreignOwnSupport
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic 1
      source).mp hsource
    change
      (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 2 SelectedPosition.val)
          (blockVertex 1 source.val) = 3 at hcolor
    have heq : swapBlockOnePositionEquiv.symm position = source := by
      exact swapBlockOnePositionEquiv.symm_apply_eq.mpr
        hsourcePosition.symm
    simpa [heq,
      ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
      using hcolor

theorem swapRestoredBranch_secondSupport (branch : Branch) :
    secondForeignOwnSupport (semantic (swapRestoredBranch branch)) =
      firstForeignOwnSupport (semantic branch) := by
  change foreignOwnSupport (semantic (swapRestoredBranch branch)) 1 =
    foreignOwnSupport (semantic branch) 0
  calc
    foreignOwnSupport (semantic (swapRestoredBranch branch)) 1 =
        (foreignOwnSupport
          (swapNormalizeFourSupportBlockTwo SelectedPosition branch).toSemantic
            1).image swapBlockOnePositionEquiv := by
              exact swapRestoredBranch_blockOneSupport_image branch
    _ = ((foreignOwnSupport branch.toSemantic 0).image
          swapBlockOnePositionEquiv.symm).image
            swapBlockOnePositionEquiv := by
      rw [foreignOwnSupport_swapNormalize_blockOne_eq_image]
    _ = foreignOwnSupport (semantic branch) 0 := by
      ext position
      simp [ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]

noncomputable def swapRestoredNormalized
    (normalized : NormalizedSupportPair) : NormalizedSupportPair where
  first := normalized.second
  second := normalized.first
  branch := swapRestoredBranch normalized.branch
  firstSupport := by
    rw [swapRestoredBranch_firstSupport, normalized.secondSupport]
  secondSupport := by
    rw [swapRestoredBranch_secondSupport, normalized.firstSupport]

@[simp] theorem swapRestoredNormalized_first
    (normalized : NormalizedSupportPair) :
    (swapRestoredNormalized normalized).first = normalized.second := rfl

@[simp] theorem swapRestoredNormalized_second
    (normalized : NormalizedSupportPair) :
    (swapRestoredNormalized normalized).second = normalized.first := rfl

/-! ## Matrix covariance of the support-restored global swap -/

noncomputable def globalSwapEnumerations
    (normalized : NormalizedSupportPair) :
    ForeignSupportEnumerations
      (swapNormalizeFourSupportBlockTwo SelectedPosition
        normalized.branch).toSemantic :=
  swapNormalizeForeignSupportEnumerations SelectedPosition normalized.branch
    (canonicalEnumerations normalized)

section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem ownNeighborhood_swapRestored
    (normalized : NormalizedSupportPair) (left right : Fin 14) :
    ownNeighborhoodHostColoring
        (canonicalEnumerations (swapRestoredNormalized normalized)) left right =
      ownNeighborhoodHostColoring (globalSwapEnumerations normalized)
        left right := by
  rw [← fourFiveFiveEquiv.apply_symm_apply left,
    ← fourFiveFiveEquiv.apply_symm_apply right]
  generalize fourFiveFiveEquiv.symm left = lc
  generalize fourFiveFiveEquiv.symm right = rc
  rcases lc with (lc | ls)
  · rcases lc with (lf | lfirst)
    · rcases rc with (rc | rs)
      · rcases rc with (rf | rfirst)
        · simp [ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring,
            ProfileDFourSupportInside61.firstFourInsideColoring,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
            canonicalEnumerations, globalSwapEnumerations,
            swapRestoredNormalized, swapRestoredBranch,
            swapNormalizeForeignSupportEnumerations,
            swappedFirstEmbedding, swappedSecondEmbedding,
            transportDegreeFlooredFiveByTailPerm,
            transportFiveExtensionByTailPerm,
            ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
            relabelVertices] <;> rfl
        · simp [ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
            canonicalEnumerations, globalSwapEnumerations,
            swapRestoredNormalized, swapRestoredBranch,
            swapNormalizeForeignSupportEnumerations,
            swappedFirstEmbedding, swappedSecondEmbedding,
            transportDegreeFlooredFiveByTailPerm,
            transportFiveExtensionByTailPerm,
            ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
            relabelVertices] <;> rfl
      · simp [ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
          canonicalEnumerations, globalSwapEnumerations,
          swapRestoredNormalized, swapRestoredBranch,
          swapNormalizeForeignSupportEnumerations,
          swappedFirstEmbedding, swappedSecondEmbedding,
          transportDegreeFlooredFiveByTailPerm,
          transportFiveExtensionByTailPerm,
          ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
          relabelVertices] <;> rfl
    · rcases rc with (rc | rs)
      · rcases rc with (rf | rfirst)
        · simp [ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
            canonicalEnumerations, globalSwapEnumerations,
            swapRestoredNormalized, swapRestoredBranch,
            swapNormalizeForeignSupportEnumerations,
            swappedFirstEmbedding, swappedSecondEmbedding,
            transportDegreeFlooredFiveByTailPerm,
            transportFiveExtensionByTailPerm,
            ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
            relabelVertices] <;> rfl
        · simp [ownNeighborhoodHostColoring, pullbackColoring,
            neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
            retainedJoinedColoring, joinColoring,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
            canonicalEnumerations, globalSwapEnumerations,
            swapRestoredNormalized, swapRestoredBranch,
            swapNormalizeForeignSupportEnumerations,
            swappedFirstEmbedding, swappedSecondEmbedding,
            transportDegreeFlooredFiveByTailPerm,
            transportFiveExtensionByTailPerm,
            ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
            relabelVertices] <;> rfl
      · simp [ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
          canonicalEnumerations, globalSwapEnumerations,
          swapRestoredNormalized, swapRestoredBranch,
          swapNormalizeForeignSupportEnumerations,
          swappedFirstEmbedding, swappedSecondEmbedding,
          transportDegreeFlooredFiveByTailPerm,
          transportFiveExtensionByTailPerm,
          ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
          relabelVertices] <;> rfl
  · rcases rc with (rc | rs)
    · rcases rc with (rf | rfirst)
      · simp [ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
          canonicalEnumerations, globalSwapEnumerations,
          swapRestoredNormalized, swapRestoredBranch,
          swapNormalizeForeignSupportEnumerations,
          swappedFirstEmbedding, swappedSecondEmbedding,
          transportDegreeFlooredFiveByTailPerm,
          transportFiveExtensionByTailPerm,
          ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
          relabelVertices] <;> rfl
      · simp [ownNeighborhoodHostColoring, pullbackColoring,
          neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
          retainedJoinedColoring, joinColoring,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
          canonicalEnumerations, globalSwapEnumerations,
          swapRestoredNormalized, swapRestoredBranch,
          swapNormalizeForeignSupportEnumerations,
          swappedFirstEmbedding, swappedSecondEmbedding,
          transportDegreeFlooredFiveByTailPerm,
          transportFiveExtensionByTailPerm,
          ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
          relabelVertices] <;> rfl
    · simp [ownNeighborhoodHostColoring, pullbackColoring,
        neighborhoodEmbedding, neighborhoodEmbeddingOnCoordinates,
        retainedJoinedColoring, joinColoring,
        ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic,
        ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
        ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
        swapRestoreTailPerm_blockZero, swapRestoreTailPerm_blockOne,
        canonicalEnumerations, globalSwapEnumerations,
        swapRestoredNormalized, swapRestoredBranch,
        swapNormalizeForeignSupportEnumerations,
        swappedFirstEmbedding, swappedSecondEmbedding,
        transportDegreeFlooredFiveByTailPerm,
        transportFiveExtensionByTailPerm,
        ProfileDSelectedPositionTransport.transportWitnessByTailPerm,
        relabelVertices] <;> rfl

end

theorem physicalMatrix_swapRestored
    (normalized : NormalizedSupportPair) (left right : Fin 14) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (swapRestoredNormalized normalized).branch)
        (physicalVertex (swapRestoredNormalized normalized) left)
        (physicalVertex (swapRestoredNormalized normalized) right) =
      hostColorPerm
        (ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
          (physicalVertex normalized (restoredK15CoordinateSwap left))
          (physicalVertex normalized (restoredK15CoordinateSwap right))) := by
  calc
    ProfileDFourRowCNF.totalColoring
        (fourExtension (swapRestoredNormalized normalized).branch)
        (physicalVertex (swapRestoredNormalized normalized) left)
        (physicalVertex (swapRestoredNormalized normalized) right) =
      ownNeighborhoodHostColoring
        (canonicalEnumerations (swapRestoredNormalized normalized))
        left right := physicalMatrix_eq_ownNeighborhood _ _ _
    _ = ownNeighborhoodHostColoring (globalSwapEnumerations normalized)
        left right := ownNeighborhood_swapRestored normalized left right
    _ = hostColorPerm
        (ownNeighborhoodHostColoring (canonicalEnumerations normalized)
          (restoredK15CoordinateSwap left)
          (restoredK15CoordinateSwap right)) := by
      exact ownNeighborhoodHostColoring_swap SelectedPosition
        normalized.branch (canonicalEnumerations normalized) left right
    _ = hostColorPerm
        (ProfileDFourRowCNF.totalColoring (fourExtension normalized.branch)
          (physicalVertex normalized (restoredK15CoordinateSwap left))
          (physicalVertex normalized (restoredK15CoordinateSwap right))) :=
      congrArg hostColorPerm
        (physicalMatrix_eq_ownNeighborhood normalized
          (restoredK15CoordinateSwap left)
          (restoredK15CoordinateSwap right)).symm

theorem exact_physicalVertex_eq_leafPhysicalVertex {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (p : Fin 14) :
    physicalVertex exact.normalized p = leafPhysicalVertex leaf p := by
  exact (leafPhysicalVertex_eq_physicalVertex exact.normalized leaf
    exact.first_eq exact.second_eq p).symm

theorem exact_swapRestored_rawMatrix {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (left right : Fin 14)
    (hne : left ≠ right) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (swapRestoredNormalized exact.normalized).branch)
        (physicalVertex (swapRestoredNormalized exact.normalized) left)
        (physicalVertex (swapRestoredNormalized exact.normalized) right) =
      rawSwapMatrixColor leaf left right := by
  rw [physicalMatrix_swapRestored, rawSwapMatrixColor_eq_semantic]
  congr 1
  rw [exact_physicalVertex_eq_leafPhysicalVertex,
    exact_physicalVertex_eq_leafPhysicalVertex]
  exact exact.matrixExact _ _
    (restoredK15CoordinateSwap.injective.ne hne)

/-! ## Undo the checked local witness -/

/-- Inverse slots in the lexicographic `S₄` table. -/
def inverseFreeAction : Fin 24 → Fin 24 :=
  ![0, 1, 2, 4, 3, 5, 6, 7, 12, 18, 13, 19,
    8, 10, 14, 20, 16, 22, 9, 11, 15, 21, 17, 23]

/-- Inverse slots in each checked five-point support stabilizer table. -/
def inverseSupportAction : SupportRepresentative → Fin 10 → Fin 10
  | .s0 => fun action => action
  | .s1 => fun action => action
  | .s4 => ![0, 1, 2, 6, 9, 5, 3, 7, 8, 4]

theorem freeFourAction_inverse_comp (action : Fin 24) (position : Fin 4) :
    freeFourAction action
        (freeFourAction (inverseFreeAction action) position) = position := by
  fin_cases action <;> fin_cases position <;> decide

theorem q2SupportAction_inverse_comp
    (representative : SupportRepresentative) (action : Fin 10)
    (position : Fin 5) :
    ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15.q2SupportAction
        representative action
        (ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15.q2SupportAction representative
          (inverseSupportAction representative action) position) = position := by
  cases representative <;> fin_cases action <;> fin_cases position <;> decide

theorem freeFourActionEquiv_inverse (action : Fin 24) :
    freeFourActionEquiv (inverseFreeAction action) =
      (freeFourActionEquiv action).symm := by
  apply Equiv.ext
  intro position
  apply (freeFourActionEquiv action).injective
  rw [Equiv.apply_symm_apply]
  exact freeFourAction_inverse_comp action position

theorem q2SupportActionEquiv_inverse
    (representative : SupportRepresentative) (action : Fin 10) :
    ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15.q2SupportActionEquiv
        representative
        (inverseSupportAction representative action) =
      (ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15.q2SupportActionEquiv
        representative action).symm := by
  apply Equiv.ext
  intro position
  apply (ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15.q2SupportActionEquiv
    representative action).injective
  rw [Equiv.apply_symm_apply]
  exact q2SupportAction_inverse_comp representative action position

theorem localCoordinateEquiv_inverse
    (first second : SupportRepresentative) (free : Fin 24)
    (firstAction secondAction : Fin 10) :
    localCoordinateEquiv first second (inverseFreeAction free)
        (inverseSupportAction first firstAction)
        (inverseSupportAction second secondAction) =
      (localCoordinateEquiv first second free firstAction secondAction).symm := by
  apply Equiv.ext
  intro position
  apply (localCoordinateEquiv first second free
    firstAction secondAction).injective
  rw [Equiv.apply_symm_apply, localCoordinateEquiv_apply,
    localCoordinateEquiv_apply]
  rw [← fourFiveFiveEquiv.apply_symm_apply position]
  generalize fourFiveFiveEquiv.symm position = coordinate
  rcases coordinate with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · simp [localCoordinateAction, localCoordinateActionOnCoordinates,
        freeFourAction_inverse_comp]
    · simp [localCoordinateAction, localCoordinateActionOnCoordinates,
        q2SupportAction_inverse_comp]
  · simp [localCoordinateAction, localCoordinateActionOnCoordinates,
      q2SupportAction_inverse_comp]

noncomputable def swapTargetNormalized {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) : NormalizedSupportPair :=
  let restored := swapRestoredNormalized exact.normalized
  transportNormalizedLocal restored
    (inverseFreeAction (witnessFree leaf))
    (inverseSupportAction restored.first (witnessFirst leaf))
    (inverseSupportAction restored.second (witnessSecond leaf))

theorem swapTargetNormalized_first {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (hswap : SwapLeafExact leaf) :
    (swapTargetNormalized exact).first = orderedFirst (swapLeaf leaf) := by
  change exact.normalized.second = orderedFirst (swapLeaf leaf)
  calc
    exact.normalized.second = orderedSecond leaf := exact.second_eq
    _ = orderedFirst (swapLeaf leaf) := hswap.1.symm

theorem swapTargetNormalized_second {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (hswap : SwapLeafExact leaf) :
    (swapTargetNormalized exact).second = orderedSecond (swapLeaf leaf) := by
  change exact.normalized.first = orderedSecond (swapLeaf leaf)
  calc
    exact.normalized.first = orderedFirst leaf := exact.first_eq
    _ = orderedSecond (swapLeaf leaf) := hswap.2.1.symm

theorem swapTargetNormalized_matrix {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (hswap : SwapLeafExact leaf)
    (left right : Fin 14) (hne : left ≠ right) :
    ProfileDFourRowCNF.totalColoring
        (fourExtension (swapTargetNormalized exact).branch)
        (physicalVertex (swapTargetNormalized exact) left)
        (physicalVertex (swapTargetNormalized exact) right) =
      orderedMatrixColor (swapLeaf leaf) left right := by
  let restored := swapRestoredNormalized exact.normalized
  let witnessEquiv := localCoordinateEquiv restored.first restored.second
    (witnessFree leaf) (witnessFirst leaf) (witnessSecond leaf)
  have hinverse :
      localCoordinateEquiv restored.first restored.second
          (inverseFreeAction (witnessFree leaf))
          (inverseSupportAction restored.first (witnessFirst leaf))
          (inverseSupportAction restored.second (witnessSecond leaf)) =
        witnessEquiv.symm := by
    exact localCoordinateEquiv_inverse _ _ _ _ _
  rw [show swapTargetNormalized exact =
      transportNormalizedLocal restored
        (inverseFreeAction (witnessFree leaf))
        (inverseSupportAction restored.first (witnessFirst leaf))
        (inverseSupportAction restored.second (witnessSecond leaf)) by
      rfl,
    transportNormalizedLocal_matrix, hinverse]
  have hpreimage : witnessEquiv.symm left ≠ witnessEquiv.symm right :=
    witnessEquiv.symm.injective.ne hne
  rw [exact_swapRestored_rawMatrix exact _ _ hpreimage,
    hswap.2.2 _ _ hpreimage]
  have hwitness (position : Fin 14) :
      swapWitnessCoordinate leaf (witnessEquiv.symm position) = position := by
    change localCoordinateAction
        (orderedFirst (swapLeaf leaf)) (orderedSecond (swapLeaf leaf))
          (witnessFree leaf) (witnessFirst leaf) (witnessSecond leaf)
          (witnessEquiv.symm position) = position
    rw [← localCoordinateEquiv_apply]
    have hfirst : restored.first = orderedFirst (swapLeaf leaf) := by
      exact swapTargetNormalized_first exact hswap
    have hsecond : restored.second = orderedSecond (swapLeaf leaf) := by
      exact swapTargetNormalized_second exact hswap
    rw [← hfirst, ← hsecond]
    exact witnessEquiv.apply_symm_apply position
  rw [hwitness, hwitness]

noncomputable def exactSwapOrderedLeaf {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (hswap : SwapLeafExact leaf) :
    ExactOrderedLeaf (swapLeaf leaf) where
  normalized := swapTargetNormalized exact
  first_eq := swapTargetNormalized_first exact hswap
  second_eq := swapTargetNormalized_second exact hswap
  matrixExact := by
    intro left right hne
    rw [leafPhysicalVertex_eq_physicalVertex
        (swapTargetNormalized exact) (swapLeaf leaf)
        (swapTargetNormalized_first exact hswap)
        (swapTargetNormalized_second exact hswap) left,
      leafPhysicalVertex_eq_physicalVertex
        (swapTargetNormalized exact) (swapLeaf leaf)
        (swapTargetNormalized_first exact hswap)
        (swapTargetNormalized_second exact hswap) right]
    exact swapTargetNormalized_matrix exact hswap left right hne

theorem exactOrderedLeaf_swap {leaf : OrderedLeaf}
    (exact : ExactOrderedLeaf leaf) (hswap : SwapLeafExact leaf) :
    Nonempty (ExactOrderedLeaf (swapLeaf leaf)) :=
  ⟨exactSwapOrderedLeaf exact hswap⟩

#print axioms swapRestore_templateCanonical
#print axioms swapRestoredBranch_firstSupport
#print axioms swapRestoredBranch_secondSupport
#print axioms swapRestoredNormalized
#print axioms physicalMatrix_swapRestored
#print axioms exact_physicalVertex_eq_leafPhysicalVertex
#print axioms exact_swapRestored_rawMatrix
#print axioms inverseFreeAction
#print axioms inverseSupportAction
#print axioms localCoordinateEquiv_inverse
#print axioms swapTargetNormalized_matrix
#print axioms exactSwapOrderedLeaf
#print axioms exactOrderedLeaf_swap

end ProfileDUUUFourSupportP15SwapTransport61
end R4333
