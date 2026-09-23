import PricingG.UUTFivePosition
import PricingG.UUTD9DegreeTransport
import PricingG.UUTD9Realization
import R4333Lean.ProfileDUUUDegreeNineCaseRealization61

/-!
# Equal-K15 swap on the block-two UUU degree-nine branch

The global profile-D symmetry interchanges the two equal K15 blocks and
fixes the K16 block setwise.  This module restricts that semantic transport
to a selected endpoint in block two.  The goal is to prove that the two
physical orientations of the foreign `5+4` split are equivalent, rather
than merely observing that the host symmetry suggests it.
-/

namespace R4333
namespace UUTD9Swap

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDFourRowKindSymmetry
open ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDDegreeNineFullNeighborhoodNormalForm61
open ProfileDUUUDegreeNineFiniteBoundary61
open UUTD9Realization

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev PositionedFiveSupport :=
  ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport

abbrev BlockZeroPosition := Fin (blockSize (0 : Fin 3))
abbrev BlockOnePosition := Fin (blockSize (1 : Fin 3))
abbrev BlockTwoPosition := Fin (blockSize (2 : Fin 3))

noncomputable def swapBlockZeroPositionEquiv :
    BlockZeroPosition ≃ BlockOnePosition :=
  localK15Zero .uut

noncomputable def swapBlockOnePositionEquiv :
    BlockOnePosition ≃ BlockZeroPosition :=
  localK15One .uut

noncomputable def blockTwoSwapTargetPosition
    (selected : BlockTwoPosition) : BlockTwoPosition :=
  (localK16Two .uut).symm selected

theorem tailVertexPerm_uut_blockTwoTarget (selected : BlockTwoPosition) :
    tailVertexPerm .uut
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      blockVertex 2 selected.val := by
  rw [tailVertexPerm_blockTwo]
  simp [blockTwoSwapTargetPosition]

@[simp] theorem hostColorPerm_blockTwoRoot :
    hostColorPerm (blockRootColor 2) = blockRootColor 2 := by
  decide

@[simp] theorem hostColorPerm_symm_blockTwoRoot :
    hostColorPerm.symm (blockRootColor 2) = blockRootColor 2 := by
  decide

private theorem swapped_tailDegree_blockTwo
    (tail : Witness .uut) (selected : BlockTwoPosition) :
    colorDegree (transportWitness tail).coloring (blockRootColor 2)
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      colorDegree tail.coloring (blockRootColor 2)
        (blockVertex 2 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices tail.coloring (tailVertexPerm .uut))
        hostColorPerm)
      (blockRootColor 2)
      (blockVertex 2 (blockTwoSwapTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockTwoRoot,
    tailVertexPerm_uut_blockTwoTarget]

/-- Swap the two foreign K15 blocks while keeping the selected endpoint in
the K16 block. -/
noncomputable def swapSupportBlockTwo (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    PositionedFiveSupport .uut 2 (blockTwoSwapTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    UUTFivePosition.swapDegreeFlooredUUT branch.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro row
    change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (tailVertexPerm .uut
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))) = _
    rw [tailVertexPerm_uut_blockTwoTarget, branch.allFiveOwn]
    exact hostColorPerm_blockTwoRoot
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (transportWitness
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 2)
      (blockVertex 2 (blockTwoSwapTargetPosition selected).val)
    rw [swapped_tailDegree_blockTwo]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (transportWitness
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 2)
      (blockVertex 2 (blockTwoSwapTargetPosition selected).val) ≤ 10
    rw [swapped_tailDegree_blockTwo]
    exact branch.tailOwnDegreeUpper

theorem swapSupportBlockTwo_tailOwnDegree
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    colorDegree
        (swapSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2)
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  exact swapped_tailDegree_blockTwo
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail selected

/-! ## The two foreign support sets are exchanged -/

theorem mem_foreignOwnSupport_swap_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected)
    (position : BlockZeroPosition) :
    position ∈ foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 0 ↔
      swapBlockZeroPositionEquiv position ∈
        foreignOwnSupport branch.toSemantic 1 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (tailVertexPerm .uut
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))
        (tailVertexPerm .uut (blockVertex 0 position.val))) =
      blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 2 selected.val)
        (blockVertex 1 (localK15Zero .uut position).val) =
      blockRootColor 2
  rw [tailVertexPerm_uut_blockTwoTarget,
    tailVertexPerm_blockZero]
  constructor
  · intro h
    have hback := congrArg hostColorPerm.symm h
    simpa using hback
  · intro h
    simpa using congrArg hostColorPerm h

theorem mem_foreignOwnSupport_swap_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected)
    (position : BlockOnePosition) :
    position ∈ foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 1 ↔
      swapBlockOnePositionEquiv position ∈
        foreignOwnSupport branch.toSemantic 0 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (tailVertexPerm .uut
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))
        (tailVertexPerm .uut (blockVertex 1 position.val))) =
      blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 2 selected.val)
        (blockVertex 0 (localK15One .uut position).val) =
      blockRootColor 2
  rw [tailVertexPerm_uut_blockTwoTarget,
    tailVertexPerm_blockOne]
  constructor
  · intro h
    have hback := congrArg hostColorPerm.symm h
    simpa using hback
  · intro h
    simpa using congrArg hostColorPerm h

theorem foreignOwnSupport_swap_blockZero_eq_image
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    foreignOwnSupport (swapSupportBlockTwo selected branch).toSemantic 0 =
      (foreignOwnSupport branch.toSemantic 1).image
        swapBlockZeroPositionEquiv.symm := by
  ext position
  rw [mem_foreignOwnSupport_swap_blockZero]
  simp only [Finset.mem_image]
  constructor
  · intro h
    exact ⟨swapBlockZeroPositionEquiv position, h, by simp⟩
  · rintro ⟨source, hsource, hsourcePosition⟩
    have heq : swapBlockZeroPositionEquiv position = source := by
      apply swapBlockZeroPositionEquiv.symm.injective
      simpa using hsourcePosition.symm
    simpa [heq] using hsource

theorem foreignOwnSupport_swap_blockOne_eq_image
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    foreignOwnSupport (swapSupportBlockTwo selected branch).toSemantic 1 =
      (foreignOwnSupport branch.toSemantic 0).image
        swapBlockOnePositionEquiv.symm := by
  ext position
  rw [mem_foreignOwnSupport_swap_blockOne]
  simp only [Finset.mem_image]
  constructor
  · intro h
    exact ⟨swapBlockOnePositionEquiv position, h, by simp⟩
  · rintro ⟨source, hsource, hsourcePosition⟩
    have heq : swapBlockOnePositionEquiv position = source := by
      apply swapBlockOnePositionEquiv.symm.injective
      simpa using hsourcePosition.symm
    simpa [heq] using hsource

theorem foreignOwnSupport_swap_blockZero_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    (foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 0).card =
      (foreignOwnSupport branch.toSemantic 1).card := by
  rw [foreignOwnSupport_swap_blockZero_eq_image,
    Finset.card_image_of_injective _ swapBlockZeroPositionEquiv.symm.injective]

theorem foreignOwnSupport_swap_blockOne_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    (foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 1).card =
      (foreignOwnSupport branch.toSemantic 0).card := by
  rw [foreignOwnSupport_swap_blockOne_eq_image,
    Finset.card_image_of_injective _ swapBlockOnePositionEquiv.symm.injective]

/-! ## Renormalizing the selected K16 position leaves foreign supports fixed -/

theorem mem_foreignOwnSupport_normalizeBlockTwo_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected)
    (position : BlockZeroPosition) :
    position ∈ foreignOwnSupport
        (UUTFivePosition.normalizeSupportBlockTwo selected branch).toSemantic 0 ↔
      position ∈ foreignOwnSupport branch.toSemantic 0 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 2 (Fin.last 15).val))
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 0 position.val)) = blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 selected.val) (blockVertex 0 position.val) =
        blockRootColor 2
  rw [← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
    Equiv.symm_apply_apply,
    selectedPositionPermTwo_symm_blockZero]

theorem mem_foreignOwnSupport_normalizeBlockTwo_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected)
    (position : BlockOnePosition) :
    position ∈ foreignOwnSupport
        (UUTFivePosition.normalizeSupportBlockTwo selected branch).toSemantic 1 ↔
      position ∈ foreignOwnSupport branch.toSemantic 1 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 2 (Fin.last 15).val))
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 1 position.val)) = blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 selected.val) (blockVertex 1 position.val) =
        blockRootColor 2
  rw [← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
    Equiv.symm_apply_apply,
    selectedPositionPermTwo_symm_blockOne]

theorem foreignOwnSupport_normalizeBlockTwo_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    foreignOwnSupport (UUTFivePosition.normalizeSupportBlockTwo selected branch).toSemantic 0 =
      foreignOwnSupport branch.toSemantic 0 := by
  ext position
  exact mem_foreignOwnSupport_normalizeBlockTwo_blockZero
    selected branch position

theorem foreignOwnSupport_normalizeBlockTwo_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    foreignOwnSupport (UUTFivePosition.normalizeSupportBlockTwo selected branch).toSemantic 1 =
      foreignOwnSupport branch.toSemantic 1 := by
  ext position
  exact mem_foreignOwnSupport_normalizeBlockTwo_blockOne
    selected branch position

/-- Swap the equal K15 blocks and then restore the selected K16 endpoint to
the canonical last position. -/
noncomputable def swapNormalizeSupportBlockTwo
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    PositionedFiveSupport .uut 2 (Fin.last 15) :=
  UUTFivePosition.normalizeSupportBlockTwo (blockTwoSwapTargetPosition selected)
    (swapSupportBlockTwo selected branch)

theorem swapNormalizeSupportBlockTwo_tailOwnDegree
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    colorDegree
        (swapNormalizeSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  rw [swapNormalizeSupportBlockTwo,
    UUTD9DegreeTransport.normalizeSupportBlockTwo_tailOwnDegree,
    swapSupportBlockTwo_tailOwnDegree]

theorem foreignOwnSupport_swapNormalize_blockZero_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    (foreignOwnSupport
        (swapNormalizeSupportBlockTwo selected branch).toSemantic 0).card =
      (foreignOwnSupport branch.toSemantic 1).card := by
  rw [swapNormalizeSupportBlockTwo,
    foreignOwnSupport_normalizeBlockTwo_blockZero,
    foreignOwnSupport_swap_blockZero_card]

theorem foreignOwnSupport_swapNormalize_blockOne_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected) :
    (foreignOwnSupport
        (swapNormalizeSupportBlockTwo selected branch).toSemantic 1).card =
      (foreignOwnSupport branch.toSemantic 0).card := by
  rw [swapNormalizeSupportBlockTwo,
    foreignOwnSupport_normalizeBlockTwo_blockOne,
    foreignOwnSupport_swap_blockOne_card]

theorem degreeNineSkeleton_blockTwo_blockZero_card
    {selected : BlockTwoPosition}
    {branch : PositionedFiveSupport .uut 2 selected}
    (skeleton : DegreeNineSkeleton branch.toSemantic) :
    (foreignOwnSupport branch.toSemantic 0).card =
      if skeleton.firstLarge then 5 else 4 := by
  cases skeleton with
  | mk degree firstLarge freeCycle largeSupport smallSupport =>
      cases firstLarge
      · simpa [smallForeignBlock, firstForeignBlock,
          PositionedFiveSupport.toSemantic] using smallSupport.supportCard
      · simpa [largeForeignBlock, firstForeignBlock,
          PositionedFiveSupport.toSemantic] using largeSupport.supportCard

theorem degreeNineSkeleton_blockTwo_blockOne_card
    {selected : BlockTwoPosition}
    {branch : PositionedFiveSupport .uut 2 selected}
    (skeleton : DegreeNineSkeleton branch.toSemantic) :
    (foreignOwnSupport branch.toSemantic 1).card =
      if skeleton.firstLarge then 4 else 5 := by
  cases skeleton with
  | mk degree firstLarge freeCycle largeSupport smallSupport =>
      cases firstLarge
      · simpa [largeForeignBlock, secondForeignBlock,
          PositionedFiveSupport.toSemantic] using largeSupport.supportCard
      · simpa [smallForeignBlock, secondForeignBlock,
          PositionedFiveSupport.toSemantic] using smallSupport.supportCard

/-- The semantic swap really reverses the physical `5+4` orientation. -/
theorem swapNormalizeSupportBlockTwo_firstLarge
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uut 2 selected)
    (sourceSkeleton : DegreeNineSkeleton branch.toSemantic)
    (targetSkeleton : DegreeNineSkeleton
      (swapNormalizeSupportBlockTwo selected branch).toSemantic) :
    targetSkeleton.firstLarge = !sourceSkeleton.firstLarge := by
  have hswapZero :=
    foreignOwnSupport_swapNormalize_blockZero_card selected branch
  have hswapOne :=
    foreignOwnSupport_swapNormalize_blockOne_card selected branch
  rw [degreeNineSkeleton_blockTwo_blockZero_card targetSkeleton,
    degreeNineSkeleton_blockTwo_blockOne_card sourceSkeleton] at hswapZero
  rw [degreeNineSkeleton_blockTwo_blockOne_card targetSkeleton,
    degreeNineSkeleton_blockTwo_blockZero_card sourceSkeleton] at hswapOne
  cases hsource : sourceSkeleton.firstLarge <;>
    cases htarget : targetSkeleton.firstLarge <;>
    simp_all

/-! ## Transport of full semantic case realizations -/

/-- Every realization in the block-two slot has a realization with the
opposite physical `5+4` orientation.  The target template bit and root orbit
are deliberately existential: the global swap is followed by a fresh
certified orbit normalization. -/
theorem exists_opposite_blockTwo_caseRealization
    (firstLarge : Bool)
    (rootCase : DegreeNineTemplateRootCase
      (residualDeficientColor 3 firstLarge))
    (realization : DegreeNineCaseRealization
      (⟨3, firstLarge, rootCase⟩ : ResidualCase)) :
    ∃ target : ResidualCase,
      caseSlot target = 3 ∧
        caseFirstLarge target = !firstLarge ∧
          Nonempty (DegreeNineCaseRealization target) := by
  let branch : PositionedFiveSupport .uut 2 (Fin.last 15) :=
    realization.branch
  let swapped := swapNormalizeSupportBlockTwo (Fin.last 15) branch
  have hswappedDegree :
      colorDegree
          swapped.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = 9 := by
    rw [show swapped = swapNormalizeSupportBlockTwo (Fin.last 15) branch by rfl,
      swapNormalizeSupportBlockTwo_tailOwnDegree]
    exact realization.tailOwnDegreeNine
  obtain ⟨targetSkeleton, targetNormal, targetRootCase,
      htwisted, hroot⟩ :=
    UUTD9Realization.exists_templateRootCase_for_positioned_degreeNine
      3 swapped hswappedDegree
  have horientation : targetSkeleton.firstLarge = !firstLarge := by
    calc
      targetSkeleton.firstLarge = !realization.skeleton.firstLarge :=
        swapNormalizeSupportBlockTwo_firstLarge
          (Fin.last 15) branch realization.skeleton targetSkeleton
      _ = !firstLarge :=
        congrArg Bool.not realization.caseFirstLarge_eq.symm
  let target : ResidualCase :=
    ⟨3, targetSkeleton.firstLarge, targetRootCase⟩
  refine ⟨target, rfl, horientation, ⟨{
    branch := swapped
    tailOwnDegreeNine := hswappedDegree
    skeleton := targetSkeleton
    caseFirstLarge_eq := rfl
    normal := targetNormal
    caseTwisted_eq := htwisted
    caseRoot_eq := hroot
  }⟩⟩


#print axioms exists_opposite_blockTwo_caseRealization
end UUTD9Swap
end R4333
