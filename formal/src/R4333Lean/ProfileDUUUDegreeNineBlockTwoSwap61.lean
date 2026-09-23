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
namespace ProfileDUUUDegreeNineBlockTwoSwap61

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
open ProfileDUUUDegreeNineCaseRealization61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev PositionedFiveSupport :=
  ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport

abbrev BlockZeroPosition := Fin (blockSize (0 : Fin 3))
abbrev BlockOnePosition := Fin (blockSize (1 : Fin 3))
abbrev BlockTwoPosition := Fin (blockSize (2 : Fin 3))

noncomputable def swapBlockZeroPositionEquiv :
    BlockZeroPosition ≃ BlockOnePosition :=
  localK15Zero .uuu

noncomputable def swapBlockOnePositionEquiv :
    BlockOnePosition ≃ BlockZeroPosition :=
  localK15One .uuu

noncomputable def blockTwoSwapTargetPosition
    (selected : BlockTwoPosition) : BlockTwoPosition :=
  (localK16Two .uuu).symm selected

theorem tailVertexPerm_uuu_blockTwoTarget (selected : BlockTwoPosition) :
    tailVertexPerm .uuu
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
    (tail : Witness .uuu) (selected : BlockTwoPosition) :
    colorDegree (transportWitness tail).coloring (blockRootColor 2)
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      colorDegree tail.coloring (blockRootColor 2)
        (blockVertex 2 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices tail.coloring (tailVertexPerm .uuu))
        hostColorPerm)
      (blockRootColor 2)
      (blockVertex 2 (blockTwoSwapTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockTwoRoot,
    tailVertexPerm_uuu_blockTwoTarget]

/-- Swap the two foreign K15 blocks while keeping the selected endpoint in
the K16 block. -/
noncomputable def swapSupportBlockTwo (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    PositionedFiveSupport .uuu 2 (blockTwoSwapTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    swapDegreeFlooredUUU branch.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro row
    change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (tailVertexPerm .uuu
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))) = _
    rw [tailVertexPerm_uuu_blockTwoTarget, branch.allFiveOwn]
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
    (branch : PositionedFiveSupport .uuu 2 selected) :
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
    (branch : PositionedFiveSupport .uuu 2 selected)
    (position : BlockZeroPosition) :
    position ∈ foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 0 ↔
      swapBlockZeroPositionEquiv position ∈
        foreignOwnSupport branch.toSemantic 1 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (tailVertexPerm .uuu
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))
        (tailVertexPerm .uuu (blockVertex 0 position.val))) =
      blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 2 selected.val)
        (blockVertex 1 (localK15Zero .uuu position).val) =
      blockRootColor 2
  rw [tailVertexPerm_uuu_blockTwoTarget,
    tailVertexPerm_blockZero]
  constructor
  · intro h
    have hback := congrArg hostColorPerm.symm h
    simpa using hback
  · intro h
    simpa using congrArg hostColorPerm h

theorem mem_foreignOwnSupport_swap_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected)
    (position : BlockOnePosition) :
    position ∈ foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 1 ↔
      swapBlockOnePositionEquiv position ∈
        foreignOwnSupport branch.toSemantic 0 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (tailVertexPerm .uuu
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))
        (tailVertexPerm .uuu (blockVertex 1 position.val))) =
      blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 2 selected.val)
        (blockVertex 0 (localK15One .uuu position).val) =
      blockRootColor 2
  rw [tailVertexPerm_uuu_blockTwoTarget,
    tailVertexPerm_blockOne]
  constructor
  · intro h
    have hback := congrArg hostColorPerm.symm h
    simpa using hback
  · intro h
    simpa using congrArg hostColorPerm h

theorem foreignOwnSupport_swap_blockZero_eq_image
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
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
    (branch : PositionedFiveSupport .uuu 2 selected) :
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
    (branch : PositionedFiveSupport .uuu 2 selected) :
    (foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 0).card =
      (foreignOwnSupport branch.toSemantic 1).card := by
  rw [foreignOwnSupport_swap_blockZero_eq_image,
    Finset.card_image_of_injective _ swapBlockZeroPositionEquiv.symm.injective]

theorem foreignOwnSupport_swap_blockOne_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    (foreignOwnSupport
        (swapSupportBlockTwo selected branch).toSemantic 1).card =
      (foreignOwnSupport branch.toSemantic 0).card := by
  rw [foreignOwnSupport_swap_blockOne_eq_image,
    Finset.card_image_of_injective _ swapBlockOnePositionEquiv.symm.injective]

/-! ## Renormalizing the selected K16 position leaves foreign supports fixed -/

theorem mem_foreignOwnSupport_normalizeBlockTwo_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected)
    (position : BlockZeroPosition) :
    position ∈ foreignOwnSupport
        (normalizeSupportBlockTwo selected branch).toSemantic 0 ↔
      position ∈ foreignOwnSupport branch.toSemantic 0 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val))
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 0 position.val)) = blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 selected.val) (blockVertex 0 position.val) =
        blockRootColor 2
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply,
    selectedPositionPermTwo_symm_blockZero]

theorem mem_foreignOwnSupport_normalizeBlockTwo_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected)
    (position : BlockOnePosition) :
    position ∈ foreignOwnSupport
        (normalizeSupportBlockTwo selected branch).toSemantic 1 ↔
      position ∈ foreignOwnSupport branch.toSemantic 1 := by
  rw [mem_foreignOwnSupport, mem_foreignOwnSupport]
  change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val))
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 1 position.val)) = blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 selected.val) (blockVertex 1 position.val) =
        blockRootColor 2
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply,
    selectedPositionPermTwo_symm_blockOne]

theorem foreignOwnSupport_normalizeBlockTwo_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    foreignOwnSupport (normalizeSupportBlockTwo selected branch).toSemantic 0 =
      foreignOwnSupport branch.toSemantic 0 := by
  ext position
  exact mem_foreignOwnSupport_normalizeBlockTwo_blockZero
    selected branch position

theorem foreignOwnSupport_normalizeBlockTwo_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    foreignOwnSupport (normalizeSupportBlockTwo selected branch).toSemantic 1 =
      foreignOwnSupport branch.toSemantic 1 := by
  ext position
  exact mem_foreignOwnSupport_normalizeBlockTwo_blockOne
    selected branch position

/-- Swap the equal K15 blocks and then restore the selected K16 endpoint to
the canonical last position. -/
noncomputable def swapNormalizeSupportBlockTwo
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    PositionedFiveSupport .uuu 2 (Fin.last 15) :=
  normalizeSupportBlockTwo (blockTwoSwapTargetPosition selected)
    (swapSupportBlockTwo selected branch)

theorem swapNormalizeSupportBlockTwo_tailOwnDegree
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    colorDegree
        (swapNormalizeSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  rw [swapNormalizeSupportBlockTwo,
    normalizeSupportBlockTwo_tailOwnDegree,
    swapSupportBlockTwo_tailOwnDegree]

theorem foreignOwnSupport_swapNormalize_blockZero_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    (foreignOwnSupport
        (swapNormalizeSupportBlockTwo selected branch).toSemantic 0).card =
      (foreignOwnSupport branch.toSemantic 1).card := by
  rw [swapNormalizeSupportBlockTwo,
    foreignOwnSupport_normalizeBlockTwo_blockZero,
    foreignOwnSupport_swap_blockZero_card]

theorem foreignOwnSupport_swapNormalize_blockOne_card
    (selected : BlockTwoPosition)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    (foreignOwnSupport
        (swapNormalizeSupportBlockTwo selected branch).toSemantic 1).card =
      (foreignOwnSupport branch.toSemantic 0).card := by
  rw [swapNormalizeSupportBlockTwo,
    foreignOwnSupport_normalizeBlockTwo_blockOne,
    foreignOwnSupport_swap_blockOne_card]

theorem degreeNineSkeleton_blockTwo_blockZero_card
    {selected : BlockTwoPosition}
    {branch : PositionedFiveSupport .uuu 2 selected}
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
    {branch : PositionedFiveSupport .uuu 2 selected}
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
    (branch : PositionedFiveSupport .uuu 2 selected)
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
  let branch : PositionedFiveSupport .uuu 2 (Fin.last 15) :=
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
    exists_templateRootCase_for_positioned_degreeNine
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

/-! ## A sound 28-case obstruction assembly -/

/-- Three unrestricted position slots contribute `3 * 2 * 4` cases.  For
the block-two slot, the proved swap allows us to retain only the `false`
orientation, contributing four more cases. -/
noncomputable def DegreeNineSwapReducedCase :=
  (Σ slot : Fin 3, Σ firstLarge : Bool,
    DegreeNineTemplateRootCase
      (residualDeficientColor slot.castSucc firstLarge)) ⊕
  DegreeNineTemplateRootCase (residualDeficientColor 3 false)

noncomputable instance degreeNineSwapReducedCaseFintype :
    Fintype DegreeNineSwapReducedCase := by
  unfold DegreeNineSwapReducedCase
  infer_instance

theorem degreeNineSwapReducedCase_card :
    Fintype.card DegreeNineSwapReducedCase = 28 := by
  classical
  change Fintype.card
    ((Σ slot : Fin 3, Σ firstLarge : Bool,
      DegreeNineTemplateRootCase
        (residualDeficientColor slot.castSucc firstLarge)) ⊕
      DegreeNineTemplateRootCase (residualDeficientColor 3 false)) = 28
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp [degreeNineTemplateRootCase_card]

noncomputable def swapReducedCaseToResidual :
    DegreeNineSwapReducedCase → ResidualCase
  | .inl indexed =>
      ⟨indexed.1.castSucc, indexed.2.1, indexed.2.2⟩
  | .inr rootCase => ⟨3, false, rootCase⟩

/-- Exactly 28 full-semantic obstruction obligations after the proved
block-two orientation quotient. -/
noncomputable def DegreeNineSwapReducedObstructionAssembly : Prop :=
  ∀ reducedCase : DegreeNineSwapReducedCase,
    DegreeNineCaseObstruction (swapReducedCaseToResidual reducedCase)

theorem swapReducedObstructionAssembly_toResidual
    (assembly : DegreeNineSwapReducedObstructionAssembly) :
    DegreeNineResidualObstructionAssembly := by
  refine ⟨?_⟩
  intro case realization
  rcases case with ⟨slot, firstLarge, rootCase⟩
  fin_cases slot
  · exact assembly (.inl ⟨0, firstLarge, rootCase⟩) realization
  · exact assembly (.inl ⟨1, firstLarge, rootCase⟩) realization
  · exact assembly (.inl ⟨2, firstLarge, rootCase⟩) realization
  · cases firstLarge
    · exact assembly (.inr rootCase) realization
    · obtain ⟨target, hslot, horientation, ⟨targetRealization⟩⟩ :=
        exists_opposite_blockTwo_caseRealization true rootCase realization
      rcases target with ⟨targetSlot, targetFirstLarge, targetRootCase⟩
      change targetSlot = 3 at hslot
      change targetFirstLarge = !true at horientation
      have hfalse : targetFirstLarge = false := by simpa using horientation
      subst targetSlot
      subst targetFirstLarge
      exact assembly (.inr targetRootCase) targetRealization

theorem no_exactDegreeNine_of_swapReducedObstructionAssembly
    (assembly : DegreeNineSwapReducedObstructionAssembly) :
    ¬ UUUFiveSupportExactDegreeNine :=
  (swapReducedObstructionAssembly_toResidual assembly).no_exactDegreeNine

#print axioms swapSupportBlockTwo_tailOwnDegree
#print axioms foreignOwnSupport_swap_blockZero_card
#print axioms foreignOwnSupport_swap_blockOne_card
#print axioms swapNormalizeSupportBlockTwo_tailOwnDegree
#print axioms foreignOwnSupport_swapNormalize_blockZero_card
#print axioms foreignOwnSupport_swapNormalize_blockOne_card
#print axioms swapNormalizeSupportBlockTwo_firstLarge
#print axioms exists_opposite_blockTwo_caseRealization
#print axioms degreeNineSwapReducedCase_card
#print axioms swapReducedObstructionAssembly_toResidual
#print axioms no_exactDegreeNine_of_swapReducedObstructionAssembly

end ProfileDUUUDegreeNineBlockTwoSwap61
end R4333
