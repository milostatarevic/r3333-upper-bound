import R4333Lean.ProfileDUUUDegreeNineBlockTwoSwap61
import R4333Lean.ProfileDUUUFourSupportPositionSymmetry61

/-!
# Equal-K15 swap on the block-two UUU four-support branch

This is the semantic bridge behind the discovery quotient at selected index
`(2, Fin.last 15)`.  The checked global UUU transport exchanges the two K15
tail blocks and host colours one and two, while fixing the K16 block setwise.
Here it is restricted to an exact four-support branch, followed by the
already checked normalization of the selected K16 endpoint.
-/

namespace R4333
namespace ProfileDUUUFourSupportBlockTwoSwap61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDFourRowKindSymmetry
open ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUFourSupportPositionSymmetry61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev PositionedFourSupport :=
  ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport

abbrev TailVertex := ProfileDRowExtension.TailVertex

abbrev BlockZeroPosition := Fin (blockSize (0 : Fin 3))
abbrev BlockOnePosition := Fin (blockSize (1 : Fin 3))
abbrev BlockTwoPosition := Fin (blockSize (2 : Fin 3))

noncomputable abbrev swapBlockZeroPositionEquiv :
    BlockZeroPosition ≃ BlockOnePosition :=
  ProfileDUUUDegreeNineBlockTwoSwap61.swapBlockZeroPositionEquiv

noncomputable abbrev swapBlockOnePositionEquiv :
    BlockOnePosition ≃ BlockZeroPosition :=
  ProfileDUUUDegreeNineBlockTwoSwap61.swapBlockOnePositionEquiv

noncomputable abbrev blockTwoSwapTargetPosition
    (selected : BlockTwoPosition) : BlockTwoPosition :=
  ProfileDUUUDegreeNineBlockTwoSwap61.blockTwoSwapTargetPosition selected

theorem tailVertexPerm_uuu_blockTwoTarget (selected : BlockTwoPosition) :
    tailVertexPerm .uuu
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      blockVertex 2 selected.val :=
  ProfileDUUUDegreeNineBlockTwoSwap61.tailVertexPerm_uuu_blockTwoTarget
    selected

@[simp] theorem hostColorPerm_blockTwoRoot :
    hostColorPerm (blockRootColor 2) = blockRootColor 2 :=
  ProfileDUUUDegreeNineBlockTwoSwap61.hostColorPerm_blockTwoRoot

@[simp] theorem hostColorPerm_symm_blockTwoRoot :
    hostColorPerm.symm (blockRootColor 2) = blockRootColor 2 :=
  ProfileDUUUDegreeNineBlockTwoSwap61.hostColorPerm_symm_blockTwoRoot

private theorem swapped_tailDegree_blockTwo
    (tail : Witness .uuu) (selected : BlockTwoPosition) :
    colorDegree (transportWitness tail).coloring (blockRootColor 2)
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      colorDegree tail.coloring (blockRootColor 2)
        (blockVertex 2 selected.val) := by
  change colorDegree
      (mapEdgeColors (relabelVertices tail.coloring (tailVertexPerm .uuu))
        hostColorPerm)
      (blockRootColor 2)
      (blockVertex 2 (blockTwoSwapTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockTwoRoot,
    tailVertexPerm_uuu_blockTwoTarget]

/-- Swap the two equal K15 blocks while keeping the selected endpoint in the
K16 block.  The retained row order is unchanged. -/
noncomputable def swapFourSupportBlockTwo (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected) :
    PositionedFourSupport .uuu 2 (blockTwoSwapTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    swapDegreeFlooredUUU branch.toDegreeFlooredFiveExtension
  firstFourOwn := by
    intro row
    change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row.castSucc
        (tailVertexPerm .uuu
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))) = _
    rw [tailVertexPerm_uuu_blockTwoTarget, branch.firstFourOwn]
    exact hostColorPerm_blockTwoRoot
  fifthNotOwn := by
    change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows (Fin.last 4)
        (tailVertexPerm .uuu
          (blockVertex 2 (blockTwoSwapTargetPosition selected).val))) ≠ _
    rw [tailVertexPerm_uuu_blockTwoTarget]
    intro hcolor
    apply branch.fifthNotOwn
    apply hostColorPerm.injective
    exact hcolor.trans hostColorPerm_blockTwoRoot.symm
  tailOwnDegreeEqTen := by
    change colorDegree
      (transportWitness
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 2)
      (blockVertex 2 (blockTwoSwapTargetPosition selected).val) = 10
    rw [swapped_tailDegree_blockTwo]
    exact branch.tailOwnDegreeEqTen

@[simp] theorem swapFourSupportBlockTwo_rows
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (row : Fin 5) (x : TailVertex) :
    (swapFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
          (tailVertexPerm .uuu x)) := by
  rfl

theorem swapFourSupportBlockTwo_tailOwnDegree
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected) :
    colorDegree
        (swapFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2)
        (blockVertex 2 (blockTwoSwapTargetPosition selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  exact swapped_tailDegree_blockTwo
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail selected

/-- Swap, then put the selected K16 endpoint back at `Fin.last 15`. -/
noncomputable def swapNormalizeFourSupportBlockTwo
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected) :
    PositionedFourSupport .uuu 2 (Fin.last 15) :=
  normalizeFourSupportBlockTwo (blockTwoSwapTargetPosition selected)
    (swapFourSupportBlockTwo selected branch)

theorem swapNormalizeFourSupportBlockTwo_tailOwnDegree
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected) :
    colorDegree
        (swapNormalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  rw [swapNormalizeFourSupportBlockTwo,
    normalizeFourSupportBlockTwo_tailOwnDegree,
    swapFourSupportBlockTwo_tailOwnDegree]

/-! ## Exact foreign supports are exchanged -/

theorem mem_foreignOwnSupport_swap_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (position : BlockZeroPosition) :
    position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapFourSupportBlockTwo selected branch).toSemantic 0 ↔
      swapBlockZeroPositionEquiv position ∈
        ProfileDFourSupportForeignSupports61.foreignOwnSupport
          branch.toSemantic 1 := by
  rw [ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport,
    ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport]
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
  rw [tailVertexPerm_uuu_blockTwoTarget, tailVertexPerm_blockZero]
  constructor
  · intro h
    have hback := congrArg hostColorPerm.symm h
    simpa using hback
  · intro h
    simpa using congrArg hostColorPerm h

theorem mem_foreignOwnSupport_swap_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (position : BlockOnePosition) :
    position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapFourSupportBlockTwo selected branch).toSemantic 1 ↔
      swapBlockOnePositionEquiv position ∈
        ProfileDFourSupportForeignSupports61.foreignOwnSupport
          branch.toSemantic 0 := by
  rw [ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport,
    ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport]
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
  rw [tailVertexPerm_uuu_blockTwoTarget, tailVertexPerm_blockOne]
  constructor
  · intro h
    have hback := congrArg hostColorPerm.symm h
    simpa using hback
  · intro h
    simpa using congrArg hostColorPerm h

theorem mem_foreignOwnSupport_normalize_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (position : BlockZeroPosition) :
    position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (normalizeFourSupportBlockTwo selected branch).toSemantic 0 ↔
      position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        branch.toSemantic 0 := by
  rw [ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport,
    ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport]
  change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val))
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 0 position.val)) = blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 selected.val) (blockVertex 0 position.val) =
        blockRootColor 2
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply, selectedPositionPermTwo_symm_blockZero]

theorem mem_foreignOwnSupport_normalize_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (position : BlockOnePosition) :
    position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (normalizeFourSupportBlockTwo selected branch).toSemantic 1 ↔
      position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        branch.toSemantic 1 := by
  rw [ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport,
    ProfileDFourSupportForeignSupports61.mem_foreignOwnSupport]
  change branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val))
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 1 position.val)) = blockRootColor 2 ↔
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 selected.val) (blockVertex 1 position.val) =
        blockRootColor 2
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply, selectedPositionPermTwo_symm_blockOne]

theorem mem_foreignOwnSupport_swapNormalize_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (position : BlockZeroPosition) :
    position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic 0 ↔
      swapBlockZeroPositionEquiv position ∈
        ProfileDFourSupportForeignSupports61.foreignOwnSupport
          branch.toSemantic 1 := by
  rw [swapNormalizeFourSupportBlockTwo,
    mem_foreignOwnSupport_normalize_blockZero,
    mem_foreignOwnSupport_swap_blockZero]

theorem mem_foreignOwnSupport_swapNormalize_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (position : BlockOnePosition) :
    position ∈ ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic 1 ↔
      swapBlockOnePositionEquiv position ∈
        ProfileDFourSupportForeignSupports61.foreignOwnSupport
          branch.toSemantic 0 := by
  rw [swapNormalizeFourSupportBlockTwo,
    mem_foreignOwnSupport_normalize_blockOne,
    mem_foreignOwnSupport_swap_blockOne]

theorem foreignOwnSupport_swapNormalize_blockZero_eq_image
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected) :
    ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic 0 =
      (ProfileDFourSupportForeignSupports61.foreignOwnSupport
        branch.toSemantic 1).image swapBlockZeroPositionEquiv.symm := by
  ext position
  rw [mem_foreignOwnSupport_swapNormalize_blockZero]
  simp only [Finset.mem_image]
  constructor
  · intro h
    exact ⟨swapBlockZeroPositionEquiv position, h, by simp⟩
  · rintro ⟨source, hsource, hsourcePosition⟩
    have heq : swapBlockZeroPositionEquiv position = source := by
      apply swapBlockZeroPositionEquiv.symm.injective
      simpa using hsourcePosition.symm
    simpa [heq] using hsource

theorem foreignOwnSupport_swapNormalize_blockOne_eq_image
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected) :
    ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic 1 =
      (ProfileDFourSupportForeignSupports61.foreignOwnSupport
        branch.toSemantic 0).image swapBlockOnePositionEquiv.symm := by
  ext position
  rw [mem_foreignOwnSupport_swapNormalize_blockOne]
  simp only [Finset.mem_image]
  constructor
  · intro h
    exact ⟨swapBlockOnePositionEquiv position, h, by simp⟩
  · rintro ⟨source, hsource, hsourcePosition⟩
    have heq : swapBlockOnePositionEquiv position = source := by
      apply swapBlockOnePositionEquiv.symm.injective
      simpa using hsourcePosition.symm
    simpa [heq] using hsource

/-! ## Transporting the two exact five-support enumerations -/

private theorem source_firstEmbeddingRange_blockZero
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic) :
    Finset.univ.image enumerations.firstEmbedding =
      ProfileDFourSupportForeignSupports61.foreignOwnSupport
        branch.toSemantic 0 := by
  simpa [ProfileDFourSupportForeignSupports61.firstForeignOwnSupport,
    ProfileDFourSupportForeignSupports61.firstForeignBlock,
    ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
    ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
    using enumerations.firstEmbeddingRange

private theorem source_secondEmbeddingRange_blockOne
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic) :
    Finset.univ.image enumerations.secondEmbedding =
      ProfileDFourSupportForeignSupports61.foreignOwnSupport
        branch.toSemantic 1 := by
  simpa [ProfileDFourSupportForeignSupports61.secondForeignOwnSupport,
    ProfileDFourSupportForeignSupports61.secondForeignBlock,
    ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
    ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
    using enumerations.secondEmbeddingRange

noncomputable def swappedFirstEmbedding
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic) :
    ProfileDFourSupportRestoredRootK15.FiveVertex ↪ BlockZeroPosition :=
  enumerations.secondEmbedding.trans
    swapBlockZeroPositionEquiv.symm.toEmbedding

noncomputable def swappedSecondEmbedding
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic) :
    ProfileDFourSupportRestoredRootK15.FiveVertex ↪ BlockOnePosition :=
  enumerations.firstEmbedding.trans
    swapBlockOnePositionEquiv.symm.toEmbedding

noncomputable def swapNormalizeForeignSupportEnumerations
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic) :
    ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
      (swapNormalizeFourSupportBlockTwo selected branch).toSemantic where
  firstEmbedding := swappedFirstEmbedding selected branch enumerations
  firstEmbeddingRange := by
    change Finset.univ.image
        (swappedFirstEmbedding selected branch enumerations) =
      ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic 0
    rw [foreignOwnSupport_swapNormalize_blockZero_eq_image,
      ← source_secondEmbeddingRange_blockOne selected branch enumerations]
    apply Finset.ext
    intro position
    constructor
    · intro hposition
      obtain ⟨a, _ha, ha⟩ := Finset.mem_image.mp hposition
      refine Finset.mem_image.mpr ⟨enumerations.secondEmbedding a,
        Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩, ?_⟩
      change swapBlockZeroPositionEquiv.symm
        (enumerations.secondEmbedding a) = position at ha
      exact ha
    · intro hposition
      obtain ⟨source, hsource, hsourcePosition⟩ :=
        Finset.mem_image.mp hposition
      obtain ⟨a, _ha, ha⟩ := Finset.mem_image.mp hsource
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      change swapBlockZeroPositionEquiv.symm
        (enumerations.secondEmbedding a) = position
      rw [ha]
      exact hsourcePosition
  secondEmbedding := swappedSecondEmbedding selected branch enumerations
  secondEmbeddingRange := by
    change Finset.univ.image
        (swappedSecondEmbedding selected branch enumerations) =
      ProfileDFourSupportForeignSupports61.foreignOwnSupport
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic 1
    rw [foreignOwnSupport_swapNormalize_blockOne_eq_image,
      ← source_firstEmbeddingRange_blockZero selected branch enumerations]
    apply Finset.ext
    intro position
    constructor
    · intro hposition
      obtain ⟨a, _ha, ha⟩ := Finset.mem_image.mp hposition
      refine Finset.mem_image.mpr ⟨enumerations.firstEmbedding a,
        Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩, ?_⟩
      change swapBlockOnePositionEquiv.symm
        (enumerations.firstEmbedding a) = position at ha
      exact ha
    · intro hposition
      obtain ⟨source, hsource, hsourcePosition⟩ :=
        Finset.mem_image.mp hposition
      obtain ⟨a, _ha, ha⟩ := Finset.mem_image.mp hsource
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      change swapBlockOnePositionEquiv.symm
        (enumerations.firstEmbedding a) = position
      rw [ha]
      exact hsourcePosition

@[simp] theorem swapNormalizeForeignSupportEnumerations_firstEmbedding
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    (swapNormalizeForeignSupportEnumerations selected branch enumerations).firstEmbedding a =
      swapBlockZeroPositionEquiv.symm (enumerations.secondEmbedding a) := by
  rfl

@[simp] theorem swapNormalizeForeignSupportEnumerations_secondEmbedding
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    (swapNormalizeForeignSupportEnumerations selected branch enumerations).secondEmbedding a =
      swapBlockOnePositionEquiv.symm (enumerations.firstEmbedding a) := by
  rfl

/-! ## The explicit `4|5|5` restored-neighbourhood action -/

abbrev FourFiveFiveCoordinates :=
  ProfileDFourSupportRestoredRootK15.FourFiveFiveCoordinates

/-- Keep the four free coordinates fixed and exchange the two five-coordinate
foreign-support groups. -/
def swapForeignCoordinate : FourFiveFiveCoordinates → FourFiveFiveCoordinates
  | .inl (.inl a) => .inl (.inl a)
  | .inl (.inr a) => .inr a
  | .inr a => .inl (.inr a)

def swapForeignCoordinates : FourFiveFiveCoordinates ≃ FourFiveFiveCoordinates where
  toFun := swapForeignCoordinate
  invFun := swapForeignCoordinate
  left_inv := by
    intro coordinate
    rcases coordinate with (left | second)
    · rcases left with (free | first) <;> rfl
    · rfl
  right_inv := by
    intro coordinate
    rcases coordinate with (left | second)
    · rcases left with (free | first) <;> rfl
    · rfl

/-- The induced permutation of the concrete `Fin 14` matrix indices. -/
def restoredK15CoordinateSwap : Fin 14 ≃ Fin 14 :=
  ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm |>.trans
    (swapForeignCoordinates.trans
      ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv)

@[simp] theorem restoredK15CoordinateSwap_apply
    (coordinate : FourFiveFiveCoordinates) :
    restoredK15CoordinateSwap
        (ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv coordinate) =
      ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv
        (swapForeignCoordinate coordinate) := by
  change ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv
      (swapForeignCoordinates
        (ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm
          (ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv coordinate))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem restoredK15CoordinateSwap_free
    (a : ProfileDFourSupportRestoredRootK15.FourVertex) :
    restoredK15CoordinateSwap
        (ProfileDFourSupportRestoredRootK15.freeLabel a) =
      ProfileDFourSupportRestoredRootK15.freeLabel a := by
  exact restoredK15CoordinateSwap_apply (.inl (.inl a))

@[simp] theorem restoredK15CoordinateSwap_first
    (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    restoredK15CoordinateSwap
        (ProfileDFourSupportRestoredRootK15.firstForeignLabel a) =
      ProfileDFourSupportRestoredRootK15.secondForeignLabel a := by
  exact restoredK15CoordinateSwap_apply (.inl (.inr a))

@[simp] theorem restoredK15CoordinateSwap_second
    (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    restoredK15CoordinateSwap
        (ProfileDFourSupportRestoredRootK15.secondForeignLabel a) =
      ProfileDFourSupportRestoredRootK15.firstForeignLabel a := by
  exact restoredK15CoordinateSwap_apply (.inr a)

theorem restoredK15CoordinateSwap_involutive (i : Fin 14) :
    restoredK15CoordinateSwap (restoredK15CoordinateSwap i) = i := by
  rw [← ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.apply_symm_apply i]
  generalize ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm i = c
  rcases c with (left | second)
  · rcases left with (free | first) <;>
      simp [swapForeignCoordinate]
  · simp [swapForeignCoordinate]

private theorem target_first_physical_transport
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    tailVertexPerm .uuu
        ((selectedPositionPermTwo .uuu
          (blockTwoSwapTargetPosition selected)).symm
          (blockVertex 0
            ((swapNormalizeForeignSupportEnumerations selected branch
              enumerations).firstEmbedding a).val)) =
      blockVertex 1 (enumerations.secondEmbedding a).val := by
  rw [selectedPositionPermTwo_symm_blockZero, tailVertexPerm_blockZero]
  rw [swapNormalizeForeignSupportEnumerations_firstEmbedding]
  change blockVertex 1
      (swapBlockZeroPositionEquiv
        (swapBlockZeroPositionEquiv.symm (enumerations.secondEmbedding a))).val = _
  rw [Equiv.apply_symm_apply]

private theorem target_second_physical_transport
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    tailVertexPerm .uuu
        ((selectedPositionPermTwo .uuu
          (blockTwoSwapTargetPosition selected)).symm
          (blockVertex 1
            ((swapNormalizeForeignSupportEnumerations selected branch
              enumerations).secondEmbedding a).val)) =
      blockVertex 0 (enumerations.firstEmbedding a).val := by
  rw [selectedPositionPermTwo_symm_blockOne, tailVertexPerm_blockOne]
  rw [swapNormalizeForeignSupportEnumerations_secondEmbedding]
  change blockVertex 0
      (swapBlockOnePositionEquiv
        (swapBlockOnePositionEquiv.symm (enumerations.firstEmbedding a))).val = _
  rw [Equiv.apply_symm_apply]

private theorem target_inside_transport
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (a b : Fin 5) :
    (swapNormalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.inside
        a b =
      hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.inside a b) := by
  rfl

private theorem target_row_first_transport
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (row : Fin 5) (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    (swapNormalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row
        (blockVertex 0
          ((swapNormalizeForeignSupportEnumerations selected branch
            enumerations).firstEmbedding a).val) =
      hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
          (blockVertex 1 (enumerations.secondEmbedding a).val)) := by
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (tailVertexPerm .uuu
          ((selectedPositionPermTwo .uuu
            (blockTwoSwapTargetPosition selected)).symm
            (blockVertex 0
              ((swapNormalizeForeignSupportEnumerations selected branch
                enumerations).firstEmbedding a).val)))) = _
  rw [target_first_physical_transport]

private theorem target_row_second_transport
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (row : Fin 5) (a : ProfileDFourSupportRestoredRootK15.FiveVertex) :
    (swapNormalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row
        (blockVertex 1
          ((swapNormalizeForeignSupportEnumerations selected branch
            enumerations).secondEmbedding a).val) =
      hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
          (blockVertex 0 (enumerations.firstEmbedding a).val)) := by
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (tailVertexPerm .uuu
          ((selectedPositionPermTwo .uuu
            (blockTwoSwapTargetPosition selected)).symm
            (blockVertex 1
              ((swapNormalizeForeignSupportEnumerations selected branch
                enumerations).secondEmbedding a).val)))) = _
  rw [target_second_physical_transport]

private theorem target_tail_transport
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (x y sourceX sourceY : TailVertex)
    (hx : tailVertexPerm .uuu
      ((selectedPositionPermTwo .uuu
        (blockTwoSwapTargetPosition selected)).symm x) = sourceX)
    (hy : tailVertexPerm .uuu
      ((selectedPositionPermTwo .uuu
        (blockTwoSwapTargetPosition selected)).symm y) = sourceY) :
    (swapNormalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        x y =
      hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          sourceX sourceY) := by
  change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (tailVertexPerm .uuu
          ((selectedPositionPermTwo .uuu
            (blockTwoSwapTargetPosition selected)).symm x))
        (tailVertexPerm .uuu
          ((selectedPositionPermTwo .uuu
            (blockTwoSwapTargetPosition selected)).symm y))) = _
  rw [hx, hy]

/-- On the fourteen old vertices of the restored K15, the semantic transport
is exactly the `4|5|5` coordinate swap followed by host-colour `1 ↔ 2`.
This is the matrix action used by the finite discovery quotient. -/
theorem ownNeighborhoodHostColoring_swap
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (u v : Fin 14) :
    ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring
        (swapNormalizeForeignSupportEnumerations selected branch enumerations)
        u v =
      hostColorPerm
        (ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring
          enumerations (restoredK15CoordinateSwap u)
          (restoredK15CoordinateSwap v)) := by
  rw [← ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.apply_symm_apply u,
    ← ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.apply_symm_apply v]
  generalize ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm u = cu
  generalize ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm v = cv
  rcases cu with (left | second)
  · rcases left with (free | first)
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
            pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
            ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
            ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
            swapForeignCoordinate,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
            using target_inside_transport selected branch free.castSucc free'.castSucc
        · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
            pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
            ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
            ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
            swapForeignCoordinate,
            ProfileDFourSupportForeignSupports61.firstForeignBlock,
            ProfileDFourSupportForeignSupports61.secondForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
            using target_row_first_transport selected branch enumerations
              free.castSucc first'
      · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
          pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
          ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
          ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
          swapForeignCoordinate,
          ProfileDFourSupportForeignSupports61.firstForeignBlock,
          ProfileDFourSupportForeignSupports61.secondForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
          using target_row_second_transport selected branch enumerations
            free.castSucc second'
    · rcases cv with (right | second')
      · rcases right with (free' | first')
        · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
            pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
            ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
            ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
            swapForeignCoordinate,
            ProfileDFourSupportForeignSupports61.firstForeignBlock,
            ProfileDFourSupportForeignSupports61.secondForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
            using target_row_first_transport selected branch enumerations
              free'.castSucc first
        · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
            pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
            ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
            ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
            swapForeignCoordinate,
            ProfileDFourSupportForeignSupports61.firstForeignBlock,
            ProfileDFourSupportForeignSupports61.secondForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
            ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
            ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
            using target_tail_transport selected branch
              (blockVertex 0 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).firstEmbedding first).val)
              (blockVertex 0 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).firstEmbedding first').val)
              (blockVertex 1 (enumerations.secondEmbedding first).val)
              (blockVertex 1 (enumerations.secondEmbedding first').val)
              (target_first_physical_transport selected branch enumerations first)
              (target_first_physical_transport selected branch enumerations first')
      · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
          pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
          ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
          ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
          swapForeignCoordinate,
          ProfileDFourSupportForeignSupports61.firstForeignBlock,
          ProfileDFourSupportForeignSupports61.secondForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
          using target_tail_transport selected branch
            (blockVertex 0 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).firstEmbedding first).val)
            (blockVertex 1 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).secondEmbedding second').val)
            (blockVertex 1 (enumerations.secondEmbedding first).val)
            (blockVertex 0 (enumerations.firstEmbedding second').val)
            (target_first_physical_transport selected branch enumerations first)
            (target_second_physical_transport selected branch enumerations second')
  · rcases cv with (right | second')
    · rcases right with (free' | first')
      · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
          pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
          ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
          ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
          swapForeignCoordinate,
          ProfileDFourSupportForeignSupports61.firstForeignBlock,
          ProfileDFourSupportForeignSupports61.secondForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
          using target_row_second_transport selected branch enumerations
            free'.castSucc second
      · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
          pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
          ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
          ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
          swapForeignCoordinate,
          ProfileDFourSupportForeignSupports61.firstForeignBlock,
          ProfileDFourSupportForeignSupports61.secondForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
          ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
          ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
          using target_tail_transport selected branch
            (blockVertex 1 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).secondEmbedding second).val)
            (blockVertex 0 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).firstEmbedding first').val)
            (blockVertex 0 (enumerations.firstEmbedding second).val)
            (blockVertex 1 (enumerations.secondEmbedding first').val)
            (target_second_physical_transport selected branch enumerations second)
            (target_first_physical_transport selected branch enumerations first')
    · simpa [ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring,
        pullbackColoring, ProfileDFourSupportRestoredRootK15.neighborhoodEmbedding,
        ProfileDFourSupportRestoredRootK15.neighborhoodEmbeddingOnCoordinates,
        ProfileDFourSupportRestoredRootK15.retainedJoinedColoring,
        swapForeignCoordinate,
        ProfileDFourSupportForeignSupports61.firstForeignBlock,
        ProfileDFourSupportForeignSupports61.secondForeignBlock,
        ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
        ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
        ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
        using target_tail_transport selected branch
          (blockVertex 1 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).secondEmbedding second).val)
          (blockVertex 1 ((swapNormalizeForeignSupportEnumerations selected branch enumerations).secondEmbedding second').val)
          (blockVertex 0 (enumerations.firstEmbedding second).val)
          (blockVertex 0 (enumerations.firstEmbedding second').val)
          (target_second_physical_transport selected branch enumerations second)
          (target_second_physical_transport selected branch enumerations second')

/-! ## The restored root is compatible with the same action -/

@[simp] theorem hostColorPerm_one : hostColorPerm (1 : Fin 4) = 2 := by
  decide

@[simp] theorem hostColorPerm_two : hostColorPerm (2 : Fin 4) = 1 := by
  decide

@[simp] theorem hostColorPerm_three : hostColorPerm (3 : Fin 4) = 3 := by
  decide

theorem restoredRootHostAttachment_swap
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (i : Fin 14) :
    ProfileDFourSupportRestoredRootK15.restoredRootHostAttachment
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic i =
      hostColorPerm
        (ProfileDFourSupportRestoredRootK15.restoredRootHostAttachment
          branch.toSemantic (restoredK15CoordinateSwap i)) := by
  rw [← ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.apply_symm_apply i]
  generalize ProfileDFourSupportRestoredRootK15.fourFiveFiveEquiv.symm i = c
  rcases c with (left | second)
  · rcases left with (free | first) <;>
      simp [ProfileDFourSupportRestoredRootK15.restoredRootHostAttachment,
        swapForeignCoordinate,
        ProfileDFourSupportRestoredRootK15.freeHostForbiddenColor,
        ProfileDFourSupportRestoredRootK15.firstForeignHostForbiddenColor,
        ProfileDFourSupportRestoredRootK15.secondForeignHostForbiddenColor,
        ProfileDFourSupportForeignSupports61.firstForeignBlock,
        ProfileDFourSupportForeignSupports61.secondForeignBlock,
        ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
        ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
        ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
  · simp [ProfileDFourSupportRestoredRootK15.restoredRootHostAttachment,
      swapForeignCoordinate,
      ProfileDFourSupportRestoredRootK15.firstForeignHostForbiddenColor,
      ProfileDFourSupportRestoredRootK15.secondForeignHostForbiddenColor,
      ProfileDFourSupportForeignSupports61.firstForeignBlock,
      ProfileDFourSupportForeignSupports61.secondForeignBlock,
      ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
      ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
      ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport.toSemantic]
    decide

/-- Extend the old-vertex coordinate swap by fixing the restored root. -/
noncomputable def liftRestoredK15CoordinateSwap : Fin 15 ≃ Fin 15 where
  toFun := Fin.lastCases (Fin.last 14)
    (fun i => (restoredK15CoordinateSwap i).castSucc)
  invFun := Fin.lastCases (Fin.last 14)
    (fun i => (restoredK15CoordinateSwap.symm i).castSucc)
  left_inv := by
    intro x
    induction x using Fin.lastCases with
    | last => rfl
    | cast i => simp
  right_inv := by
    intro x
    induction x using Fin.lastCases with
    | last => rfl
    | cast i => simp

@[simp] theorem liftRestoredK15CoordinateSwap_last :
    liftRestoredK15CoordinateSwap (Fin.last 14) = Fin.last 14 := by
  rfl

@[simp] theorem liftRestoredK15CoordinateSwap_castSucc (i : Fin 14) :
    liftRestoredK15CoordinateSwap i.castSucc =
      (restoredK15CoordinateSwap i).castSucc := by
  simp [liftRestoredK15CoordinateSwap]

/-- The complete restored-root host-colouring, not just its old `14×14`
submatrix, is transported by the lifted coordinate swap and colour `1 ↔ 2`. -/
theorem restoredRootHostK15_swap
    (selected : BlockTwoPosition)
    (branch : PositionedFourSupport .uuu 2 selected)
    (enumerations :
      ProfileDFourSupportRestoredRootK15.ForeignSupportEnumerations
        branch.toSemantic)
    (u v : Fin 15) :
    ProfileDFourSupportRestoredRootK15.restoredRootHostK15
        (swapNormalizeForeignSupportEnumerations selected branch enumerations)
        u v =
      hostColorPerm
        (ProfileDFourSupportRestoredRootK15.restoredRootHostK15
          enumerations (liftRestoredK15CoordinateSwap u)
          (liftRestoredK15CoordinateSwap v)) := by
  change extendByLast
      (ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring
        (swapNormalizeForeignSupportEnumerations selected branch enumerations))
      (ProfileDFourSupportRestoredRootK15.restoredRootHostAttachment
        (swapNormalizeFourSupportBlockTwo selected branch).toSemantic)
      0 u v =
    hostColorPerm
      (extendByLast
        (ProfileDFourSupportRestoredRootK15.ownNeighborhoodHostColoring
          enumerations)
        (ProfileDFourSupportRestoredRootK15.restoredRootHostAttachment
          branch.toSemantic)
        0 (liftRestoredK15CoordinateSwap u)
          (liftRestoredK15CoordinateSwap v))
  induction u using Fin.lastCases with
  | last =>
      induction v using Fin.lastCases with
      | last =>
          change (0 : Fin 4) = hostColorPerm 0
          rfl
      | cast j =>
          rw [extendByLast_last_old, liftRestoredK15CoordinateSwap_last,
            liftRestoredK15CoordinateSwap_castSucc, extendByLast_last_old]
          exact restoredRootHostAttachment_swap selected branch j
  | cast i =>
      induction v using Fin.lastCases with
      | last =>
          rw [extendByLast_old_last, liftRestoredK15CoordinateSwap_castSucc,
            liftRestoredK15CoordinateSwap_last, extendByLast_old_last]
          exact restoredRootHostAttachment_swap selected branch i
      | cast j =>
          rw [extendByLast_old_old, liftRestoredK15CoordinateSwap_castSucc,
            liftRestoredK15CoordinateSwap_castSucc, extendByLast_old_old]
          exact ownNeighborhoodHostColoring_swap
            selected branch enumerations i j

#print axioms swapFourSupportBlockTwo
#print axioms swapNormalizeFourSupportBlockTwo
#print axioms swapNormalizeFourSupportBlockTwo_tailOwnDegree
#print axioms mem_foreignOwnSupport_swapNormalize_blockZero
#print axioms mem_foreignOwnSupport_swapNormalize_blockOne
#print axioms swapNormalizeForeignSupportEnumerations
#print axioms ownNeighborhoodHostColoring_swap
#print axioms restoredRootHostAttachment_swap
#print axioms restoredRootHostK15_swap

end ProfileDUUUFourSupportBlockTwoSwap61
end R4333
