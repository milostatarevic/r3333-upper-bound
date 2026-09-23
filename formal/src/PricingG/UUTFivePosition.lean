import R4333Lean.ProfileDUUUFiveSupportPositionSymmetry
namespace R4333
namespace UUTFivePosition
open ColoringJoinRows SingleRootStarCNF
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDRowSupportBounds61 ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open ProfileDSelectedPositionTransport
open ProfileDFourRowKindSymmetry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind
abbrev TailVertex := ProfileDRowExtension.TailVertex
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev FiveExtension := ProfileDHighOwnFiveRowSplit61.FiveExtension
abbrev DegreeFlooredFiveExtension :=
  ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension
abbrev SemanticFiveSupport :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension


open ProfileDUUUFiveSupportPositionSymmetry
noncomputable def normalizeDegreeBlockZero
    (ext : DegreeFlooredFiveExtension .uut) (selected : Fin 15) :
    DegreeFlooredFiveExtension .uut :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermZero .uut selected).symm
    (selectedPositionPermZero_symm_templateCanonical
      ext.toFiveExtension.tail selected)

noncomputable def normalizeDegreeBlockOne
    (ext : DegreeFlooredFiveExtension .uut) (selected : Fin 15) :
    DegreeFlooredFiveExtension .uut :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermOne .uut selected).symm
    (selectedPositionPermOne_symm_templateCanonical
      ext.toFiveExtension.tail selected)

noncomputable def normalizeDegreeBlockTwo
    (ext : DegreeFlooredFiveExtension .uut) (selected : Fin 16) :
    DegreeFlooredFiveExtension .uut :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermTwo .uut selected).symm
    (selectedPositionPermTwo_symm_templateCanonical
      ext.toFiveExtension.tail selected)

def k15Representative (selected : Fin 15) : Fin 15 :=
  k15UntwistedPositionRepresentative selected

theorem k15Representative_mem (selected : Fin 15) :
    k15Representative selected ∈ ({0, 1, 2} : Finset (Fin 15)) := by
  exact k15UntwistedPositionRepresentative_mem selected

theorem selectedPositionPermZero_uut_selected (selected : Fin 15) :
    selectedPositionPermZero .uut selected (blockVertex 0 selected.val) =
      blockVertex 0 (k15Representative selected).val := by
  rw [selectedPositionPermZero_blockZero,
    k15SelectedPositionEquiv_selected]
  rfl

theorem selectedPositionPermOne_uut_selected (selected : Fin 15) :
    selectedPositionPermOne .uut selected (blockVertex 1 selected.val) =
      blockVertex 1 (k15Representative selected).val := by
  rw [selectedPositionPermOne_blockOne,
    k15SelectedPositionEquiv_selected]
  rfl

theorem selectedPositionPermTwo_uut_selected (selected : Fin 16) :
    selectedPositionPermTwo .uut selected (blockVertex 2 selected.val) =
      blockVertex 2 (Fin.last 15).val := by
  rw [selectedPositionPermTwo_blockTwo,
    k16TemplateToLastEquiv_apply, k16TemplateToLastMap_deleted]

private theorem normalized_tailDegree_zero
    (tail : Witness .uut) (selected : Fin 15) (q : Fin 4) :
    colorDegree
        (transportWitnessByTailPerm tail
          (selectedPositionPermZero .uut selected).symm
          (selectedPositionPermZero_symm_templateCanonical tail selected)).coloring
        q (blockVertex 0 (k15Representative selected).val) =
      colorDegree tail.coloring q (blockVertex 0 selected.val) := by
  change colorDegree
      (relabelVertices tail.coloring
        (selectedPositionPermZero .uut selected).symm)
      q (blockVertex 0 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermZero_uut_selected selected,
    Equiv.symm_apply_apply]

private theorem normalized_tailDegree_one
    (tail : Witness .uut) (selected : Fin 15) (q : Fin 4) :
    colorDegree
        (transportWitnessByTailPerm tail
          (selectedPositionPermOne .uut selected).symm
          (selectedPositionPermOne_symm_templateCanonical tail selected)).coloring
        q (blockVertex 1 (k15Representative selected).val) =
      colorDegree tail.coloring q (blockVertex 1 selected.val) := by
  change colorDegree
      (relabelVertices tail.coloring
        (selectedPositionPermOne .uut selected).symm)
      q (blockVertex 1 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermOne_uut_selected selected,
    Equiv.symm_apply_apply]

private theorem normalized_tailDegree_two
    (tail : Witness .uut) (selected : Fin 16) (q : Fin 4) :
    colorDegree
        (transportWitnessByTailPerm tail
          (selectedPositionPermTwo .uut selected).symm
          (selectedPositionPermTwo_symm_templateCanonical tail selected)).coloring
        q (blockVertex 2 (Fin.last 15).val) =
      colorDegree tail.coloring q (blockVertex 2 selected.val) := by
  change colorDegree
      (relabelVertices tail.coloring
        (selectedPositionPermTwo .uut selected).symm)
      q (blockVertex 2 (Fin.last 15).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermTwo_uut_selected selected,
    Equiv.symm_apply_apply]

noncomputable def normalizeSupportBlockZero (selected : Fin 15)
    (branch : PositionedFiveSupport .uut 0 selected) :
    PositionedFiveSupport .uut 0 (k15Representative selected) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockZero branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermZero .uut selected).symm
        (blockVertex 0 (k15Representative selected).val)) = _
    rw [← selectedPositionPermZero_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uut selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val)
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermZero_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uut selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermZero_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper

noncomputable def normalizeSupportBlockOne (selected : Fin 15)
    (branch : PositionedFiveSupport .uut 1 selected) :
    PositionedFiveSupport .uut 1 (k15Representative selected) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockOne branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermOne .uut selected).symm
        (blockVertex 1 (k15Representative selected).val)) = _
    rw [← selectedPositionPermOne_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermOne .uut selected).symm)
      (blockRootColor 1)
      (blockVertex 1 (k15Representative selected).val)
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermOne_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermOne .uut selected).symm)
      (blockRootColor 1)
      (blockVertex 1 (k15Representative selected).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermOne_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper

noncomputable def normalizeSupportBlockTwo (selected : Fin 16)
    (branch : PositionedFiveSupport .uut 2 selected) :
    PositionedFiveSupport .uut 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockTwo branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 2 (Fin.last 15).val)) = _
    rw [← selectedPositionPermTwo_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uut selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val)
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermTwo_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uut selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermTwo_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper

/-! ## Swapping the two equal K15 blocks -/

@[simp] theorem swapKind_uut : swapKind .uut = .uut := rfl

noncomputable def swapDegreeFlooredUUT
    (ext : DegreeFlooredFiveExtension .uut) :
    DegreeFlooredFiveExtension .uut := by
  simpa using swapDegreeFlooredFive ext

noncomputable def blockOneTargetPosition (selected : Fin 15) : Fin 15 :=
  (localK15Zero .uut).symm selected

theorem tailVertexPerm_uut_blockOneTarget (selected : Fin 15) :
    tailVertexPerm .uut
        (blockVertex 0 (blockOneTargetPosition selected).val) =
      blockVertex 1 selected.val := by
  rw [tailVertexPerm_blockZero]
  simp [blockOneTargetPosition]

@[simp] theorem hostColorPerm_blockOneRoot :
    hostColorPerm (blockRootColor 1) = blockRootColor 0 := by
  decide

@[simp] theorem hostColorPerm_symm_blockZeroRoot :
    hostColorPerm.symm (blockRootColor 0) = blockRootColor 1 := by
  decide

private theorem swapped_tailDegree_blockOneToZero
    (tail : Witness .uut) (selected : Fin 15) :
    colorDegree (transportWitness tail).coloring (blockRootColor 0)
        (blockVertex 0 (blockOneTargetPosition selected).val) =
      colorDegree tail.coloring (blockRootColor 1)
        (blockVertex 1 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices tail.coloring (tailVertexPerm .uut))
        hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockZeroRoot,
    tailVertexPerm_uut_blockOneTarget]

noncomputable def swapSupportBlockOneToZero (selected : Fin 15)
    (branch : PositionedFiveSupport .uut 1 selected) :
    PositionedFiveSupport .uut 0 (blockOneTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    swapDegreeFlooredUUT branch.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro row
    change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (tailVertexPerm .uut
          (blockVertex 0 (blockOneTargetPosition selected).val))) = _
    rw [tailVertexPerm_uut_blockOneTarget, branch.allFiveOwn]
    exact hostColorPerm_blockOneRoot
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (transportWitness
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val)
    rw [swapped_tailDegree_blockOneToZero]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (transportWitness
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail).coloring
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) ≤ 10
    rw [swapped_tailDegree_blockOneToZero]
    exact branch.tailOwnDegreeUpper


#print axioms normalizeSupportBlockTwo
#print axioms swapDegreeFlooredUUT
end UUTFivePosition
end R4333
