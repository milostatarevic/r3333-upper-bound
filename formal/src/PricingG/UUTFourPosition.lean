import R4333Lean.ProfileDUUUFourSupportPositionSymmetry61
import PricingG.UUTFivePosition
namespace R4333.UUTFourPosition
open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDUUUDegreeTenFiniteBoundary61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev UUTFivePosition.Kind := ProfileDTripleJoinReduction.Kind
abbrev UUTFivePosition.TailVertex := ProfileDRowExtension.TailVertex

abbrev SemanticFourSupport :=
  ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension

abbrev UUTFivePosition.DegreeFlooredFiveExtension :=
  ProfileDHighOwnFiveRowSplit61.DegreeFlooredFiveExtension


open ProfileDUUUFourSupportPositionSymmetry61
noncomputable def normalizeFourSupportBlockZero (selected : Fin 15)
    (branch : PositionedFourSupport .uut 0 selected) :
    PositionedFourSupport .uut 0 (UUTFivePosition.k15Representative selected) where
  toDegreeFlooredFiveExtension :=
    UUTFivePosition.normalizeDegreeBlockZero branch.toDegreeFlooredFiveExtension selected
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      ((selectedPositionPermZero .uut selected).symm
        (blockVertex 0 (UUTFivePosition.k15Representative selected).val)) = _
    rw [← UUTFivePosition.selectedPositionPermZero_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      ((selectedPositionPermZero .uut selected).symm
        (blockVertex 0 (UUTFivePosition.k15Representative selected).val)) ≠ _
    rw [← UUTFivePosition.selectedPositionPermZero_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uut selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (UUTFivePosition.k15Representative selected).val) = 10
    rw [colorDegree_relabelVertices,
      ← UUTFivePosition.selectedPositionPermZero_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeEqTen

theorem normalizeFourSupportBlockZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFourSupport .uut 0 selected) :
    colorDegree
        (normalizeFourSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (UUTFivePosition.k15Representative selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0) (blockVertex 0 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uut selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (UUTFivePosition.k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← UUTFivePosition.selectedPositionPermZero_uut_selected selected,
    Equiv.symm_apply_apply]

noncomputable def normalizeFourSupportBlockTwo (selected : Fin 16)
    (branch : PositionedFourSupport .uut 2 selected) :
    PositionedFourSupport .uut 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension :=
    UUTFivePosition.normalizeDegreeBlockTwo branch.toDegreeFlooredFiveExtension selected
  firstFourOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      row.castSucc
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 2 (Fin.last 15).val)) = _
    rw [← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.firstFourOwn row
  fifthNotOwn := by
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      (Fin.last 4)
      ((selectedPositionPermTwo .uut selected).symm
        (blockVertex 2 (Fin.last 15).val)) ≠ _
    rw [← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.fifthNotOwn
  tailOwnDegreeEqTen := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uut selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = 10
    rw [colorDegree_relabelVertices,
      ← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeEqTen

theorem normalizeFourSupportBlockTwo_tailOwnDegree
    (selected : Fin 16)
    (branch : PositionedFourSupport .uut 2 selected) :
    colorDegree
        (normalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uut selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = _
  rw [colorDegree_relabelVertices]
  rw [← UUTFivePosition.selectedPositionPermTwo_uut_selected selected,
    Equiv.symm_apply_apply]

@[simp] theorem normalizeFourSupportBlockZero_rows
    (selected : Fin 15)
    (branch : PositionedFourSupport .uut 0 selected)
    (row : Fin 5) (x : UUTFivePosition.TailVertex) :
    (normalizeFourSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        ((selectedPositionPermZero .uut selected).symm x) := by
  rfl

@[simp] theorem normalizeFourSupportBlockTwo_rows
    (selected : Fin 16)
    (branch : PositionedFourSupport .uut 2 selected)
    (row : Fin 5) (x : UUTFivePosition.TailVertex) :
    (normalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        ((selectedPositionPermTwo .uut selected).symm x) := by
  rfl

theorem normalizeFourSupportBlockZero_rowSupport_card
    (selected : Fin 15)
    (branch : PositionedFourSupport .uut 0 selected)
    (row : Fin 5) (q : Fin 4) :
    (rowColorSupport
      ((normalizeFourSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row) q).card =
      (rowColorSupport
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row)
        q).card := by
  change (rowColorSupport
      ((transportFiveExtensionByTailPerm
        branch.toDegreeFlooredFiveExtension.toFiveExtension
        (selectedPositionPermZero .uut selected).symm
        (selectedPositionPermZero_symm_templateCanonical
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
          selected)).rows row) q).card = _
  exact transportFiveExtensionByTailPerm_rowSupport_card
    branch.toDegreeFlooredFiveExtension.toFiveExtension
    (selectedPositionPermZero .uut selected).symm
    (selectedPositionPermZero_symm_templateCanonical
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail selected)
    row q

theorem normalizeFourSupportBlockTwo_rowSupport_card
    (selected : Fin 16)
    (branch : PositionedFourSupport .uut 2 selected)
    (row : Fin 5) (q : Fin 4) :
    (rowColorSupport
      ((normalizeFourSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row) q).card =
      (rowColorSupport
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row)
        q).card := by
  change (rowColorSupport
      ((transportFiveExtensionByTailPerm
        branch.toDegreeFlooredFiveExtension.toFiveExtension
        (selectedPositionPermTwo .uut selected).symm
        (selectedPositionPermTwo_symm_templateCanonical
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail
          selected)).rows row) q).card = _
  exact transportFiveExtensionByTailPerm_rowSupport_card
    branch.toDegreeFlooredFiveExtension.toFiveExtension
    (selectedPositionPermTwo .uut selected).symm
    (selectedPositionPermTwo_symm_templateCanonical
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail selected)
    row q

/-! ## Swapping block one to block zero -/

noncomputable def swapFourSupportBlockOneToZero (selected : Fin 15)
    (branch : PositionedFourSupport .uut 1 selected) :
    PositionedFourSupport .uut 0 (UUTFivePosition.blockOneTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    UUTFivePosition.swapDegreeFlooredUUT branch.toDegreeFlooredFiveExtension
  firstFourOwn := by
    intro row
    change ProfileDFourRowKindSymmetry.hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row.castSucc
        (ProfileDFourRowKindSymmetry.tailVertexPerm .uut
          (blockVertex 0 (UUTFivePosition.blockOneTargetPosition selected).val))) = _
    rw [UUTFivePosition.tailVertexPerm_uut_blockOneTarget, branch.firstFourOwn]
    exact UUTFivePosition.hostColorPerm_blockOneRoot
  fifthNotOwn := by
    change ProfileDFourRowKindSymmetry.hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows (Fin.last 4)
        (ProfileDFourRowKindSymmetry.tailVertexPerm .uut
          (blockVertex 0 (UUTFivePosition.blockOneTargetPosition selected).val))) ≠ _
    rw [UUTFivePosition.tailVertexPerm_uut_blockOneTarget]
    intro hcolor
    apply branch.fifthNotOwn
    apply ProfileDFourRowKindSymmetry.hostColorPerm.injective
    exact hcolor.trans UUTFivePosition.hostColorPerm_blockOneRoot.symm
  tailOwnDegreeEqTen := by
    change colorDegree
      (mapEdgeColors
        (relabelVertices
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uut))
        ProfileDFourRowKindSymmetry.hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (UUTFivePosition.blockOneTargetPosition selected).val) = 10
    rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
      UUTFivePosition.hostColorPerm_symm_blockZeroRoot,
      UUTFivePosition.tailVertexPerm_uut_blockOneTarget]
    exact branch.tailOwnDegreeEqTen

theorem swapFourSupportBlockOneToZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFourSupport .uut 1 selected) :
    colorDegree
        (swapFourSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (UUTFivePosition.blockOneTargetPosition selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1) (blockVertex 1 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uut))
        ProfileDFourRowKindSymmetry.hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (UUTFivePosition.blockOneTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    UUTFivePosition.hostColorPerm_symm_blockZeroRoot,
    UUTFivePosition.tailVertexPerm_uut_blockOneTarget]

@[simp] theorem swapFourSupportBlockOneToZero_rows
    (selected : Fin 15)
    (branch : PositionedFourSupport .uut 1 selected)
    (row : Fin 5) (x : UUTFivePosition.TailVertex) :
    (swapFourSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row x =
      ProfileDFourRowKindSymmetry.hostColorPerm
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uut x)) := by
  rfl

theorem swapFourSupportBlockOneToZero_rowSupport_card
    (selected : Fin 15)
    (branch : PositionedFourSupport .uut 1 selected)
    (row : Fin 5) (q : Fin 4) :
    (rowColorSupport
      ((swapFourSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.rows
        row) q).card =
      (rowColorSupport
        (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row)
        (ProfileDFourRowKindSymmetry.hostColorPerm.symm q)).card := by
  change (rowColorSupport
      ((swapFiveExtension
        branch.toDegreeFlooredFiveExtension.toFiveExtension).rows row)
        q).card = _
  exact swapped_rowColorSupport_card
    branch.toDegreeFlooredFiveExtension.toFiveExtension row q


#print axioms normalizeFourSupportBlockTwo
end R4333.UUTFourPosition
