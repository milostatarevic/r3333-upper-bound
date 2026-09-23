import R4333Lean.ProfileDHighOwnFiveSupportC5CheckedBoundary
import R4333Lean.CriticalTemplateSelectedPositionOrbits
import R4333Lean.NormalizedCanonicalAttaching61

/-!
# Exact selected-position quotient for the UUU five-support branch

This module transports the five retained rows through the already-certified
critical-template automorphisms.  It proves that every UUU five-support
object reduces to exactly four displayed position families:

* block zero, positions `0`, `1`, or `2`; and
* block two, position `15`.

The equal `K15` blocks are merged by the existing block/host-colour swap.
The three remaining `K15` classes are distinguished by their colour-degree
signature in the untwisted `K15`; the swap induces the identity permutation
on the local three-colour labels, so it cannot merge those classes.  The
`K16` family remains separate because its block has order sixteen.

No search result or unsatisfiability claim is used here.
-/

namespace R4333
namespace ProfileDUUUFiveSupportPositionSymmetry

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

/-! ## A block/position-indexed semantic object -/

structure PositionedFiveSupport (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)) where
  toDegreeFlooredFiveExtension : DegreeFlooredFiveExtension kind
  allFiveOwn : ∀ a : FiveVertex,
    toDegreeFlooredFiveExtension.toFiveExtension.rows a
        (blockVertex block position.val) = blockRootColor block
  tailOwnDegreeLower :
    9 ≤ colorDegree
      toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val)
  tailOwnDegreeUpper :
    colorDegree
      toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor block) (blockVertex block position.val) ≤ 10

def PositionedFiveSupport.toSemantic {kind : Kind} {block : Fin 3}
    {position : Fin (blockSize block)}
    (branch : PositionedFiveSupport kind block position) :
    SemanticFiveSupport kind where
  toDegreeFlooredFiveExtension := branch.toDegreeFlooredFiveExtension
  block := block
  position := position
  allFiveOwn := branch.allFiveOwn
  tailOwnDegreeLower := branch.tailOwnDegreeLower
  tailOwnDegreeUpper := branch.tailOwnDegreeUpper

def PositionedFiveSupport.ofSemantic {kind : Kind}
    (ext : SemanticFiveSupport kind) :
    PositionedFiveSupport kind ext.block ext.position where
  toDegreeFlooredFiveExtension := ext.toDegreeFlooredFiveExtension
  allFiveOwn := ext.allFiveOwn
  tailOwnDegreeLower := ext.tailOwnDegreeLower
  tailOwnDegreeUpper := ext.tailOwnDegreeUpper

/-! ## Five-row transport through a certified tail permutation -/

noncomputable def transportFiveExtensionByTailPerm {kind : Kind}
    (ext : FiveExtension kind) (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < blockSize block → right < blockSize block → left < right →
      ext.tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (blockSize block) (kind.twisted block)
            left right)) : FiveExtension kind where
  tail := transportWitnessByTailPerm ext.tail perm hcanonical
  inside := ext.inside
  rows := fun row x => ext.rows row (perm x)
  insideNoMono := ext.insideNoMono
  insideRootForbidden := ext.insideRootForbidden
  rowsAdmissible := by
    intro row x y hxy hbad
    apply ext.rowsAdmissible row (perm x) (perm y) (perm.injective.ne hxy)
    simpa [transportWitnessByTailPerm] using hbad
  rowsPairCompatible := by
    intro left right hlr x hbad
    exact ext.rowsPairCompatible left right hlr (perm x) hbad

theorem transportFiveExtensionByTailPerm_rowSupport_card
    {kind : Kind} (ext : FiveExtension kind)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < blockSize block → right < blockSize block → left < right →
      ext.tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (blockSize block) (kind.twisted block)
            left right))
    (row : FiveVertex) (q : Fin 4) :
    (rowColorSupport
      ((transportFiveExtensionByTailPerm ext perm hcanonical).rows row) q).card =
      (rowColorSupport (ext.rows row) q).card := by
  simpa [transportFiveExtensionByTailPerm, Function.comp_def] using
    (ProfileDBlockZeroSupport.rowColorSupport_card_comp_equiv
      perm (ext.rows row) q)

noncomputable def transportDegreeFlooredFiveByTailPerm {kind : Kind}
    (ext : DegreeFlooredFiveExtension kind)
    (perm : Equiv.Perm TailVertex)
    (hcanonical : ∀ (block : Fin 3) (left right : Nat),
      left < blockSize block → right < blockSize block → left < right →
      ext.toFiveExtension.tail.coloring (perm (blockVertex block left))
          (perm (blockVertex block right)) =
        canonicalPalette (Fin.succ block)
          (templateColor (blockSize block) (kind.twisted block)
            left right)) : DegreeFlooredFiveExtension kind where
  toFiveExtension :=
    transportFiveExtensionByTailPerm ext.toFiveExtension perm hcanonical
  zeroSupportLower := by
    intro row
    rw [transportFiveExtensionByTailPerm_rowSupport_card]
    exact ext.zeroSupportLower row
  zeroSupportUpper := by
    intro row
    rw [transportFiveExtensionByTailPerm_rowSupport_card]
    exact ext.zeroSupportUpper row
  nonzeroSupportLower := by
    intro row q hq
    rw [transportFiveExtensionByTailPerm_rowSupport_card]
    exact ext.nonzeroSupportLower row q hq
  nonzeroSupportUpper := by
    intro row q hq
    rw [transportFiveExtensionByTailPerm_rowSupport_card]
    exact ext.nonzeroSupportUpper row q hq

noncomputable def normalizeDegreeBlockZero
    (ext : DegreeFlooredFiveExtension .uuu) (selected : Fin 15) :
    DegreeFlooredFiveExtension .uuu :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermZero .uuu selected).symm
    (selectedPositionPermZero_symm_templateCanonical
      ext.toFiveExtension.tail selected)

noncomputable def normalizeDegreeBlockOne
    (ext : DegreeFlooredFiveExtension .uuu) (selected : Fin 15) :
    DegreeFlooredFiveExtension .uuu :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermOne .uuu selected).symm
    (selectedPositionPermOne_symm_templateCanonical
      ext.toFiveExtension.tail selected)

noncomputable def normalizeDegreeBlockTwo
    (ext : DegreeFlooredFiveExtension .uuu) (selected : Fin 16) :
    DegreeFlooredFiveExtension .uuu :=
  transportDegreeFlooredFiveByTailPerm ext
    (selectedPositionPermTwo .uuu selected).symm
    (selectedPositionPermTwo_symm_templateCanonical
      ext.toFiveExtension.tail selected)

def k15Representative (selected : Fin 15) : Fin 15 :=
  k15UntwistedPositionRepresentative selected

theorem k15Representative_mem (selected : Fin 15) :
    k15Representative selected ∈ ({0, 1, 2} : Finset (Fin 15)) := by
  exact k15UntwistedPositionRepresentative_mem selected

theorem selectedPositionPermZero_uuu_selected (selected : Fin 15) :
    selectedPositionPermZero .uuu selected (blockVertex 0 selected.val) =
      blockVertex 0 (k15Representative selected).val := by
  rw [selectedPositionPermZero_blockZero,
    k15SelectedPositionEquiv_selected]
  rfl

theorem selectedPositionPermOne_uuu_selected (selected : Fin 15) :
    selectedPositionPermOne .uuu selected (blockVertex 1 selected.val) =
      blockVertex 1 (k15Representative selected).val := by
  rw [selectedPositionPermOne_blockOne,
    k15SelectedPositionEquiv_selected]
  rfl

theorem selectedPositionPermTwo_uuu_selected (selected : Fin 16) :
    selectedPositionPermTwo .uuu selected (blockVertex 2 selected.val) =
      blockVertex 2 (Fin.last 15).val := by
  rw [selectedPositionPermTwo_blockTwo,
    k16TemplateToLastEquiv_apply, k16TemplateToLastMap_deleted]

private theorem normalized_tailDegree_zero
    (tail : Witness .uuu) (selected : Fin 15) (q : Fin 4) :
    colorDegree
        (transportWitnessByTailPerm tail
          (selectedPositionPermZero .uuu selected).symm
          (selectedPositionPermZero_symm_templateCanonical tail selected)).coloring
        q (blockVertex 0 (k15Representative selected).val) =
      colorDegree tail.coloring q (blockVertex 0 selected.val) := by
  change colorDegree
      (relabelVertices tail.coloring
        (selectedPositionPermZero .uuu selected).symm)
      q (blockVertex 0 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermZero_uuu_selected selected,
    Equiv.symm_apply_apply]

private theorem normalized_tailDegree_one
    (tail : Witness .uuu) (selected : Fin 15) (q : Fin 4) :
    colorDegree
        (transportWitnessByTailPerm tail
          (selectedPositionPermOne .uuu selected).symm
          (selectedPositionPermOne_symm_templateCanonical tail selected)).coloring
        q (blockVertex 1 (k15Representative selected).val) =
      colorDegree tail.coloring q (blockVertex 1 selected.val) := by
  change colorDegree
      (relabelVertices tail.coloring
        (selectedPositionPermOne .uuu selected).symm)
      q (blockVertex 1 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermOne_uuu_selected selected,
    Equiv.symm_apply_apply]

private theorem normalized_tailDegree_two
    (tail : Witness .uuu) (selected : Fin 16) (q : Fin 4) :
    colorDegree
        (transportWitnessByTailPerm tail
          (selectedPositionPermTwo .uuu selected).symm
          (selectedPositionPermTwo_symm_templateCanonical tail selected)).coloring
        q (blockVertex 2 (Fin.last 15).val) =
      colorDegree tail.coloring q (blockVertex 2 selected.val) := by
  change colorDegree
      (relabelVertices tail.coloring
        (selectedPositionPermTwo .uuu selected).symm)
      q (blockVertex 2 (Fin.last 15).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply]

noncomputable def normalizeSupportBlockZero (selected : Fin 15)
    (branch : PositionedFiveSupport .uuu 0 selected) :
    PositionedFiveSupport .uuu 0 (k15Representative selected) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockZero branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermZero .uuu selected).symm
        (blockVertex 0 (k15Representative selected).val)) = _
    rw [← selectedPositionPermZero_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uuu selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val)
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermZero_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uuu selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermZero_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper

noncomputable def normalizeSupportBlockOne (selected : Fin 15)
    (branch : PositionedFiveSupport .uuu 1 selected) :
    PositionedFiveSupport .uuu 1 (k15Representative selected) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockOne branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermOne .uuu selected).symm
        (blockVertex 1 (k15Representative selected).val)) = _
    rw [← selectedPositionPermOne_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermOne .uuu selected).symm)
      (blockRootColor 1)
      (blockVertex 1 (k15Representative selected).val)
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermOne_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermOne .uuu selected).symm)
      (blockRootColor 1)
      (blockVertex 1 (k15Representative selected).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermOne_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper

noncomputable def normalizeSupportBlockTwo (selected : Fin 16)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    PositionedFiveSupport .uuu 2 (Fin.last 15) where
  toDegreeFlooredFiveExtension :=
    normalizeDegreeBlockTwo branch.toDegreeFlooredFiveExtension selected
  allFiveOwn := by
    intro row
    change branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
      ((selectedPositionPermTwo .uuu selected).symm
        (blockVertex 2 (Fin.last 15).val)) = _
    rw [← selectedPositionPermTwo_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.allFiveOwn row
  tailOwnDegreeLower := by
    change 9 ≤ colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uuu selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val)
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermTwo_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeLower
  tailOwnDegreeUpper := by
    change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uuu selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) ≤ 10
    rw [colorDegree_relabelVertices,
      ← selectedPositionPermTwo_uuu_selected selected,
      Equiv.symm_apply_apply]
    exact branch.tailOwnDegreeUpper

/-! ## Swapping the two equal K15 blocks -/

noncomputable def swapFiveExtension {kind : Kind}
    (ext : FiveExtension kind) :
    FiveExtension (swapKind kind) where
  tail := transportWitness ext.tail
  inside := mapEdgeColors ext.inside hostColorPerm
  rows := fun row x => hostColorPerm (ext.rows row (tailVertexPerm kind x))
  insideNoMono := noMono_mapEdgeColors _ _ ext.insideNoMono
  insideRootForbidden := by
    intro left right hlr hzero
    apply ext.insideRootForbidden left right hlr
    apply hostColorPerm.injective
    simpa using hzero
  rowsAdmissible := by
    intro row x y hxy hbad
    apply ext.rowsAdmissible row
      (tailVertexPerm kind x) (tailVertexPerm kind y)
      ((tailVertexPerm kind).injective.ne hxy)
    exact ⟨hostColorPerm.injective hbad.1,
      hostColorPerm.injective hbad.2⟩
  rowsPairCompatible := by
    intro left right hlr x hbad
    apply ext.rowsPairCompatible left right hlr (tailVertexPerm kind x)
    exact ⟨hostColorPerm.injective hbad.1,
      hostColorPerm.injective hbad.2⟩

theorem swapped_rowColorSupport_card {kind : Kind}
    (ext : FiveExtension kind) (row : FiveVertex) (q : Fin 4) :
    (rowColorSupport ((swapFiveExtension ext).rows row) q).card =
      (rowColorSupport (ext.rows row) (hostColorPerm.symm q)).card := by
  classical
  let e := tailVertexPerm kind
  let source := rowColorSupport (ext.rows row) (hostColorPerm.symm q)
  have hsupport :
      rowColorSupport ((swapFiveExtension ext).rows row) q =
        source.image e.symm := by
    ext x
    simp only [mem_rowColorSupport, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      change e x ∈ source
      apply (mem_rowColorSupport
        (ext.rows row) (hostColorPerm.symm q) (e x)).2
      change hostColorPerm (ext.rows row (e x)) = q at hx
      have hback := congrArg hostColorPerm.symm hx
      simpa using hback
    · rintro ⟨y, hy, hyx⟩
      change hostColorPerm (ext.rows row (e x)) = q
      have hey : e x = y := by
        apply e.symm.injective
        simpa using hyx.symm
      rw [hey]
      have hy' : ext.rows row y = hostColorPerm.symm q :=
        (mem_rowColorSupport
          (ext.rows row) (hostColorPerm.symm q) y).1
            (by simpa [source] using hy)
      simpa using congrArg hostColorPerm hy'
  rw [hsupport, Finset.card_image_of_injective source e.symm.injective]

noncomputable def swapDegreeFlooredFive {kind : Kind}
    (ext : DegreeFlooredFiveExtension kind) :
    DegreeFlooredFiveExtension (swapKind kind) where
  toFiveExtension := swapFiveExtension ext.toFiveExtension
  zeroSupportLower := by
    intro row
    rw [swapped_rowColorSupport_card, hostColorPerm_symm_zero]
    exact ext.zeroSupportLower row
  zeroSupportUpper := by
    intro row
    rw [swapped_rowColorSupport_card, hostColorPerm_symm_zero]
    exact ext.zeroSupportUpper row
  nonzeroSupportLower := by
    intro row q hq
    rw [swapped_rowColorSupport_card]
    exact ext.nonzeroSupportLower row (hostColorPerm.symm q)
      (hostColorPerm_symm_ne_zero hq)
  nonzeroSupportUpper := by
    intro row q hq
    rw [swapped_rowColorSupport_card]
    exact ext.nonzeroSupportUpper row (hostColorPerm.symm q)
      (hostColorPerm_symm_ne_zero hq)

@[simp] theorem swapKind_uuu : swapKind .uuu = .uuu := rfl

noncomputable def swapDegreeFlooredUUU
    (ext : DegreeFlooredFiveExtension .uuu) :
    DegreeFlooredFiveExtension .uuu := by
  simpa using swapDegreeFlooredFive ext

noncomputable def blockOneTargetPosition (selected : Fin 15) : Fin 15 :=
  (localK15Zero .uuu).symm selected

theorem tailVertexPerm_uuu_blockOneTarget (selected : Fin 15) :
    tailVertexPerm .uuu
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
    (tail : Witness .uuu) (selected : Fin 15) :
    colorDegree (transportWitness tail).coloring (blockRootColor 0)
        (blockVertex 0 (blockOneTargetPosition selected).val) =
      colorDegree tail.coloring (blockRootColor 1)
        (blockVertex 1 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices tail.coloring (tailVertexPerm .uuu))
        hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockZeroRoot,
    tailVertexPerm_uuu_blockOneTarget]

noncomputable def swapSupportBlockOneToZero (selected : Fin 15)
    (branch : PositionedFiveSupport .uuu 1 selected) :
    PositionedFiveSupport .uuu 0 (blockOneTargetPosition selected) where
  toDegreeFlooredFiveExtension :=
    swapDegreeFlooredUUU branch.toDegreeFlooredFiveExtension
  allFiveOwn := by
    intro row
    change hostColorPerm
      (branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row
        (tailVertexPerm .uuu
          (blockVertex 0 (blockOneTargetPosition selected).val))) = _
    rw [tailVertexPerm_uuu_blockOneTarget, branch.allFiveOwn]
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

/-! ## The four exact representatives and semantic coverage -/

abbrev SelectedIndex := Σ block : Fin 3, Fin (blockSize block)

def k15Index (position : Fin 15) : SelectedIndex := ⟨0, position⟩
def k16Index (position : Fin 16) : SelectedIndex := ⟨2, position⟩

def uuuRepresentatives : List SelectedIndex :=
  [k15Index 0, k15Index 1, k15Index 2, k16Index (Fin.last 15)]

theorem uuuRepresentatives_length : uuuRepresentatives.length = 4 := by
  decide

theorem uuuRepresentatives_nodup : uuuRepresentatives.Nodup := by
  decide

theorem k15Index_representative_mem (selected : Fin 15) :
    k15Index (k15Representative selected) ∈ uuuRepresentatives := by
  have h := k15Representative_mem selected
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h
  · rw [h]
    exact List.Mem.head _
  · rw [h]
    exact List.Mem.tail _ (List.Mem.head _)
  · rw [h]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem k16Index_last_mem :
    k16Index (Fin.last 15) ∈ uuuRepresentatives := by
  exact List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _)))

theorem exists_positioned_representative
    (ext : SemanticFiveSupport .uuu) :
    ∃ index : SelectedIndex,
      index ∈ uuuRepresentatives ∧
        Nonempty (PositionedFiveSupport .uuu index.1 index.2) := by
  cases ext with
  | mk degree block position allFive lower upper =>
      fin_cases block
      · let source : PositionedFiveSupport .uuu 0 position :=
          ⟨degree, allFive, lower, upper⟩
        let normalized := normalizeSupportBlockZero position source
        exact ⟨k15Index (k15Representative position),
          k15Index_representative_mem position, ⟨normalized⟩⟩
      · let source : PositionedFiveSupport .uuu 1 position :=
          ⟨degree, allFive, lower, upper⟩
        let swapped := swapSupportBlockOneToZero position source
        let normalized := normalizeSupportBlockZero
          (blockOneTargetPosition position) swapped
        exact ⟨k15Index (k15Representative
            (blockOneTargetPosition position)),
          k15Index_representative_mem (blockOneTargetPosition position),
          ⟨normalized⟩⟩
      · let source : PositionedFiveSupport .uuu 2 position :=
          ⟨degree, allFive, lower, upper⟩
        let normalized := normalizeSupportBlockTwo position source
        exact ⟨k16Index (Fin.last 15), k16Index_last_mem, ⟨normalized⟩⟩

theorem fiveSupport_yields_representative_satisfying
    (ext : SemanticFiveSupport .uuu) :
    ∃ index : SelectedIndex,
      index ∈ uuuRepresentatives ∧
        ∃ branch : CanonicalBranch .uuu index.1 index.2,
          (finalValuation branch).satisfies_fmla
            (fmla .uuu index.1 index.2) := by
  obtain ⟨index, hindex, ⟨positioned⟩⟩ :=
    exists_positioned_representative ext
  obtain ⟨branch⟩ := exists_canonicalTransport positioned.toSemantic
  exact ⟨index, hindex, branch, canonicalBranch_satisfies_fmla branch⟩

/-! ## Exactness: the three K15 representatives do not merge -/

def k15DegreeSignature (x : Fin 15) : Nat × Nat × Nat :=
  (colorDegree (k15Template false) 0 x,
    colorDegree (k15Template false) 1 x,
    colorDegree (k15Template false) 2 x)

def k15OrbitClass : Fin 15 → Fin 3 := ![
  0, 1, 2, 0, 2, 0, 1, 0, 2, 1, 1, 1, 2, 2, 0
]

@[simp] theorem k15DegreeSignature_zero :
    k15DegreeSignature 0 = (4, 5, 5) := by decide

@[simp] theorem k15DegreeSignature_one :
    k15DegreeSignature 1 = (5, 5, 4) := by decide

@[simp] theorem k15DegreeSignature_two :
    k15DegreeSignature 2 = (5, 4, 5) := by decide

theorem k15OrbitClass_of_signature
    (left right : Fin 15)
    (h : k15DegreeSignature left = k15DegreeSignature right) :
    k15OrbitClass left = k15OrbitClass right := by
  revert h
  fin_cases left <;> fin_cases right <;> decide

theorem k15_colorDegree_preserved
    (e : Equiv.Perm (Fin 15))
    (hpreserves : ∀ left right, left ≠ right →
      k15Template false left right =
        k15Template false (e left) (e right))
    (x : Fin 15) (q : Fin 3) :
    colorDegree (k15Template false) q (e x) =
      colorDegree (k15Template false) q x := by
  rw [← colorDegree_relabelVertices (k15Template false) e q x]
  unfold colorDegree
  apply congrArg Finset.card
  ext y
  simp only [mem_colorNeighborhood, relabelVertices_apply]
  by_cases hyx : y = x
  · subst y
    simp
  · constructor
    · rintro ⟨hne, hcolor⟩
      exact ⟨hne, (hpreserves x y (Ne.symm hyx)).trans hcolor⟩
    · rintro ⟨hne, hcolor⟩
      exact ⟨hne, (hpreserves x y (Ne.symm hyx)).symm.trans hcolor⟩

theorem k15DegreeSignature_preserved
    (e : Equiv.Perm (Fin 15))
    (hpreserves : ∀ left right, left ≠ right →
      k15Template false left right =
        k15Template false (e left) (e right))
    (x : Fin 15) :
    k15DegreeSignature (e x) = k15DegreeSignature x := by
  apply Prod.ext
  · exact k15_colorDegree_preserved e hpreserves x 0
  · apply Prod.ext
    · exact k15_colorDegree_preserved e hpreserves x 1
    · exact k15_colorDegree_preserved e hpreserves x 2

theorem k15OrbitClass_preserved
    (e : Equiv.Perm (Fin 15))
    (hpreserves : ∀ left right, left ≠ right →
      k15Template false left right =
        k15Template false (e left) (e right))
    (x : Fin 15) :
    k15OrbitClass (e x) = k15OrbitClass x :=
  k15OrbitClass_of_signature _ _
    (k15DegreeSignature_preserved e hpreserves x)

theorem k15_representatives_eq_of_class_eq
    (left right : Fin 15)
    (hleft : left ∈ ({0, 1, 2} : Finset (Fin 15)))
    (hright : right ∈ ({0, 1, 2} : Finset (Fin 15)))
    (hclass : k15OrbitClass left = k15OrbitClass right) :
    left = right := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hleft hright
  rcases hleft with rfl | rfl | rfl <;>
    rcases hright with rfl | rfl | rfl <;>
      simp [k15OrbitClass] at hclass ⊢

theorem strong_automorphism_cannot_merge_k15_representatives
    (e : Equiv.Perm (Fin 15))
    (hpreserves : ∀ left right, left ≠ right →
      k15Template false left right =
        k15Template false (e left) (e right))
    (left right : Fin 15)
    (hleft : left ∈ ({0, 1, 2} : Finset (Fin 15)))
    (hright : right ∈ ({0, 1, 2} : Finset (Fin 15)))
    (hne : left ≠ right) :
    e left ≠ right := by
  intro hmap
  apply hne
  apply k15_representatives_eq_of_class_eq left right hleft hright
  have hclass := k15OrbitClass_preserved e hpreserves left
  simpa [hmap] using hclass.symm

/-! The only size-compatible nontrivial host-colour symmetry swaps colours
one and two together with the two `K15` blocks.  On either `K15`, its induced
local label permutation is the identity, so the weak template maps used by
the block swap are in fact strong colour-preserving automorphisms. -/

theorem labelPerm_zero_apply (q : Fin 3) : labelPerm 0 q = q := by
  apply SingleRootStarWitness61.canonicalPalette_injective 1
  have h := hostColorPerm_canonicalPalette (0 : Fin 3) q
  simp only [swapFirstTwoBlocks_zero] at h
  change hostColorPerm (canonicalPalette 2 q) =
    canonicalPalette 1 (labelPerm 0 q) at h
  have hleft :
      hostColorPerm (canonicalPalette 2 q) = canonicalPalette 1 q := by
    fin_cases q <;> decide
  rw [hleft] at h
  exact h.symm

theorem labelPerm_one_apply (q : Fin 3) : labelPerm 1 q = q := by
  apply SingleRootStarWitness61.canonicalPalette_injective 2
  have h := hostColorPerm_canonicalPalette (1 : Fin 3) q
  simp only [swapFirstTwoBlocks_one] at h
  change hostColorPerm (canonicalPalette 1 q) =
    canonicalPalette 2 (labelPerm 1 q) at h
  have hleft :
      hostColorPerm (canonicalPalette 1 q) = canonicalPalette 2 q := by
    fin_cases q <;> decide
  rw [hleft] at h
  exact h.symm

theorem labelPerm_zero_symm_apply (q : Fin 3) :
    (labelPerm 0).symm q = q := by
  apply (labelPerm 0).injective
  rw [Equiv.apply_symm_apply, labelPerm_zero_apply]

theorem labelPerm_one_symm_apply (q : Fin 3) :
    (labelPerm 1).symm q = q := by
  apply (labelPerm 1).injective
  rw [Equiv.apply_symm_apply, labelPerm_one_apply]

theorem localK15Zero_uuu_strong
    (left right : Fin 15) (hlr : left ≠ right) :
    k15Template false left right =
      k15Template false
        (localK15Zero .uuu left) (localK15Zero .uuu right) := by
  symm
  have h := localK15Zero_preserves .uuu left right hlr
  simpa [Kind.twisted, labelPerm_zero_symm_apply] using h

theorem localK15One_uuu_strong
    (left right : Fin 15) (hlr : left ≠ right) :
    k15Template false left right =
      k15Template false
        (localK15One .uuu left) (localK15One .uuu right) := by
  symm
  have h := localK15One_preserves .uuu left right hlr
  simpa [Kind.twisted, labelPerm_one_symm_apply] using h

theorem blockSwapZero_preserves_k15OrbitClass (x : Fin 15) :
    k15OrbitClass (localK15Zero .uuu x) = k15OrbitClass x :=
  k15OrbitClass_preserved (localK15Zero .uuu)
    localK15Zero_uuu_strong x

theorem blockSwapOne_preserves_k15OrbitClass (x : Fin 15) :
    k15OrbitClass (localK15One .uuu x) = k15OrbitClass x :=
  k15OrbitClass_preserved (localK15One .uuu)
    localK15One_uuu_strong x

theorem size_preserving_block_permutation_fixes_two
    (e : Equiv.Perm (Fin 3))
    (hsize : ∀ block, blockSize (e block) = blockSize block) :
    e 2 = 2 := by
  have h := hsize 2
  generalize heq : e 2 = image at h
  fin_cases image
  · simp [ProfileDTripleJoinReduction.blockSize] at h
  · simp [ProfileDTripleJoinReduction.blockSize] at h
  · rfl

theorem size_preserving_block_permutation_points
    (e : Equiv.Perm (Fin 3))
    (hsize : ∀ block, blockSize (e block) = blockSize block) :
    (e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 2) ∨
      (e 0 = 1 ∧ e 1 = 0 ∧ e 2 = 2) := by
  have htwo := size_preserving_block_permutation_fixes_two e hsize
  have hzeroOne : e 0 ≠ e 1 := e.injective.ne (by decide)
  have hzeroTwo : e 0 ≠ e 2 := e.injective.ne (by decide)
  have honeTwo : e 1 ≠ e 2 := e.injective.ne (by decide)
  generalize hzeroEq : e 0 = hzero
  generalize honeEq : e 1 = hone
  fin_cases hzero <;> fin_cases hone <;> simp_all

theorem size_preserving_block_permutation_eq_identity_or_swap
    (e : Equiv.Perm (Fin 3))
    (hsize : ∀ block, blockSize (e block) = blockSize block) :
    e = Equiv.refl (Fin 3) ∨ e = swapFirstTwoBlocks := by
  rcases size_preserving_block_permutation_points e hsize with
    ⟨hzero, hone, htwo⟩ | ⟨hzero, hone, htwo⟩
  · left
    apply Equiv.ext
    intro block
    fin_cases block
    · exact hzero
    · exact hone
    · exact htwo
  · right
    apply Equiv.ext
    intro block
    fin_cases block
    · simpa using hzero
    · simpa using hone
    · simpa using htwo

/-! ## Explicit generated orbit relation -/

inductive UUUSelectedLocation where
  | blockZero (position : Fin 15)
  | blockOne (position : Fin 15)
  | blockTwo (position : Fin 16)
  deriving DecidableEq

def UUUSelectedLocation.toIndex : UUUSelectedLocation → SelectedIndex
  | .blockZero position => k15Index position
  | .blockOne position => ⟨1, position⟩
  | .blockTwo position => k16Index position

inductive UUUOrbitInvariant where
  | k15 (positionClass : Fin 3)
  | k16
  deriving DecidableEq

def locationInvariant : UUUSelectedLocation → UUUOrbitInvariant
  | .blockZero position => .k15 (k15OrbitClass position)
  | .blockOne position => .k15 (k15OrbitClass position)
  | .blockTwo _ => .k16

/-! One generator is either a strong local template automorphism or the
restriction of the global equal-K15 block/host-colour swap.  The K16 weak
map is included explicitly; all of its positions have one orbit. -/
inductive UUUGeneratorStep :
    UUUSelectedLocation → UUUSelectedLocation → Prop where
  | strongZero (e : Equiv.Perm (Fin 15))
      (hpreserves : ∀ left right, left ≠ right →
        k15Template false left right =
          k15Template false (e left) (e right))
      (position : Fin 15) :
      UUUGeneratorStep (.blockZero position) (.blockZero (e position))
  | strongOne (e : Equiv.Perm (Fin 15))
      (hpreserves : ∀ left right, left ≠ right →
        k15Template false left right =
          k15Template false (e left) (e right))
      (position : Fin 15) :
      UUUGeneratorStep (.blockOne position) (.blockOne (e position))
  | strongTwo (e : Equiv.Perm (Fin 16))
      (_hpreserves : ∀ left right, left ≠ right →
        k16Template false left right =
          k16Template false (e left) (e right))
      (position : Fin 16) :
      UUUGeneratorStep (.blockTwo position) (.blockTwo (e position))
  | swapZero (position : Fin 15) :
      UUUGeneratorStep (.blockZero position)
        (.blockOne (localK15Zero .uuu position))
  | swapOne (position : Fin 15) :
      UUUGeneratorStep (.blockOne position)
        (.blockZero (localK15One .uuu position))
  | swapTwo (position : Fin 16) :
      UUUGeneratorStep (.blockTwo position)
        (.blockTwo (localK16Two .uuu position))

theorem generator_preserves_locationInvariant
    {source target : UUUSelectedLocation}
    (step : UUUGeneratorStep source target) :
    locationInvariant source = locationInvariant target := by
  cases step with
  | strongZero e hpreserves position =>
      exact congrArg UUUOrbitInvariant.k15
        (k15OrbitClass_preserved e hpreserves position).symm
  | strongOne e hpreserves position =>
      exact congrArg UUUOrbitInvariant.k15
        (k15OrbitClass_preserved e hpreserves position).symm
  | strongTwo => rfl
  | swapZero position =>
      exact congrArg UUUOrbitInvariant.k15
        (blockSwapZero_preserves_k15OrbitClass position).symm
  | swapOne position =>
      exact congrArg UUUOrbitInvariant.k15
        (blockSwapOne_preserves_k15OrbitClass position).symm
  | swapTwo => rfl

/-- Reflexive, symmetric, transitive closure of the certified generators. -/
inductive UUUOrbitRelated :
    UUUSelectedLocation → UUUSelectedLocation → Prop where
  | refl (location) : UUUOrbitRelated location location
  | step {source target} :
      UUUGeneratorStep source target → UUUOrbitRelated source target
  | symm {source target} :
      UUUOrbitRelated source target → UUUOrbitRelated target source
  | trans {left middle right} :
      UUUOrbitRelated left middle →
      UUUOrbitRelated middle right →
      UUUOrbitRelated left right

theorem orbitRelated_preserves_locationInvariant
    {source target : UUUSelectedLocation}
    (related : UUUOrbitRelated source target) :
    locationInvariant source = locationInvariant target := by
  induction related with
  | refl => rfl
  | step generator => exact generator_preserves_locationInvariant generator
  | symm _ ih => exact ih.symm
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight

def uuuRepresentativeLocations : List UUUSelectedLocation :=
  [.blockZero 0, .blockZero 1, .blockZero 2,
    .blockTwo (Fin.last 15)]

theorem representativeLocations_toIndex :
    uuuRepresentativeLocations.map UUUSelectedLocation.toIndex =
      uuuRepresentatives := by
  rfl

theorem representativeLocationInvariants_nodup :
    (uuuRepresentativeLocations.map locationInvariant).Nodup := by
  decide

theorem distinct_representativeLocations_not_related
    (left right : UUUSelectedLocation)
    (hleft : left ∈ uuuRepresentativeLocations)
    (hright : right ∈ uuuRepresentativeLocations)
    (hne : left ≠ right) :
    ¬UUUOrbitRelated left right := by
  intro hrelated
  have hinvariant := orbitRelated_preserves_locationInvariant hrelated
  simp [uuuRepresentativeLocations] at hleft hright
  rcases hleft with rfl | rfl | rfl | rfl <;>
    rcases hright with rfl | rfl | rfl | rfl <;>
      simp [locationInvariant, k15OrbitClass] at hinvariant hne

/-! Consequently the four displayed indices are an exact minimal cover for
the certified semantic symmetry group: three pairwise distinct orbits among
the equal `K15` blocks, plus the size-separated `K16` orbit. -/

theorem uuu_minimal_orbit_count : uuuRepresentatives.length = 4 :=
  uuuRepresentatives_length

#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.exists_positioned_representative
#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.fiveSupport_yields_representative_satisfying
#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.strong_automorphism_cannot_merge_k15_representatives
#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.blockSwapZero_preserves_k15OrbitClass
#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.size_preserving_block_permutation_fixes_two
#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.size_preserving_block_permutation_eq_identity_or_swap
#print axioms R4333.ProfileDUUUFiveSupportPositionSymmetry.distinct_representativeLocations_not_related

end ProfileDUUUFiveSupportPositionSymmetry
end R4333
