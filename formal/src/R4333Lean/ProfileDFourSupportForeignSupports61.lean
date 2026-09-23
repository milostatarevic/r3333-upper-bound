import R4333Lean.ProfileDFourSupportInside61
import R4333Lean.ProfileDHighOwnForeignC5Skeleton61

/-!
# Exact foreign supports in the profile-D four-support branch

For a `FourSupportFiveRowExtension`, the selected tail endpoint has exact
own-colour degree ten.  Its own block contributes no neighbour in that colour,
while each foreign block contributes at most five by the same two-colour
triangle-free argument used in the five-support branch.  Consequently both
foreign supports have cardinality exactly five.

This module is semantic only.  It contains no catalogue enumeration or finite
refutation claim.
-/

namespace R4333
namespace ProfileDFourSupportForeignSupports61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FourSupportExtension :=
  ProfileDHighOwnFiveRowSplit61.FourSupportFiveRowExtension

abbrev firstForeignBlock :=
  ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock

abbrev secondForeignBlock :=
  ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock

/-- The selected endpoint's own-colour neighbours in one tail block. -/
def foreignOwnSupport {kind : Kind} (ext : FourSupportExtension kind)
    (target : Fin 3) : Finset (Fin (blockSize target)) :=
  Finset.univ.filter fun position =>
    ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex ext.block ext.position.val)
        (blockVertex target position.val) = blockRootColor ext.block

@[simp] theorem mem_foreignOwnSupport {kind : Kind}
    (ext : FourSupportExtension kind) (target : Fin 3)
    (position : Fin (blockSize target)) :
    position ∈ foreignOwnSupport ext target ↔
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex ext.block ext.position.val)
          (blockVertex target position.val) = blockRootColor ext.block := by
  simp [foreignOwnSupport]

/-- Two own-colour neighbours of the selected endpoint cannot have a mutual
edge in that same colour. -/
theorem foreignOwnSupport_edge_ne_own {kind : Kind}
    (ext : FourSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block)
    (left : Fin (blockSize target))
    (hleft : left ∈ foreignOwnSupport ext target)
    (right : Fin (blockSize target))
    (hright : right ∈ foreignOwnSupport ext target)
    (hlr : left ≠ right) :
    ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
        left right ≠ blockRootColor ext.block := by
  let tail := ext.toDegreeFlooredFiveExtension.toFiveExtension.tail
  have hsourceLeft :
      blockVertex ext.block ext.position.val ≠
        blockVertex target left.val :=
    blockVertex_ne_of_block_ne ext.block target htarget.symm
      ext.position.isLt left.isLt
  have hsourceRight :
      blockVertex ext.block ext.position.val ≠
        blockVertex target right.val :=
    blockVertex_ne_of_block_ne ext.block target htarget.symm
      ext.position.isLt right.isLt
  have hleftRight :
      blockVertex target left.val ≠ blockVertex target right.val :=
    (blockVertex_fixed_injective target).ne hlr
  have hleftColor := (mem_foreignOwnSupport ext target left).mp hleft
  have hrightColor := (mem_foreignOwnSupport ext target right).mp hright
  intro hedge
  apply tail.noMono
    (blockVertex ext.block ext.position.val)
    (blockVertex target left.val) (blockVertex target right.val)
  · exact ⟨hsourceLeft, hsourceRight, hleftRight⟩
  · exact ⟨hleftColor.trans hrightColor.symm,
      hrightColor.trans hedge.symm⟩

/-- Internal edges induced by one foreign support use only zero and the
third nonzero root colour. -/
theorem foreignOwnSupport_edge_color_cases {kind : Kind}
    (ext : FourSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block)
    (left : Fin (blockSize target))
    (hleft : left ∈ foreignOwnSupport ext target)
    (right : Fin (blockSize target))
    (hright : right ∈ foreignOwnSupport ext target)
    (hlr : left ≠ right) :
    ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
          ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
          left right = 0 ∨
      ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
          ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
          left right =
        ProfileDHighOwnForeignC5Skeleton61.thirdBlockRootColor
          ext.block target := by
  have hnotOwn := foreignOwnSupport_edge_ne_own
    ext target htarget left hleft right hright hlr
  have hnotTarget :=
    ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring_ne_root
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
      left right hlr
  generalize hcolor :
      ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target
        left right = color
  generalize hsource : ext.block = source at htarget hnotOwn hcolor ⊢
  fin_cases source <;> fin_cases target <;> fin_cases color <;>
    simp_all [blockRootColor,
      ProfileDHighOwnForeignC5Skeleton61.thirdBlockRootColor]

/-- The triangle-free two-colour support cap in either foreign block. -/
theorem foreignOwnSupport_card_le_five {kind : Kind}
    (ext : FourSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block) :
    (foreignOwnSupport ext target).card ≤ 5 := by
  apply twoColorFinset_card_le_five
    (ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target)
    (ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring_noMono
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail target)
    (p := (0 : Fin 4))
    (q := ProfileDHighOwnForeignC5Skeleton61.thirdBlockRootColor
      ext.block target)
    (foreignOwnSupport ext target)
  intro left hleft right hright hlr
  exact foreignOwnSupport_edge_color_cases
    ext target htarget left hleft right hright hlr

/-! ## Exact partition of the selected endpoint's tail own-degree -/

def selectedEndpointOwnRow {kind : Kind}
    (ext : FourSupportExtension kind) : TailVertex → Fin 4 :=
  fun y =>
    if y = blockVertex ext.block ext.position.val then 0
    else ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex ext.block ext.position.val) y

theorem selectedEndpointOwnRow_support_eq_neighborhood {kind : Kind}
    (ext : FourSupportExtension kind) :
    rowColorSupport (selectedEndpointOwnRow ext) (blockRootColor ext.block) =
      colorNeighborhood
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) := by
  ext y
  simp only [mem_rowColorSupport, mem_colorNeighborhood]
  constructor
  · intro hy
    have hyne : y ≠ blockVertex ext.block ext.position.val := by
      intro heq
      subst y
      have hzero : (0 : Fin 4) = blockRootColor ext.block := by
        simpa [selectedEndpointOwnRow] using hy
      exact (blockRootColor_ne_zero ext.block) hzero.symm
    exact ⟨hyne, by simpa [selectedEndpointOwnRow, hyne] using hy⟩
  · rintro ⟨hyne, hycolor⟩
    simpa [selectedEndpointOwnRow, hyne] using hycolor

def endpointBlockSupport {kind : Kind} (ext : FourSupportExtension kind)
    (target : Fin 3) : Finset (Fin (blockSize target)) :=
  rowColorSupport
    (fun position => selectedEndpointOwnRow ext
      (blockVertex target position.val))
    (blockRootColor ext.block)

theorem endpointBlockSupport_eq_foreignOwnSupport {kind : Kind}
    (ext : FourSupportExtension kind) (target : Fin 3)
    (htarget : target ≠ ext.block) :
    endpointBlockSupport ext target = foreignOwnSupport ext target := by
  ext position
  have hvertices :
      blockVertex target position.val ≠
        blockVertex ext.block ext.position.val := by
    exact (blockVertex_ne_of_block_ne ext.block target htarget.symm
      ext.position.isLt position.isLt).symm
  simp [endpointBlockSupport, foreignOwnSupport,
    selectedEndpointOwnRow, hvertices]

/-- The selected endpoint's own block contributes no neighbour in its own
root colour. -/
theorem endpointBlockSupport_own_card_eq_zero {kind : Kind}
    (ext : FourSupportExtension kind) :
    (endpointBlockSupport ext ext.block).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro position hposition
  have hcolor := (mem_rowColorSupport _ _ position).mp hposition
  by_cases hsame : position = ext.position
  · subst position
    have hzero : (0 : Fin 4) = blockRootColor ext.block := by
      simpa [endpointBlockSupport, selectedEndpointOwnRow] using hcolor
    exact (blockRootColor_ne_zero ext.block) hzero.symm
  · have hne :
        blockVertex ext.block position.val ≠
          blockVertex ext.block ext.position.val :=
      (blockVertex_fixed_injective ext.block).ne hsame
    have hforbidden :=
      ProfileDHighOwnForeignC5Skeleton61.tailBlockColoring_ne_root
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail ext.block
        position ext.position hsame
    apply hforbidden
    change ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex ext.block position.val)
      (blockVertex ext.block ext.position.val) = blockRootColor ext.block
    rw [ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring.color_symm]
    simpa [endpointBlockSupport, selectedEndpointOwnRow, hne] using hcolor

theorem selectedTailOwnDegree_eq_threeBlockSum {kind : Kind}
    (ext : FourSupportExtension kind) :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (endpointBlockSupport ext 0).card +
        ((endpointBlockSupport ext 1).card +
          (endpointBlockSupport ext 2).card) := by
  rw [show colorDegree
      ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (rowColorSupport (selectedEndpointOwnRow ext)
        (blockRootColor ext.block)).card by
      rw [selectedEndpointOwnRow_support_eq_neighborhood]
      rfl]
  have hsum := support_card_eq_block_sum
    (selectedEndpointOwnRow ext) (blockRootColor ext.block)
  have hzero :
      ProfileDBlockZeroSupport.k15Row (selectedEndpointOwnRow ext) 0 =
        fun position : Fin 15 => selectedEndpointOwnRow ext
          (blockVertex 0 position.val) := by
    rfl
  have hone :
      ProfileDBlockZeroSupport.k15Row (selectedEndpointOwnRow ext) 1 =
        fun position : Fin 15 => selectedEndpointOwnRow ext
          (blockVertex 1 position.val) := by
    rfl
  have htwo :
      ProfileDBlockZeroSupport.k16Row (selectedEndpointOwnRow ext) =
        fun position : Fin 16 => selectedEndpointOwnRow ext
          (blockVertex 2 position.val) := by
    rfl
  rw [hzero, hone, htwo] at hsum
  simpa [endpointBlockSupport,
    ProfileDTripleJoinReduction.blockSize] using hsum

theorem selectedTailOwnDegree_eq_foreignSum {kind : Kind}
    (ext : FourSupportExtension kind) :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (foreignOwnSupport ext (firstForeignBlock ext.block)).card +
        (foreignOwnSupport ext (secondForeignBlock ext.block)).card := by
  have hall := selectedTailOwnDegree_eq_threeBlockSum ext
  have hown := endpointBlockSupport_own_card_eq_zero ext
  have hfirst := endpointBlockSupport_eq_foreignOwnSupport ext
    (firstForeignBlock ext.block)
    (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne ext.block)
  have hsecond := endpointBlockSupport_eq_foreignOwnSupport ext
    (secondForeignBlock ext.block)
    (ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock_ne ext.block)
  calc
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) =
      (endpointBlockSupport ext 0).card +
        ((endpointBlockSupport ext 1).card +
          (endpointBlockSupport ext 2).card) := hall
    _ = (endpointBlockSupport ext ext.block).card +
        ((endpointBlockSupport ext (firstForeignBlock ext.block)).card +
          (endpointBlockSupport ext
            (secondForeignBlock ext.block)).card) :=
      ProfileDHighOwnForeignC5Skeleton61.threeBlockSum_eq_source_foreignSum
        (fun target => (endpointBlockSupport ext target).card) ext.block
    _ = (foreignOwnSupport ext (firstForeignBlock ext.block)).card +
        (foreignOwnSupport ext (secondForeignBlock ext.block)).card := by
      rw [hown, hfirst, hsecond]
      omega

/-- The first foreign support in the deterministic block order. -/
def firstForeignOwnSupport {kind : Kind} (ext : FourSupportExtension kind) :
    Finset (Fin (blockSize (firstForeignBlock ext.block))) :=
  foreignOwnSupport ext (firstForeignBlock ext.block)

/-- The second foreign support in the deterministic block order. -/
def secondForeignOwnSupport {kind : Kind} (ext : FourSupportExtension kind) :
    Finset (Fin (blockSize (secondForeignBlock ext.block))) :=
  foreignOwnSupport ext (secondForeignBlock ext.block)

/-- Exact saturation of both foreign supports. -/
theorem foreignOwnSupport_cards_eq_five {kind : Kind}
    (ext : FourSupportExtension kind) :
    (firstForeignOwnSupport ext).card = 5 ∧
      (secondForeignOwnSupport ext).card = 5 := by
  have hfirstCap := foreignOwnSupport_card_le_five ext
    (firstForeignBlock ext.block)
    (ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock_ne ext.block)
  have hsecondCap := foreignOwnSupport_card_le_five ext
    (secondForeignBlock ext.block)
    (ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock_ne ext.block)
  have hsum := selectedTailOwnDegree_eq_foreignSum ext
  have hdegree := ext.tailOwnDegreeEqTen
  change
    (foreignOwnSupport ext (firstForeignBlock ext.block)).card = 5 ∧
      (foreignOwnSupport ext (secondForeignBlock ext.block)).card = 5
  omega

theorem firstForeignOwnSupport_card_eq_five {kind : Kind}
    (ext : FourSupportExtension kind) :
    (firstForeignOwnSupport ext).card = 5 :=
  (foreignOwnSupport_cards_eq_five ext).1

theorem secondForeignOwnSupport_card_eq_five {kind : Kind}
    (ext : FourSupportExtension kind) :
    (secondForeignOwnSupport ext).card = 5 :=
  (foreignOwnSupport_cards_eq_five ext).2

#print axioms foreignOwnSupport_card_le_five
#print axioms endpointBlockSupport_own_card_eq_zero
#print axioms selectedTailOwnDegree_eq_foreignSum
#print axioms foreignOwnSupport_cards_eq_five
#print axioms firstForeignOwnSupport_card_eq_five
#print axioms secondForeignOwnSupport_card_eq_five

end ProfileDFourSupportForeignSupports61
end R4333
