import R4333Lean.ProfileDColumnOwnColorIncidence61

/-!
# Exact cap on profile-D free own-colour columns

Fix a tail vertex in one of the three critical blocks and look at the free
vertices joined to it in that block's root colour.  Two such free vertices
cannot have their mutual edge in colour zero (the free block is
root-forbidden) or in the tail vertex's block colour (row-pair
compatibility).  The induced support is therefore two-coloured and has order
at most five.

Together with the two foreign-block caps, a tail vertex whose own-colour
degree in the non-root `K60` is at least fourteen has four or five such free
neighbours.  This is the column form needed by the high-incidence root
normalization.
-/

namespace R4333
namespace ProfileDFreeOwnColorColumnCap

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDRowSupportBounds61
open ProfileDColumnOwnColorIncidence61

set_option maxRecDepth 1000000

theorem freeOwnColorSupport_avoids_ownColor {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block)) (a b : FreeVertex)
    (ha : a ∈ freeOwnColorSupport ext block i)
    (hb : b ∈ freeOwnColorSupport ext block i) (hab : a ≠ b) :
    ext.inside a b ≠ blockRootColor block := by
  have haColor :
      ext.rows a (blockVertex block i.val) = blockRootColor block :=
    (mem_rowColorSupport _ _ _).mp (by
      simpa [freeOwnColorSupport] using ha)
  have hbColor :
      ext.rows b (blockVertex block i.val) = blockRootColor block :=
    (mem_rowColorSupport _ _ _).mp (by
      simpa [freeOwnColorSupport] using hb)
  intro hedge
  apply ext.rowsPairCompatible a b hab (blockVertex block i.val)
  exact ⟨hedge.trans haColor.symm, haColor.trans hbColor.symm⟩

/-- Every free own-colour column has order at most five. -/
theorem freeOwnColorSupport_le_five {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block)) :
    (freeOwnColorSupport ext block i).card ≤ 5 := by
  let S := freeOwnColorSupport ext block i
  change S.card ≤ 5
  fin_cases block
  · apply twoColorFinset_card_le_five ext.inside ext.insideNoMono
      (p := (2 : Fin 4)) (q := (3 : Fin 4)) S
    intro a ha b hb hab
    have hzero := ext.insideRootForbidden a b hab
    have hone := freeOwnColorSupport_avoids_ownColor ext 0 i a b ha hb hab
    generalize hcolor : ext.inside a b = color
    fin_cases color <;> simp_all [blockRootColor]
  · apply twoColorFinset_card_le_five ext.inside ext.insideNoMono
      (p := (1 : Fin 4)) (q := (3 : Fin 4)) S
    intro a ha b hb hab
    have hzero := ext.insideRootForbidden a b hab
    have htwo := freeOwnColorSupport_avoids_ownColor ext 1 i a b ha hb hab
    generalize hcolor : ext.inside a b = color
    fin_cases color <;> simp_all [blockRootColor]
  · apply twoColorFinset_card_le_five ext.inside ext.insideNoMono
      (p := (1 : Fin 4)) (q := (2 : Fin 4)) S
    intro a ha b hb hab
    have hzero := ext.insideRootForbidden a b hab
    have hthree := freeOwnColorSupport_avoids_ownColor ext 2 i a b ha hb hab
    generalize hcolor : ext.inside a b = color
    fin_cases color <;> simp_all [blockRootColor]

/-- A tail vertex has at most ten own-colour neighbours inside the other two
tail blocks; its own block contributes none. -/
theorem tail_ownColorDegree_le_ten {kind : Kind}
    (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block)) :
    colorDegree ext.tail.coloring (blockRootColor block)
      (blockVertex block i.val) ≤ 10 := by
  have htailDegree :
      colorDegree ext.tail.coloring (blockRootColor block)
          (blockVertex block i.val) =
        (rowColorSupport (ownNeighborRow ext block i)
          (blockRootColor block)).card := by
    rw [ownNeighborRow_support_eq_colorNeighborhood]
    rfl
  rw [htailDegree, support_card_eq_block_sum]
  fin_cases block
  · have hown := ownBlock_support_eq_zero ext 0 i
    have hother1 := k15_otherBlock_support_le_five ext 0 i 1 (by decide)
    have hother2 := k16_otherBlock_support_le_five ext 0 i (by decide)
    have hrowEq :
        ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 0 =
          fun j : Fin 15 => ownNeighborRow ext 0 i (blockVertex 0 j.val) := by
      funext j
      rfl
    have hown' : (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 0)
          (blockRootColor 0)).card = 0 := by
      rw [hrowEq]
      exact hown
    change (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 0)
          (blockRootColor 0)).card +
      ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 0 i) 1)
          (blockRootColor 0)).card +
       (rowColorSupport
        (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 0 i))
          (blockRootColor 0)).card) ≤ 10
    omega
  · have hother0 := k15_otherBlock_support_le_five ext 1 i 0 (by decide)
    have hown := ownBlock_support_eq_zero ext 1 i
    have hother2 := k16_otherBlock_support_le_five ext 1 i (by decide)
    have hrowEq :
        ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 1 =
          fun j : Fin 15 => ownNeighborRow ext 1 i (blockVertex 1 j.val) := by
      funext j
      rfl
    have hown' : (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 1)
          (blockRootColor 1)).card = 0 := by
      rw [hrowEq]
      exact hown
    change (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 0)
          (blockRootColor 1)).card +
      ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 1 i) 1)
          (blockRootColor 1)).card +
       (rowColorSupport
        (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 1 i))
          (blockRootColor 1)).card) ≤ 10
    omega
  · have hother0 := k15_otherBlock_support_le_five ext 2 i 0 (by decide)
    have hother1 := k15_otherBlock_support_le_five ext 2 i 1 (by decide)
    have hown := ownBlock_support_eq_zero ext 2 i
    have hrowEq :
        ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 2 i) =
          fun j : Fin 16 => ownNeighborRow ext 2 i (blockVertex 2 j.val) := by
      rfl
    have hown' : (rowColorSupport
        (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 2 i))
          (blockRootColor 2)).card = 0 := by
      rw [hrowEq]
      exact hown
    change (rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 2 i) 0)
          (blockRootColor 2)).card +
      ((rowColorSupport
        (ProfileDBlockZeroSupport.k15Row (ownNeighborRow ext 2 i) 1)
          (blockRootColor 2)).card +
       (rowColorSupport
        (ProfileDBlockZeroSupport.k16Row (ownNeighborRow ext 2 i))
          (blockRootColor 2)).card) ≤ 10
    omega

theorem freeOwnColorSupport_ge_four_of_fullDegree_ge_fourteen
    {kind : Kind} (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block i.val))) :
    4 ≤ (freeOwnColorSupport ext block i).card := by
  change 14 ≤ colorDegree
    (joinColoring ext.inside ext.tail.coloring ext.rows)
      (blockRootColor block) (.inr (blockVertex block i.val)) at hdegree
  rw [colorDegree_joinColoring_inr] at hdegree
  have htail := tail_ownColorDegree_le_ten ext block i
  change 4 ≤ (rowColorSupport
    (fun a => ext.rows a (blockVertex block i.val))
      (blockRootColor block)).card
  omega

theorem freeOwnColorSupport_between_four_and_five_of_fullDegree_ge_fourteen
    {kind : Kind} (ext : Extension kind) (block : Fin 3)
    (i : Fin (blockSize block))
    (hdegree : 14 ≤ colorDegree (fullJoinedColoring ext)
      (blockRootColor block) (.inr (blockVertex block i.val))) :
    4 ≤ (freeOwnColorSupport ext block i).card ∧
      (freeOwnColorSupport ext block i).card ≤ 5 :=
  ⟨freeOwnColorSupport_ge_four_of_fullDegree_ge_fourteen
      ext block i hdegree,
    freeOwnColorSupport_le_five ext block i⟩

#print axioms R4333.ProfileDFreeOwnColorColumnCap.freeOwnColorSupport_le_five
#print axioms R4333.ProfileDFreeOwnColorColumnCap.tail_ownColorDegree_le_ten
#print axioms R4333.ProfileDFreeOwnColorColumnCap.freeOwnColorSupport_between_four_and_five_of_fullDegree_ge_fourteen

end ProfileDFreeOwnColorColumnCap
end R4333
