import R4333Lean.ColoringJoinRows

/-!
# Cardinal support obstruction for compatible extension rows

The colour on an edge between two new vertices is unavailable as soon as
their supports in that colour overlap.  This file records the finite
pigeonhole form used by the Chung-tail row analysis: on a sixteen-vertex
block, two rows which each use a colour at least eleven times must overlap.

The result is entirely semantic.  It has no dependence on a SAT encoding or
on the Chung construction.
-/

namespace R4333
namespace ColoringJoinRows

/-- The finite set of core coordinates on which a row takes colour `q`. -/
def rowColorSupport {B C : Type*} [Fintype B] [DecidableEq C]
    (row : B → C) (q : C) : Finset B :=
  Finset.univ.filter fun x ↦ row x = q

@[simp] theorem mem_rowColorSupport {B C : Type*}
    [Fintype B] [DecidableEq C] (row : B → C) (q : C) (x : B) :
    x ∈ rowColorSupport row q ↔ row x = q := by
  simp [rowColorSupport]

/-- If two colour supports together are larger than the core, they overlap;
equivalently, that colour is not available on the edge between the rows. -/
theorem not_mem_availableColors_of_card_lt_support_sum
    {B C : Type*} [Fintype B] [DecidableEq B] [DecidableEq C]
    (left right : B → C) (q : C)
    (hlarge : Fintype.card B <
      (rowColorSupport left q).card + (rowColorSupport right q).card) :
    q ∉ availableColors left right := by
  intro havailable
  have hdisjoint :
      Disjoint (rowColorSupport left q) (rowColorSupport right q) := by
    rw [Finset.disjoint_left]
    intro x hleft hright
    exact havailable x
      ⟨(mem_rowColorSupport left q x).mp hleft,
       (mem_rowColorSupport right q x).mp hright⟩
  have hunionBound :
      ((rowColorSupport left q) ∪ (rowColorSupport right q)).card ≤
        Fintype.card B := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ
        ((rowColorSupport left q) ∪ (rowColorSupport right q)))
  rw [Finset.card_union_of_disjoint hdisjoint] at hunionBound
  omega

/-- The numerical instance used by a canonical K16 layer.  Eleven is the
natural bound obtained when the complementary colour support has size at
most five, the independence number of a critical three-colour K16. -/
theorem not_mem_availableColors_of_eleven_on_sixteen
    {B C : Type*} [Fintype B] [DecidableEq B] [DecidableEq C]
    (left right : B → C) (q : C)
    (hcard : Fintype.card B = 16)
    (hleft : 11 ≤ (rowColorSupport left q).card)
    (hright : 11 ≤ (rowColorSupport right q).card) :
    q ∉ availableColors left right := by
  apply not_mem_availableColors_of_card_lt_support_sum
  omega

#print axioms R4333.ColoringJoinRows.not_mem_availableColors_of_card_lt_support_sum
#print axioms R4333.ColoringJoinRows.not_mem_availableColors_of_eleven_on_sixteen

end ColoringJoinRows
end R4333
