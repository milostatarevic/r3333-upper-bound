import R4333Lean.CanonicalStarOwnColorDegree
import R4333Lean.ColoringJoinRowSupport
import R4333Lean.ProfileDFourRowDegreeCap
import R4333Lean.ProfileDFourRowKindSymmetry

/-!
# Degree floors retained by the profile-D four-row restriction

The bare profile-D four-row object is a good colouring on only fifty
non-root vertices.  It therefore forgets lower degree information which was
present before the restriction from the full canonical `K61` star.

This file retains that information exactly where it matters.  Every vertex
of the free `K14` has, into the `K15 + K15 + K16` tail,

* between eleven and fifteen edges of colour zero; and
* between seven and thirteen edges of each of colours one, two, and three.

The proof is elementary but genuinely global.  In the non-root `K60`, the
four colour degrees sum to 59.  The omitted root gives the colour-zero cap
15, while all other colour degrees are at most 16, so every nonzero degree
is at least 12.  Inside the free `K14`, every nonzero colour degree lies
between three and five: its edges use only three colours, and a colour
neighbourhood is two-coloured and hence has order at most five.  Subtracting
the inside contribution leaves the displayed tail-row interval.

The resulting `DegreeFlooredFourExtension` is a strictly stronger semantic
certificate target than `FourExtension`.  Every full profile-D star still
supplies one.  No obstruction to these objects is asserted here.
-/

namespace R4333
namespace ProfileDRowSupportBounds61

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDFourRowDegreeCap
open ProfileDFourRowKindSymmetry
open SingleRootStarCNF

set_option maxRecDepth 1000000

/-! ## Generic degree decomposition for a joined colouring -/

/-- At a vertex on the left of a join, a colour degree is the inside degree
plus the cardinality of that colour's cross-row support. -/
theorem colorDegree_joinColoring_inl
    {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (q : C) (a : A) :
    colorDegree (joinColoring inside base rows) q (.inl a) =
      colorDegree inside q a + (rowColorSupport (rows a) q).card := by
  classical
  have hneighborhood :
      colorNeighborhood (joinColoring inside base rows) q (.inl a) =
        (colorNeighborhood inside q a).disjSum
          (rowColorSupport (rows a) q) := by
    ext x
    cases x with
    | inl x =>
        simp [colorNeighborhood, rowColorSupport, joinColoring]
    | inr x =>
        simp [colorNeighborhood, rowColorSupport, joinColoring]
  rw [colorDegree, hneighborhood, Finset.card_disjSum]
  rfl

/-- The four colour supports of an arbitrary finite row partition its
domain. -/
theorem rowColorSupport_sum_fin4
    {B : Type*} [Fintype B] [DecidableEq B]
    (row : B → Fin 4) :
    (rowColorSupport row 0).card +
      ((rowColorSupport row 1).card +
        ((rowColorSupport row 2).card +
          (rowColorSupport row 3).card)) = Fintype.card B := by
  classical
  have hpartition :
      (Finset.univ : Finset B).card =
        ∑ q ∈ (Finset.univ : Finset (Fin 4)),
          ((Finset.univ : Finset B).filter fun x ↦ row x = q).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  simpa [rowColorSupport, Fin.sum_univ_succ] using hpartition.symm

/-! ## Full fourteen-row arithmetic -/

abbrev FullJoinedVertex := Sum FreeVertex TailVertex

def fullJoinedColoring {kind : Kind} (ext : Extension kind) :
    EdgeColoring FullJoinedVertex (Fin 4) :=
  joinColoring ext.inside ext.tail.coloring ext.rows

def fullJoinedRootColor : FullJoinedVertex → Fin 4
  | .inl _ => 0
  | .inr x => tailRootColor x

theorem fullJoinedColoring_noMono {kind : Kind} (ext : Extension kind) :
    NoMonochromaticTriangle (fullJoinedColoring ext) := by
  exact (noMono_joinColoring_iff
    ext.inside ext.tail.coloring ext.rows).2
      ⟨ext.insideNoMono, ext.tail.noMono,
        ext.rowsAdmissible, ext.rowsPairCompatible⟩

/-- The omitted root can be restored to the full fourteen-row extension. -/
theorem fullJoinedColoring_rootForbidden {kind : Kind}
    (ext : Extension kind) (u v : FullJoinedVertex) (huv : u ≠ v)
    (hsame : fullJoinedRootColor u = fullJoinedRootColor v) :
    fullJoinedColoring ext u v ≠ fullJoinedRootColor u := by
  let small : FourExtension kind := restrictFour ext
  cases u with
  | inl a =>
      cases v with
      | inl b =>
          exact ext.insideRootForbidden a b
            (fun h ↦ huv (congrArg Sum.inl h))
      | inr y =>
          exfalso
          exact tailRootColor_ne_zero y hsame.symm
  | inr x =>
      cases v with
      | inl b =>
          exfalso
          exact tailRootColor_ne_zero x hsame
      | inr y =>
          exact tail_rootForbidden small x y
            (fun h ↦ huv (congrArg Sum.inr h)) hsame

theorem fullJoinedColorDegree_le_sixteen {kind : Kind}
    (ext : Extension kind) (q : Fin 4) (v : FullJoinedVertex) :
    colorDegree (fullJoinedColoring ext) q v ≤ 16 := by
  fin_cases q
  · exact colorDegree_le_sixteen_of_four (fullJoinedColoring ext)
      (fullJoinedColoring_noMono ext) 0 1 2 3
        (by intro z; fin_cases z <;> simp) v
  · exact colorDegree_le_sixteen_of_four (fullJoinedColoring ext)
      (fullJoinedColoring_noMono ext) 1 0 2 3
        (by intro z; fin_cases z <;> simp) v
  · exact colorDegree_le_sixteen_of_four (fullJoinedColoring ext)
      (fullJoinedColoring_noMono ext) 2 0 1 3
        (by intro z; fin_cases z <;> simp) v
  · exact colorDegree_le_sixteen_of_four (fullJoinedColoring ext)
      (fullJoinedColoring_noMono ext) 3 0 1 2
        (by intro z; fin_cases z <;> simp) v

theorem fullJoinedOwnDegree_le_fifteen {kind : Kind}
    (ext : Extension kind) (v : FullJoinedVertex) :
    colorDegree (fullJoinedColoring ext) (fullJoinedRootColor v) v ≤ 15 :=
  colorDegree_rootColor_le_fifteen
    (fullJoinedColoring ext) fullJoinedRootColor
    (fullJoinedColoring_noMono ext)
    (fullJoinedColoring_rootForbidden ext) v

/-- All four non-root degrees at a free vertex sum to 59. -/
theorem free_degree_sum_fiftyNine {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) :
    colorDegree (fullJoinedColoring ext) 0 (.inl a) +
      (colorDegree (fullJoinedColoring ext) 1 (.inl a) +
        (colorDegree (fullJoinedColoring ext) 2 (.inl a) +
          colorDegree (fullJoinedColoring ext) 3 (.inl a))) = 59 := by
  have hsum := sum_colorDegree_eq_card_sub_one
    (fullJoinedColoring ext) (.inl a)
  simpa [Fin.sum_univ_succ, FullJoinedVertex, FreeVertex, TailVertex] using hsum

/-- The colour-zero degree of a free vertex is at least eleven. -/
theorem free_zero_degree_ge_eleven {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) :
    11 ≤ colorDegree (fullJoinedColoring ext) 0 (.inl a) := by
  have hsum := free_degree_sum_fiftyNine ext a
  have h1 := fullJoinedColorDegree_le_sixteen ext 1 (.inl a)
  have h2 := fullJoinedColorDegree_le_sixteen ext 2 (.inl a)
  have h3 := fullJoinedColorDegree_le_sixteen ext 3 (.inl a)
  omega

/-- The tighter colour-zero cap forces every nonzero degree to be at least
twelve in the non-root `K60`. -/
theorem free_nonzero_degree_ge_twelve {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (q : Fin 4) (hq : q ≠ 0) :
    12 ≤ colorDegree (fullJoinedColoring ext) q (.inl a) := by
  have hsum := free_degree_sum_fiftyNine ext a
  have h0 : colorDegree (fullJoinedColoring ext) 0 (.inl a) ≤ 15 := by
    simpa [fullJoinedRootColor] using
      fullJoinedOwnDegree_le_fifteen ext (.inl a)
  have h1 := fullJoinedColorDegree_le_sixteen ext 1 (.inl a)
  have h2 := fullJoinedColorDegree_le_sixteen ext 2 (.inl a)
  have h3 := fullJoinedColorDegree_le_sixteen ext 3 (.inl a)
  fin_cases q <;> simp_all <;> omega

/-! ## Generic root-forbidden K14 arithmetic -/

/-- If colour zero is forbidden on all distinct internal edges, every
internal colour-zero degree vanishes.  This generic form is reusable by the
profile-C free K14. -/
theorem rootForbidden_zero_degree_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (inside : EdgeColoring V (Fin 4))
    (hroot : ∀ x y : V, x ≠ y → inside x y ≠ 0) (a : V) :
    colorDegree inside 0 a = 0 := by
  rw [colorDegree, Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    have hx' := (mem_colorNeighborhood inside 0 a x).mp hx
    exact (hroot a x hx'.1.symm hx'.2).elim
  · intro hx
    simp at hx

/-- In any triangle-free four-colouring whose distinct edges avoid zero,
every nonzero colour degree is at most five.  Its colour neighbourhood is
explicitly two-coloured, so this is exactly `R(3,3) ≤ 6`. -/
theorem rootForbidden_nonzero_degree_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (inside : EdgeColoring V (Fin 4))
    (hnoMono : NoMonochromaticTriangle inside)
    (hroot : ∀ x y : V, x ≠ y → inside x y ≠ 0)
    (a : V) (q : Fin 4) (hq : q ≠ 0) :
    colorDegree inside q a ≤ 5 := by
  let S := colorNeighborhood inside q a
  have havoid : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y →
      inside x y ≠ q := by
    intro x hx y hy hxy
    exact neighborhood_avoids_own_color inside hnoMono hx hy hxy
  change S.card ≤ 5
  fin_cases q
  · exact (hq rfl).elim
  · apply twoColorFinset_card_le_five inside hnoMono
      (p := (2 : Fin 4)) (q := (3 : Fin 4)) S
    intro x hx y hy hxy
    have hnot0 := hroot x y hxy
    have hnot1 := havoid hx hy hxy
    generalize hxyc : inside x y = cxy
    fin_cases cxy <;> simp_all
  · apply twoColorFinset_card_le_five inside hnoMono
      (p := (1 : Fin 4)) (q := (3 : Fin 4)) S
    intro x hx y hy hxy
    have hnot0 := hroot x y hxy
    have hnot2 := havoid hx hy hxy
    generalize hxyc : inside x y = cxy
    fin_cases cxy <;> simp_all
  · apply twoColorFinset_card_le_five inside hnoMono
      (p := (1 : Fin 4)) (q := (2 : Fin 4)) S
    intro x hx y hy hxy
    have hnot0 := hroot x y hxy
    have hnot3 := havoid hx hy hxy
    generalize hxyc : inside x y = cxy
    fin_cases cxy <;> simp_all

/-- At order fourteen the three nonzero degrees sum to thirteen.  Combining
that identity with the preceding upper bound shows that each lies between
three and five. -/
theorem rootForbidden_nonzero_degree_ge_three_at_fourteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 14)
    (inside : EdgeColoring V (Fin 4))
    (hnoMono : NoMonochromaticTriangle inside)
    (hroot : ∀ x y : V, x ≠ y → inside x y ≠ 0)
    (a : V) (q : Fin 4) (hq : q ≠ 0) :
    3 ≤ colorDegree inside q a := by
  have hsum := sum_colorDegree_eq_card_sub_one inside a
  have hzero := rootForbidden_zero_degree_eq_zero inside hroot a
  have h1 := rootForbidden_nonzero_degree_le_five
    inside hnoMono hroot a 1 (by decide)
  have h2 := rootForbidden_nonzero_degree_le_five
    inside hnoMono hroot a 2 (by decide)
  have h3 := rootForbidden_nonzero_degree_le_five
    inside hnoMono hroot a 3 (by decide)
  have hsum' :
      colorDegree inside 0 a +
        (colorDegree inside 1 a +
          (colorDegree inside 2 a + colorDegree inside 3 a)) = 13 := by
    simpa [Fin.sum_univ_succ, hcard] using hsum
  fin_cases q <;> simp_all <;> omega

/-! ## The free profile-D K14 -/

theorem inside_zero_degree_eq_zero {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) : colorDegree ext.inside 0 a = 0 :=
  rootForbidden_zero_degree_eq_zero
    ext.inside ext.insideRootForbidden a

theorem inside_nonzero_degree_le_five {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (q : Fin 4) (hq : q ≠ 0) :
    colorDegree ext.inside q a ≤ 5 :=
  rootForbidden_nonzero_degree_le_five
    ext.inside ext.insideNoMono ext.insideRootForbidden a q hq

theorem inside_nonzero_degree_ge_three {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (q : Fin 4) (hq : q ≠ 0) :
    3 ≤ colorDegree ext.inside q a :=
  rootForbidden_nonzero_degree_ge_three_at_fourteen
    (by simp [FreeVertex]) ext.inside ext.insideNoMono
    ext.insideRootForbidden a q hq

/-! ## Tail-row support bounds -/

theorem free_join_degree_decomposition {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (q : Fin 4) :
    colorDegree (fullJoinedColoring ext) q (.inl a) =
      colorDegree ext.inside q a +
        (rowColorSupport (ext.rows a) q).card :=
  colorDegree_joinColoring_inl ext.inside ext.tail.coloring ext.rows q a

theorem row_zero_support_ge_eleven {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) :
    11 ≤ (rowColorSupport (ext.rows a) 0).card := by
  have hdegree := free_zero_degree_ge_eleven ext a
  rw [free_join_degree_decomposition ext a 0,
    inside_zero_degree_eq_zero ext a] at hdegree
  simpa using hdegree

theorem row_zero_support_le_fifteen {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) :
    (rowColorSupport (ext.rows a) 0).card ≤ 15 := by
  have hdegree : colorDegree (fullJoinedColoring ext) 0 (.inl a) ≤ 15 := by
    simpa [fullJoinedRootColor] using
      fullJoinedOwnDegree_le_fifteen ext (.inl a)
  rw [free_join_degree_decomposition ext a 0,
    inside_zero_degree_eq_zero ext a] at hdegree
  simpa using hdegree

theorem row_nonzero_support_ge_seven {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (q : Fin 4) (hq : q ≠ 0) :
    7 ≤ (rowColorSupport (ext.rows a) q).card := by
  have hdegree := free_nonzero_degree_ge_twelve ext a q hq
  have hinside := inside_nonzero_degree_le_five ext a q hq
  rw [free_join_degree_decomposition ext a q] at hdegree
  omega

theorem row_nonzero_support_le_thirteen {kind : Kind} (ext : Extension kind)
    (a : FreeVertex) (q : Fin 4) (hq : q ≠ 0) :
    (rowColorSupport (ext.rows a) q).card ≤ 13 := by
  have hdegree := fullJoinedColorDegree_le_sixteen ext q (.inl a)
  have hinside := inside_nonzero_degree_ge_three ext a q hq
  rw [free_join_degree_decomposition ext a q] at hdegree
  omega

/-! ## Strong four-row endpoint -/

/-- A four-row object together with the degree floors inherited from the
full canonical `K61` star. -/
structure DegreeFlooredFourExtension (kind : Kind) where
  toFourExtension : FourExtension kind
  zeroSupportLower : ∀ a,
    11 ≤ (rowColorSupport (toFourExtension.rows a) 0).card
  zeroSupportUpper : ∀ a,
    (rowColorSupport (toFourExtension.rows a) 0).card ≤ 15
  nonzeroSupportLower : ∀ a q, q ≠ 0 →
    7 ≤ (rowColorSupport (toFourExtension.rows a) q).card
  nonzeroSupportUpper : ∀ a q, q ≠ 0 →
    (rowColorSupport (toFourExtension.rows a) q).card ≤ 13

/-- The support interval, as a predicate on a single proposed tail row. -/
def DegreeFlooredRow (row : TailVertex → Fin 4) : Prop :=
  11 ≤ (rowColorSupport row 0).card ∧
  (rowColorSupport row 0).card ≤ 15 ∧
  ∀ q : Fin 4, q ≠ 0 →
    7 ≤ (rowColorSupport row q).card ∧
      (rowColorSupport row q).card ≤ 13

theorem DegreeFlooredFourExtension.row_degreeFloored {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    DegreeFlooredRow (ext.toFourExtension.rows a) :=
  ⟨ext.zeroSupportLower a, ext.zeroSupportUpper a,
    fun q hq ↦ ⟨ext.nonzeroSupportLower a q hq,
      ext.nonzeroSupportUpper a q hq⟩⟩

/-- The three nonzero supports have total order at least 31. -/
theorem DegreeFlooredFourExtension.nonzero_support_sum_ge_thirtyOne
    {kind : Kind} (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    31 ≤ (rowColorSupport (ext.toFourExtension.rows a) 1).card +
      ((rowColorSupport (ext.toFourExtension.rows a) 2).card +
        (rowColorSupport (ext.toFourExtension.rows a) 3).card) := by
  have hsum := rowColorSupport_sum_fin4
    (ext.toFourExtension.rows a)
  have hzero := ext.zeroSupportUpper a
  simp only [TailVertex, Fintype.card_fin] at hsum
  omega

/-- Consequently every selected row has a nonzero support of order at least
eleven. -/
theorem DegreeFlooredFourExtension.exists_nonzero_support_ge_eleven
    {kind : Kind} (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    11 ≤ (rowColorSupport (ext.toFourExtension.rows a) 1).card ∨
      11 ≤ (rowColorSupport (ext.toFourExtension.rows a) 2).card ∨
      11 ≤ (rowColorSupport (ext.toFourExtension.rows a) 3).card := by
  have hsum := ext.nonzero_support_sum_ge_thirtyOne a
  omega

/-- In fact at least two nonzero supports have order at least nine. -/
theorem DegreeFlooredFourExtension.two_nonzero_supports_ge_nine
    {kind : Kind} (ext : DegreeFlooredFourExtension kind) (a : FourVertex) :
    (9 ≤ (rowColorSupport (ext.toFourExtension.rows a) 1).card ∧
      9 ≤ (rowColorSupport (ext.toFourExtension.rows a) 2).card) ∨
    (9 ≤ (rowColorSupport (ext.toFourExtension.rows a) 1).card ∧
      9 ≤ (rowColorSupport (ext.toFourExtension.rows a) 3).card) ∨
    (9 ≤ (rowColorSupport (ext.toFourExtension.rows a) 2).card ∧
      9 ≤ (rowColorSupport (ext.toFourExtension.rows a) 3).card) := by
  have hsum := ext.nonzero_support_sum_ge_thirtyOne a
  have h1 := ext.nonzeroSupportUpper a 1 (by decide)
  have h2 := ext.nonzeroSupportUpper a 2 (by decide)
  have h3 := ext.nonzeroSupportUpper a 3 (by decide)
  omega

/-- A degree-floored row has no loop in the nonzero-colour compatibility
graph, because all three allowed supports are nonempty. -/
theorem no_nonzero_compatibility_loop_of_degreeFlooredRow
    (row : TailVertex → Fin 4) (hrow : DegreeFlooredRow row) :
    ¬RowsShareAllowedColor {q : Fin 4 | q ≠ 0} row row := by
  rintro ⟨q, hq, havailable⟩
  have hpositive : 0 < (rowColorSupport row q).card := by
    have := (hrow.2.2 q hq).1
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  apply havailable x
  have hxq := (mem_rowColorSupport row q x).mp hx
  exact ⟨hxq, hxq⟩

/-- The four selected rows are genuinely distinct, rather than four copies
of a row with a compatibility loop. -/
theorem DegreeFlooredFourExtension.rows_injective {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    Function.Injective ext.toFourExtension.rows := by
  intro a b hab
  by_contra hne
  have hshare : RowsShareAllowedColor {q : Fin 4 | q ≠ 0}
      (ext.toFourExtension.rows a) (ext.toFourExtension.rows b) := by
    refine ⟨ext.toFourExtension.inside a b,
      ext.toFourExtension.insideRootForbidden a b hne, ?_⟩
    exact (rowPairCompatible_iff_edge_mem_availableColors
      ext.toFourExtension.inside ext.toFourExtension.rows).mp
        ext.toFourExtension.rowsPairCompatible a b hne
  rw [hab] at hshare
  exact no_nonzero_compatibility_loop_of_degreeFlooredRow
    (ext.toFourExtension.rows b) (ext.row_degreeFloored b) hshare

/-! ## The existing K15-block swap preserves every floor -/

theorem transported_rowColorSupport_card {kind : Kind}
    (ext : FourExtension kind) (a : FourVertex) (q : Fin 4) :
    (rowColorSupport
      ((transportFourExtension ext).rows a) q).card =
      (rowColorSupport (ext.rows a) (hostColorPerm.symm q)).card := by
  classical
  let e := tailVertexPerm kind
  let source := rowColorSupport (ext.rows a) (hostColorPerm.symm q)
  have hsupport :
      rowColorSupport ((transportFourExtension ext).rows a) q =
        source.image e.symm := by
    ext x
    simp only [mem_rowColorSupport, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      change e x ∈ source
      apply (mem_rowColorSupport
        (ext.rows a) (hostColorPerm.symm q) (e x)).2
      change hostColorPerm (ext.rows a (e x)) = q at hx
      have hback := congrArg hostColorPerm.symm hx
      simpa using hback
    · rintro ⟨y, hy, hyx⟩
      change hostColorPerm (ext.rows a (e x)) = q
      have hey : e x = y := by
        apply e.symm.injective
        simpa using hyx.symm
      rw [hey]
      change hostColorPerm (ext.rows a y) = q
      have hy' : ext.rows a y = hostColorPerm.symm q :=
        (mem_rowColorSupport
          (ext.rows a) (hostColorPerm.symm q) y).1 (by simpa [source] using hy)
      simpa using congrArg hostColorPerm hy'
  rw [hsupport, Finset.card_image_of_injective source e.symm.injective]

theorem hostColorPerm_symm_zero : hostColorPerm.symm 0 = 0 := by
  apply hostColorPerm.injective
  simp

theorem hostColorPerm_symm_ne_zero {q : Fin 4} (hq : q ≠ 0) :
    hostColorPerm.symm q ≠ 0 := by
  intro hzero
  apply hq
  have := congrArg hostColorPerm hzero
  simpa using this

/-- Swap the two K15 blocks in a degree-floored object.  The tail vertex
permutation preserves support cardinalities, and the host permutation fixes
zero while merely exchanging two nonzero colours. -/
noncomputable def transportDegreeFlooredFour {kind : Kind}
    (ext : DegreeFlooredFourExtension kind) :
    DegreeFlooredFourExtension (swapKind kind) where
  toFourExtension := transportFourExtension ext.toFourExtension
  zeroSupportLower := by
    intro a
    rw [transported_rowColorSupport_card ext.toFourExtension a 0,
      hostColorPerm_symm_zero]
    exact ext.zeroSupportLower a
  zeroSupportUpper := by
    intro a
    rw [transported_rowColorSupport_card ext.toFourExtension a 0,
      hostColorPerm_symm_zero]
    exact ext.zeroSupportUpper a
  nonzeroSupportLower := by
    intro a q hq
    rw [transported_rowColorSupport_card ext.toFourExtension a q]
    exact ext.nonzeroSupportLower a (hostColorPerm.symm q)
      (hostColorPerm_symm_ne_zero hq)
  nonzeroSupportUpper := by
    intro a q hq
    rw [transported_rowColorSupport_card ext.toFourExtension a q]
    exact ext.nonzeroSupportUpper a (hostColorPerm.symm q)
      (hostColorPerm_symm_ne_zero hq)

theorem nonempty_degreeFlooredFour_iff_swapKind (kind : Kind) :
    Nonempty (DegreeFlooredFourExtension kind) ↔
      Nonempty (DegreeFlooredFourExtension (swapKind kind)) := by
  constructor
  · rintro ⟨ext⟩
    exact ⟨transportDegreeFlooredFour ext⟩
  · rintro ⟨ext⟩
    have hback := transportDegreeFlooredFour ext
    simpa using Nonempty.intro hback

/-- Restrict a full fourteen-row extension while retaining all four support
intervals for each selected row. -/
def restrictDegreeFlooredFour {kind : Kind} (ext : Extension kind) :
    DegreeFlooredFourExtension kind where
  toFourExtension := restrictFour ext
  zeroSupportLower := by
    intro a
    exact row_zero_support_ge_eleven ext (fourEmbedding a)
  zeroSupportUpper := by
    intro a
    exact row_zero_support_le_fifteen ext (fourEmbedding a)
  nonzeroSupportLower := by
    intro a q hq
    exact row_nonzero_support_ge_seven ext (fourEmbedding a) q hq
  nonzeroSupportUpper := by
    intro a q hq
    exact row_nonzero_support_le_thirteen ext (fourEmbedding a) q hq

def degreeFlooredFourExtensionOfStar
    (w : CanonicalStarWitness ProfileD) :
    DegreeFlooredFourExtension (kindOfWitness w) :=
  restrictDegreeFlooredFour (extensionOfStar w)

theorem exists_degreeFlooredFourExtension_of_star
    (w : CanonicalStarWitness ProfileD) :
    ∃ kind : Kind, Nonempty (DegreeFlooredFourExtension kind) :=
  ⟨kindOfWitness w, ⟨degreeFlooredFourExtensionOfStar w⟩⟩

def UniversalDegreeFlooredFourRowObstruction : Prop :=
  ∀ kind : Kind, ¬Nonempty (DegreeFlooredFourExtension kind)

/-- Only six degree-floored kinds remain after exchanging the two equal
K15 blocks. -/
structure SwapRepresentativeDegreeFlooredObstructions : Prop where
  uuu : ¬Nonempty (DegreeFlooredFourExtension .uuu)
  uut : ¬Nonempty (DegreeFlooredFourExtension .uut)
  utu : ¬Nonempty (DegreeFlooredFourExtension .utu)
  utt : ¬Nonempty (DegreeFlooredFourExtension .utt)
  ttu : ¬Nonempty (DegreeFlooredFourExtension .ttu)
  ttt : ¬Nonempty (DegreeFlooredFourExtension .ttt)

theorem SwapRepresentativeDegreeFlooredObstructions.universal
    (h : SwapRepresentativeDegreeFlooredObstructions) :
    UniversalDegreeFlooredFourRowObstruction := by
  intro kind
  cases kind with
  | uuu => exact h.uuu
  | uut => exact h.uut
  | utu => exact h.utu
  | utt => exact h.utt
  | tuu =>
      intro hext
      apply h.utu
      have htransported :=
        (nonempty_degreeFlooredFour_iff_swapKind .tuu).mp hext
      simpa [swapKind, Kind.twisted, Kind.ofBooleans] using htransported
  | tut =>
      intro hext
      apply h.utt
      have htransported :=
        (nonempty_degreeFlooredFour_iff_swapKind .tut).mp hext
      simpa [swapKind, Kind.twisted, Kind.ofBooleans] using htransported
  | ttu => exact h.ttu
  | ttt => exact h.ttt

/-- It is enough to refute the six swap-representative degree-floored
four-row objects; the packaging of that symmetry can be layered separately.
This universal form already strictly strengthens the previous eight-kind
four-row endpoint. -/
theorem no_profileD_star_of_degreeFlooredFourRowObstruction
    (h : UniversalDegreeFlooredFourRowObstruction) :
    ¬Nonempty (CanonicalStarWitness ProfileD) := by
  rintro ⟨w⟩
  obtain ⟨kind, hext⟩ := exists_degreeFlooredFourExtension_of_star w
  exact h kind hext

theorem no_profileD_star_of_swapRepresentativeDegreeFlooredObstructions
    (h : SwapRepresentativeDegreeFlooredObstructions) :
    ¬Nonempty (CanonicalStarWitness ProfileD) :=
  no_profileD_star_of_degreeFlooredFourRowObstruction h.universal

#print axioms R4333.ProfileDRowSupportBounds61.colorDegree_joinColoring_inl
#print axioms R4333.ProfileDRowSupportBounds61.rootForbidden_nonzero_degree_ge_three_at_fourteen
#print axioms R4333.ProfileDRowSupportBounds61.row_zero_support_ge_eleven
#print axioms R4333.ProfileDRowSupportBounds61.row_nonzero_support_ge_seven
#print axioms R4333.ProfileDRowSupportBounds61.row_nonzero_support_le_thirteen
#print axioms R4333.ProfileDRowSupportBounds61.DegreeFlooredFourExtension.rows_injective
#print axioms R4333.ProfileDRowSupportBounds61.restrictDegreeFlooredFour
#print axioms R4333.ProfileDRowSupportBounds61.no_profileD_star_of_degreeFlooredFourRowObstruction
#print axioms R4333.ProfileDRowSupportBounds61.transportDegreeFlooredFour
#print axioms R4333.ProfileDRowSupportBounds61.no_profileD_star_of_swapRepresentativeDegreeFlooredObstructions

end ProfileDRowSupportBounds61
end R4333
