import R4333Lean.Basic

/-!
# Exact row semantics for extending a coloured complete graph

When a fixed coloured core is extended by new vertices, each new vertex is
described by one cross row into the core.  This file proves the exact
decomposition of the triangle condition:

* the core and the new-vertex subgraph are triangle-free;
* every individual row is admissible against core edges; and
* every pair of rows is compatible with the colour of the corresponding
  new-vertex edge.

This is the semantic form of the reduced extension searches used for the
profile-A and profile-D tails.  No finiteness or SAT encoding is involved.
-/

namespace R4333
namespace ColoringJoinRows

/-- One proposed cross row creates no monochromatic triangle with two core
vertices. -/
def RowAdmissible {B C : Type*}
    (base : EdgeColoring B C) (row : B → C) : Prop :=
  ∀ x y : B, x ≠ y →
    ¬(row x = row y ∧ row y = base x y)

/-- Two rows create no monochromatic triangle with their new-vertex edge. -/
def RowPairCompatible {A B C : Type*}
    (inside : EdgeColoring A C) (rows : A → B → C) : Prop :=
  ∀ a b : A, a ≠ b → ∀ x : B,
    ¬(inside a b = rows a x ∧ rows a x = rows b x)

/-- Colours available for the edge between two proposed extension rows.  A
colour is available exactly when the two rows never take it simultaneously
at a core vertex. -/
def availableColors {B C : Type*} (left right : B → C) : Set C :=
  {q | ∀ x : B, ¬(left x = q ∧ right x = q)}

/-- Two rows are adjacent in the compatibility graph for `allowed` if at
least one allowed new--new edge colour is available between them. -/
def RowsShareAllowedColor {B C : Type*}
    (allowed : Set C) (left right : B → C) : Prop :=
  ∃ q : C, q ∈ allowed ∧ q ∈ availableColors left right

theorem rowPairCompatible_iff_edge_mem_availableColors
    {A B C : Type*} (inside : EdgeColoring A C) (rows : A → B → C) :
    RowPairCompatible inside rows ↔
      ∀ a b : A, a ≠ b →
        inside a b ∈ availableColors (rows a) (rows b) := by
  constructor
  · intro h a b hab x hcollision
    apply h a b hab x
    exact ⟨hcollision.1.symm, hcollision.1.trans hcollision.2.symm⟩
  · intro h a b hab x hcollision
    apply h a b hab x
    exact ⟨hcollision.1.symm,
      hcollision.2.symm.trans hcollision.1.symm⟩

/-- Join a coloured graph on `A` to a coloured graph on `B` using one
`B`-row for each vertex of `A`. -/
def joinColoring {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) : EdgeColoring (Sum A B) C where
  color
    | .inl a, .inl b => inside a b
    | .inl a, .inr x => rows a x
    | .inr x, .inl a => rows a x
    | .inr x, .inr y => base x y
  color_symm u v := by
    cases u <;> cases v <;> simp [inside.color_symm, base.color_symm]

@[simp] theorem joinColoring_inl_inl {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (a b : A) :
    joinColoring inside base rows (.inl a) (.inl b) = inside a b := rfl

@[simp] theorem joinColoring_inl_inr {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (a : A) (x : B) :
    joinColoring inside base rows (.inl a) (.inr x) = rows a x := rfl

@[simp] theorem joinColoring_inr_inl {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (x : B) (a : A) :
    joinColoring inside base rows (.inr x) (.inl a) = rows a x := rfl

@[simp] theorem joinColoring_inr_inr {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (x y : B) :
    joinColoring inside base rows (.inr x) (.inr y) = base x y := rfl

/-- Exact extension theorem: the three displayed conditions are jointly
necessary and sufficient for the joined colouring to be triangle-free. -/
theorem noMono_joinColoring_iff {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) :
    NoMonochromaticTriangle (joinColoring inside base rows) ↔
      NoMonochromaticTriangle inside ∧
      NoMonochromaticTriangle base ∧
      (∀ a : A, RowAdmissible base (rows a)) ∧
      RowPairCompatible inside rows := by
  constructor
  · intro hjoin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b d habd hhom
      apply hjoin (.inl a) (.inl b) (.inl d)
      · exact
          ⟨fun h ↦ habd.1 (Sum.inl.inj h),
           fun h ↦ habd.2.1 (Sum.inl.inj h),
           fun h ↦ habd.2.2 (Sum.inl.inj h)⟩
      · exact hhom
    · intro x y z hxyz hhom
      apply hjoin (.inr x) (.inr y) (.inr z)
      · exact
          ⟨fun h ↦ hxyz.1 (Sum.inr.inj h),
           fun h ↦ hxyz.2.1 (Sum.inr.inj h),
           fun h ↦ hxyz.2.2 (Sum.inr.inj h)⟩
      · exact hhom
    · intro a x y hxy hbad
      apply hjoin (.inl a) (.inr x) (.inr y)
      · exact ⟨Sum.inl_ne_inr, Sum.inl_ne_inr,
          fun h ↦ hxy (Sum.inr.inj h)⟩
      · exact hbad
    · intro a b hab x hbad
      apply hjoin (.inl a) (.inl b) (.inr x)
      · exact ⟨fun h ↦ hab (Sum.inl.inj h),
          Sum.inl_ne_inr, Sum.inl_ne_inr⟩
      · exact hbad
  · rintro ⟨hinside, hbase, hrows, hpairs⟩
    intro u v w huv hhom
    cases u with
    | inl a =>
        cases v with
        | inl b =>
            cases w with
            | inl d =>
                apply hinside a b d
                · exact
                    ⟨fun h ↦ huv.1 (congrArg Sum.inl h),
                     fun h ↦ huv.2.1 (congrArg Sum.inl h),
                     fun h ↦ huv.2.2 (congrArg Sum.inl h)⟩
                · exact hhom
            | inr x =>
                have hab : a ≠ b :=
                  fun h ↦ huv.1 (congrArg Sum.inl h)
                exact hpairs a b hab x hhom
        | inr x =>
            cases w with
            | inl b =>
                have hab : a ≠ b :=
                  fun h ↦ huv.2.1 (congrArg Sum.inl h)
                apply hpairs a b hab x
                exact ⟨hhom.1.symm, hhom.1.trans hhom.2⟩
            | inr y =>
                have hxy : x ≠ y :=
                  fun h ↦ huv.2.2 (congrArg Sum.inr h)
                exact hrows a x y hxy hhom
    | inr x =>
        cases v with
        | inl a =>
            cases w with
            | inl b =>
                have hab : a ≠ b :=
                  fun h ↦ huv.2.2 (congrArg Sum.inl h)
                apply hpairs a b hab x
                exact ⟨hhom.2.symm.trans hhom.1.symm, hhom.1⟩
            | inr y =>
                have hxy : x ≠ y :=
                  fun h ↦ huv.2.1 (congrArg Sum.inr h)
                apply hrows a x y hxy
                exact ⟨hhom.1.trans hhom.2, hhom.2.symm⟩
        | inr y =>
            cases w with
            | inl a =>
                have hxy : x ≠ y :=
                  fun h ↦ huv.1 (congrArg Sum.inr h)
                apply hrows a x y hxy
                exact ⟨hhom.2, hhom.2.symm.trans hhom.1.symm⟩
            | inr z =>
                apply hbase x y z
                · exact
                    ⟨fun h ↦ huv.1 (congrArg Sum.inr h),
                     fun h ↦ huv.2.1 (congrArg Sum.inr h),
                     fun h ↦ huv.2.2 (congrArg Sum.inr h)⟩
                · exact hhom

/-- Every distinct pair of extension rows is adjacent in the allowed-colour
compatibility graph. -/
theorem extension_rows_share_allowed {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (allowed : Set C)
    (hinsideAllowed : ∀ a b : A, a ≠ b → inside a b ∈ allowed)
    (hjoin : NoMonochromaticTriangle (joinColoring inside base rows)) :
    ∀ a b : A, a ≠ b →
      RowsShareAllowedColor allowed (rows a) (rows b) := by
  have hpairs :=
    (rowPairCompatible_iff_edge_mem_availableColors inside rows).mp
      ((noMono_joinColoring_iff inside base rows).mp hjoin).2.2.2
  intro a b hab
  exact ⟨inside a b, hinsideAllowed a b hab, hpairs a b hab⟩

/-- If no admissible row has a compatibility loop, distinct extension
vertices have distinct rows. -/
theorem extension_rows_injective_of_no_admissible_loop
    {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (allowed : Set C)
    (hinsideAllowed : ∀ a b : A, a ≠ b → inside a b ∈ allowed)
    (hnoLoop : ∀ row : B → C, RowAdmissible base row →
      ¬RowsShareAllowedColor allowed row row)
    (hjoin : NoMonochromaticTriangle (joinColoring inside base rows)) :
    Function.Injective rows := by
  have hdecomp := (noMono_joinColoring_iff inside base rows).mp hjoin
  have hshare := extension_rows_share_allowed
    inside base rows allowed hinsideAllowed hjoin
  intro a b hrows
  by_contra hab
  apply hnoLoop (rows a) (hdecomp.2.2.1 a)
  simpa [hrows] using hshare a b hab

/-- A finite clique-number bound on the admissible-row compatibility graph
transfers directly to the number of new vertices in any extension. -/
theorem extension_card_le_of_row_clique_bound
    {A B C : Type*} [Fintype A]
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (allowed : Set C) (bound : Nat)
    (hinsideAllowed : ∀ a b : A, a ≠ b → inside a b ∈ allowed)
    (hnoLoop : ∀ row : B → C, RowAdmissible base row →
      ¬RowsShareAllowedColor allowed row row)
    (hclique : ∀ S : Finset (B → C),
      (∀ row ∈ S, RowAdmissible base row) →
      (∀ left ∈ S, ∀ right ∈ S, left ≠ right →
        RowsShareAllowedColor allowed left right) →
      S.card ≤ bound)
    (hjoin : NoMonochromaticTriangle (joinColoring inside base rows)) :
    Fintype.card A ≤ bound := by
  classical
  have hdecomp := (noMono_joinColoring_iff inside base rows).mp hjoin
  have hinjective := extension_rows_injective_of_no_admissible_loop
    inside base rows allowed hinsideAllowed hnoLoop hjoin
  have hshare := extension_rows_share_allowed
    inside base rows allowed hinsideAllowed hjoin
  let rowSet : Finset (B → C) := Finset.univ.image rows
  have hrowCard : rowSet.card = Fintype.card A := by
    rw [show Fintype.card A = (Finset.univ : Finset A).card by simp]
    exact Finset.card_image_of_injective Finset.univ hinjective
  have hadmissible : ∀ row ∈ rowSet, RowAdmissible base row := by
    intro row hrow
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hrow
    exact hdecomp.2.2.1 a
  have hpairwise : ∀ left ∈ rowSet, ∀ right ∈ rowSet,
      left ≠ right → RowsShareAllowedColor allowed left right := by
    intro left hleft right hright hlr
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hleft
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hright
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hlr rfl
    exact hshare a b hab
  rw [← hrowCard]
  exact hclique rowSet hadmissible hpairwise

/-- A reusable two-vertex obstruction.  If no two individually admissible
rows share an available colour from the palette allowed on new--new edges,
then a triangle-free extension can contain at most one new vertex.  This is
the exact universal statement that a fixed-tail two-row UNSAT certificate
would need to establish before it could eliminate a whole star profile. -/
theorem subsingleton_of_no_allowed_compatible_admissible_rows
    {A B C : Type*}
    (inside : EdgeColoring A C) (base : EdgeColoring B C)
    (rows : A → B → C) (allowed : Set C)
    (hinsideAllowed : ∀ a b : A, a ≠ b → inside a b ∈ allowed)
    (hnoPair : ∀ left right : B → C,
      RowAdmissible base left → RowAdmissible base right →
      ∀ q : C, q ∈ allowed → q ∉ availableColors left right)
    (hjoin : NoMonochromaticTriangle (joinColoring inside base rows)) :
    Subsingleton A := by
  have hdecomp := (noMono_joinColoring_iff inside base rows).mp hjoin
  have hpairs :=
    (rowPairCompatible_iff_edge_mem_availableColors inside rows).mp
      hdecomp.2.2.2
  constructor
  intro a b
  by_contra hab
  have hallowed := hinsideAllowed a b hab
  have havailable := hpairs a b hab
  exact hnoPair (rows a) (rows b) (hdecomp.2.2.1 a)
    (hdecomp.2.2.1 b) (inside a b) hallowed havailable

#print axioms R4333.ColoringJoinRows.noMono_joinColoring_iff
#print axioms R4333.ColoringJoinRows.rowPairCompatible_iff_edge_mem_availableColors
#print axioms R4333.ColoringJoinRows.extension_rows_share_allowed
#print axioms R4333.ColoringJoinRows.extension_card_le_of_row_clique_bound
#print axioms R4333.ColoringJoinRows.subsingleton_of_no_allowed_compatible_admissible_rows

end ColoringJoinRows
end R4333
