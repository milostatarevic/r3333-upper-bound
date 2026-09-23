import R4333Lean.Attaching61
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Trusted interfaces for the critical three-colour catalogues

The finite attaching proof needs the critical triangle-free three-colourings
on 15 and 16 vertices.  This file defines the mathematical statement that a
catalogue must satisfy.  It contains no catalogue data and no completeness
assumption: a later certificate must construct terms of these definitions.
-/

namespace R4333

/-- The concrete three-element colour type used by the neighbourhood
templates. -/
abbrev ThreeColor := Fin 3

private theorem fin3_cases (q : ThreeColor) :
    q = 0 ∨ q = 1 ∨ q = 2 := by fin_cases q <;> simp

private theorem fin3_ne_zero (q : ThreeColor) (h : q ≠ 0) :
    q = 1 ∨ q = 2 := by fin_cases q <;> simp_all

private theorem fin3_ne_one (q : ThreeColor) (h : q ≠ 1) :
    q = 0 ∨ q = 2 := by fin_cases q <;> simp_all

private theorem fin3_ne_two (q : ThreeColor) (h : q ≠ 2) :
    q = 0 ∨ q = 1 := by fin_cases q <;> simp_all

/-- In a critical three-colouring of `K16`, every vertex has degree exactly
five in every colour.  This is the ordinary mathematical normalization that
precedes the finite Clebsch-classification certificate. -/
theorem threeColor_degree_eq_five_at_16
    (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor) (v : Fin 16) :
    colorDegree c q v = 5 := by
  have hle : ∀ r : ThreeColor, colorDegree c r v ≤ 5 := by
    intro r
    fin_cases r
    · apply twoColorFinset_card_le_five c hc
        (p := (1 : Fin 3)) (q := (2 : Fin 3))
        (colorNeighborhood c (0 : Fin 3) v)
      intro x hx y hy hxy
      have hnot := neighborhood_avoids_own_color c hc hx hy hxy
      exact fin3_ne_zero (c x y) hnot
    · apply twoColorFinset_card_le_five c hc
        (p := (0 : Fin 3)) (q := (2 : Fin 3))
        (colorNeighborhood c (1 : Fin 3) v)
      intro x hx y hy hxy
      have hnot := neighborhood_avoids_own_color c hc hx hy hxy
      exact fin3_ne_one (c x y) hnot
    · apply twoColorFinset_card_le_five c hc
        (p := (0 : Fin 3)) (q := (1 : Fin 3))
        (colorNeighborhood c (2 : Fin 3) v)
      intro x hx y hy hxy
      have hnot := neighborhood_avoids_own_color c hc hx hy hxy
      exact fin3_ne_two (c x y) hnot
  have hsum := sum_colorDegree_eq_card_sub_one c v
  have hsum' :
      colorDegree c (0 : Fin 3) v +
        (colorDegree c (1 : Fin 3) v + colorDegree c (2 : Fin 3) v) = 15 := by
    simpa [Fin.sum_univ_succ] using hsum
  have h0 := hle (0 : Fin 3)
  have h1 := hle (1 : Fin 3)
  have h2 := hle (2 : Fin 3)
  rcases fin3_cases q with rfl | rfl | rfl <;> omega

/-- Every independent set in one colour graph of a critical `K16`
three-colouring has at most five vertices. -/
theorem threeColor_independent_card_le_five_at_16
    (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor)
    (S : Finset (Fin 16))
    (hindependent : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → c x y ≠ q) :
    S.card ≤ 5 := by
  rcases fin3_cases q with rfl | rfl | rfl
  · apply twoColorFinset_card_le_five c hc
      (p := (1 : Fin 3)) (q := (2 : Fin 3)) S
    intro x hx y hy hxy
    have hnot := hindependent hx hy hxy
    exact fin3_ne_zero (c x y) hnot
  · apply twoColorFinset_card_le_five c hc
      (p := (0 : Fin 3)) (q := (2 : Fin 3)) S
    intro x hx y hy hxy
    have hnot := hindependent hx hy hxy
    exact fin3_ne_one (c x y) hnot
  · apply twoColorFinset_card_le_five c hc
      (p := (0 : Fin 3)) (q := (1 : Fin 3)) S
    intro x hx y hy hxy
    have hnot := hindependent hx hy hxy
    exact fin3_ne_two (c x y) hnot

/-- A vertex relabeling together with a global colour relabeling.  Edge
values on the diagonal remain irrelevant. -/
structure WeakColorEquiv {V W C D : Type*}
    (c : EdgeColoring V C) (d : EdgeColoring W D) where
  vertex : V ≃ W
  colors : C ≃ D
  map_color : ∀ u v, u ≠ v → colors (c u v) = d (vertex u) (vertex v)

namespace WeakColorEquiv

/-- Identity weak isomorphism. -/
def refl {V C : Type*} (c : EdgeColoring V C) : WeakColorEquiv c c where
  vertex := Equiv.refl V
  colors := Equiv.refl C
  map_color := by simp

/-- Reverse a weak colour isomorphism. -/
def symm {V W C D : Type*} {c : EdgeColoring V C} {d : EdgeColoring W D}
    (e : WeakColorEquiv c d) : WeakColorEquiv d c where
  vertex := e.vertex.symm
  colors := e.colors.symm
  map_color := by
    intro x y hxy
    apply e.colors.injective
    simpa using (e.map_color (e.vertex.symm x) (e.vertex.symm y)
      (by simpa using e.vertex.symm.injective.ne hxy)).symm

/-- Compose vertex and colour relabelings. -/
def trans {U V W A B C : Type*}
    {a : EdgeColoring U A} {b : EdgeColoring V B} {c : EdgeColoring W C}
    (e₁ : WeakColorEquiv a b) (e₂ : WeakColorEquiv b c) :
    WeakColorEquiv a c where
  vertex := e₁.vertex.trans e₂.vertex
  colors := e₁.colors.trans e₂.colors
  map_color := by
    intro x y hxy
    exact congrArg e₂.colors (e₁.map_color x y hxy) |>.trans
      (e₂.map_color (e₁.vertex x) (e₁.vertex y)
        (e₁.vertex.injective.ne hxy))

/-- A weak isomorphism transports the absence of monochromatic triangles. -/
theorem noMono_map {V W C D : Type*}
    {c : EdgeColoring V C} {d : EdgeColoring W D}
    (e : WeakColorEquiv c d)
    (hc : NoMonochromaticTriangle c) : NoMonochromaticTriangle d := by
  intro x y z hxyz hd
  let u := e.vertex.symm x
  let v := e.vertex.symm y
  let w := e.vertex.symm z
  have huv : u ≠ v := by
    intro h
    apply hxyz.1
    have hmapped := congrArg e.vertex h
    simpa [u, v] using hmapped
  have huw : u ≠ w := by
    intro h
    apply hxyz.2.1
    have hmapped := congrArg e.vertex h
    simpa [u, w] using hmapped
  have hvw : v ≠ w := by
    intro h
    apply hxyz.2.2
    have hmapped := congrArg e.vertex h
    simpa [v, w] using hmapped
  apply hc u v w ⟨huv, huw, hvw⟩
  constructor
  · apply e.colors.injective
    calc
      e.colors (c u v) = d x y := by simpa [u, v] using e.map_color u v huv
      _ = d x z := hd.1
      _ = e.colors (c u w) := by
        simpa [u, w] using (e.map_color u w huw).symm
  · apply e.colors.injective
    calc
      e.colors (c u w) = d x z := by simpa [u, w] using e.map_color u w huw
      _ = d y z := hd.2
      _ = e.colors (c v w) := by
        simpa [v, w] using (e.map_color v w hvw).symm

/-- A weak isomorphism preserves the absence of monochromatic triangles in
both directions. -/
theorem noMono_iff {V W C D : Type*}
    {c : EdgeColoring V C} {d : EdgeColoring W D}
    (e : WeakColorEquiv c d) :
    NoMonochromaticTriangle c ↔ NoMonochromaticTriangle d :=
  ⟨noMono_map e, noMono_map e.symm⟩

end WeakColorEquiv

/-- A finite list is complete when every triangle-free labeled coloring is
weakly isomorphic to a listed entry.  Completeness is a theorem to be
certificate-checked, never an input axiom. -/
def ThreeColorCatalogueComplete (n : ℕ)
    (catalogue : List (EdgeColoring (Fin n) ThreeColor)) : Prop :=
  (∀ t ∈ catalogue, NoMonochromaticTriangle t) ∧
  ∀ c : EdgeColoring (Fin n) ThreeColor,
    NoMonochromaticTriangle c →
      ∃ t ∈ catalogue, Nonempty (WeakColorEquiv c t)

/-- An explicit embedding of one colored complete graph into another,
allowing a global permutation of the three colors. -/
structure ColorEmbedding {V W C D : Type*}
    (small : EdgeColoring V C) (large : EdgeColoring W D) where
  vertex : V ↪ W
  colors : C ≃ D
  map_color : ∀ u v, u ≠ v →
    colors (small u v) = large (vertex u) (vertex v)

namespace ColorEmbedding

/-- Precompose an embedding with a weak isomorphism of its source. -/
def precompWeak {U V W A B C : Type*}
    {a : EdgeColoring U A} {b : EdgeColoring V B} {c : EdgeColoring W C}
    (e : WeakColorEquiv a b) (f : ColorEmbedding b c) :
    ColorEmbedding a c where
  vertex := e.vertex.toEmbedding.trans f.vertex
  colors := e.colors.trans f.colors
  map_color := by
    intro u v huv
    exact congrArg f.colors (e.map_color u v huv) |>.trans
      (f.map_color (e.vertex u) (e.vertex v) (e.vertex.injective.ne huv))

end ColorEmbedding

/-- Every good coloring of order `m` extends to some good coloring of order
`n`.  This is the exact catalogue fact required to replace private arbitrary
templates by the critical order-15/16 objects. -/
def EveryThreeColoringExtends (m n : ℕ) : Prop :=
  ∀ c : EdgeColoring (Fin m) ThreeColor,
    NoMonochromaticTriangle c →
      ∃ d : EdgeColoring (Fin n) ThreeColor,
        NoMonochromaticTriangle d ∧ Nonempty (ColorEmbedding c d)

/-- A complete good catalogue reduces a universal extension theorem to one
explicit extension witness for each listed representative. -/
theorem everyThreeColoringExtends_of_catalogue
    {m n : ℕ} {catalogue : List (EdgeColoring (Fin m) ThreeColor)}
    (hcomplete : ThreeColorCatalogueComplete m catalogue)
    (hextends : ∀ t ∈ catalogue,
      ∃ d : EdgeColoring (Fin n) ThreeColor,
        NoMonochromaticTriangle d ∧ Nonempty (ColorEmbedding t d)) :
    EveryThreeColoringExtends m n := by
  intro c hc
  obtain ⟨t, ht, ⟨e⟩⟩ := hcomplete.2 c hc
  obtain ⟨d, hd, ⟨f⟩⟩ := hextends t ht
  exact ⟨d, hd, ⟨f.precompWeak e⟩⟩

#print axioms R4333.threeColor_degree_eq_five_at_16
#print axioms R4333.threeColor_independent_card_le_five_at_16
#print axioms R4333.WeakColorEquiv.noMono_iff
#print axioms R4333.everyThreeColoringExtends_of_catalogue

end R4333
