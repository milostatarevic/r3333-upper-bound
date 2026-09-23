/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
-/
import R4333Lean.ColorRelabel
import Mathlib.Data.Fintype.EquivFin

/-!
# Three-colourings induced on four-colour neighbourhoods

If all vertices in a set are joined to a root by one fixed colour `delta`,
then no edge between two distinct vertices of that set can have colour
`delta`.  Thus a triangle-free four-colouring induces a triangle-free
three-colouring on each monochromatic neighbourhood.

The diagonal of an `EdgeColoring` is deliberately unconstrained.  The
construction below therefore replaces diagonal values by an explicit colour
different from `delta`; it never attempts to prove that an original diagonal
value avoids `delta`.
-/

namespace R4333

/-- The three four-colours other than the root colour `delta`. -/
abbrev NeighborhoodColor (delta : FourColor) :=
  {q : FourColor // q ≠ delta}

/-- Flip the first bit to obtain a canonical colour different from `delta`.
This is used only to fill irrelevant diagonal entries. -/
def alternateNeighborhoodColor (delta : FourColor) : NeighborhoodColor delta :=
  ⟨(!delta.1, delta.2), by
    rcases delta with ⟨a, b⟩
    cases a <;> simp⟩

/-- Removing one element from the four-element colour type leaves exactly
three colours. -/
theorem neighborhoodColor_card (delta : FourColor) :
    Fintype.card (NeighborhoodColor delta) = 3 := by
  rcases delta with ⟨a, b⟩
  cases a <;> cases b <;> decide

/-- A fixed, kernel-defined equivalence from the three remaining colours to
the catalogue colour type `Fin 3`. -/
noncomputable def neighborhoodColorEquivFin3 (delta : FourColor) :
    NeighborhoodColor delta ≃ Fin 3 :=
  Fintype.equivOfCardEq (by simp)

/-- The vertices in the `delta`-neighbourhood of `root`. -/
abbrev NeighborhoodVertex {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (root : V) :=
  {v : V // v ∈ colorNeighborhood c delta root}

/-- The induced colouring of a monochromatic neighbourhood by the three
colours other than `delta`.  On the diagonal it uses
`alternateNeighborhoodColor delta`; on distinct vertices it uses `c`. -/
def neighborhoodThreeColoring {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V) :
    EdgeColoring (NeighborhoodVertex c delta root) (NeighborhoodColor delta) where
  color x y :=
    if hxy : x = y then
      alternateNeighborhoodColor delta
    else
      ⟨c x.1 y.1, neighborhood_avoids_own_color c hc x.2 y.2
        (fun hval ↦ hxy (Subtype.ext hval))⟩
  color_symm x y := by
    by_cases hxy : x = y
    · subst y
      rfl
    · have hyx : y ≠ x := Ne.symm hxy
      simp only [hxy, hyx, ↓reduceDIte]
      apply Subtype.ext
      exact c.color_symm x.1 y.1

/-- Off the diagonal, the induced colour has exactly the original
four-colour as its underlying value. -/
@[simp]
theorem neighborhoodThreeColoring_coe_apply_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (x y : NeighborhoodVertex c delta root) (hxy : x ≠ y) :
    ((neighborhoodThreeColoring c hc delta root x y :
        NeighborhoodColor delta) : FourColor) = c x.1 y.1 := by
  simp [neighborhoodThreeColoring, hxy]

/-- The diagonal is filled by the explicit safe colour, independently of
the diagonal of the original colouring. -/
@[simp]
theorem neighborhoodThreeColoring_apply_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (x : NeighborhoodVertex c delta root) :
    neighborhoodThreeColoring c hc delta root x x =
      alternateNeighborhoodColor delta := by
  simp [neighborhoodThreeColoring]

/-- The induced three-colouring of every monochromatic neighbourhood remains
triangle-free. -/
theorem neighborhoodThreeColoring_good
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V) :
    NoMonochromaticTriangle (neighborhoodThreeColoring c hc delta root) := by
  intro x y z hdistinct hmono
  have hxy : x.1 ≠ y.1 := by
    intro h
    exact hdistinct.1 (Subtype.ext h)
  have hxz : x.1 ≠ z.1 := by
    intro h
    exact hdistinct.2.1 (Subtype.ext h)
  have hyz : y.1 ≠ z.1 := by
    intro h
    exact hdistinct.2.2 (Subtype.ext h)
  apply hc x.1 y.1 z.1 ⟨hxy, hxz, hyz⟩
  constructor
  · have h := congrArg Subtype.val hmono.1
    simpa [neighborhoodThreeColoring, hdistinct.1, hdistinct.2.1] using h
  · have h := congrArg Subtype.val hmono.2
    simpa [neighborhoodThreeColoring, hdistinct.2.1, hdistinct.2.2] using h

/-- The subtype of neighbourhood vertices has cardinality equal to the
ordinary colour degree. -/
theorem neighborhoodVertex_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (root : V) :
    Fintype.card (NeighborhoodVertex c delta root) =
      colorDegree c delta root := by
  change Fintype.card ↥(colorNeighborhood c delta root) =
    (colorNeighborhood c delta root).card
  exact Fintype.card_coe _

/-- Label a neighbourhood of cardinality `n` by `Fin n`. -/
noncomputable def neighborhoodVertexEquivFin
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (root : V)
    (hcard : Fintype.card (NeighborhoodVertex c delta root) = n) :
    Fin n ≃ NeighborhoodVertex c delta root :=
  Fintype.equivOfCardEq (by simpa using hcard.symm)

/-- The same labeling, with the hypothesis expressed as an equality of colour
degree rather than an equality of subtype cardinality. -/
noncomputable def neighborhoodVertexEquivFinOfDegree
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (root : V)
    (hdegree : colorDegree c delta root = n) :
    Fin n ≃ NeighborhoodVertex c delta root :=
  neighborhoodVertexEquivFin c delta root
    ((neighborhoodVertex_card c delta root).trans hdegree)

/-- Pull the induced colouring back along a chosen `Fin n` labeling and map
its remaining colour subtype to the catalogue type `Fin 3`. -/
noncomputable def labeledNeighborhoodThreeColoring
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (e : Fin n ≃ NeighborhoodVertex c delta root) :
    EdgeColoring (Fin n) (Fin 3) :=
  mapEdgeColors
    (relabelVertices (neighborhoodThreeColoring c hc delta root) e)
    (neighborhoodColorEquivFin3 delta)

/-- Off the diagonal, undoing the chosen colour labeling recovers the
original four-colour on the corresponding pair of neighbourhood vertices. -/
@[simp]
theorem neighborhoodColorEquivFin3_symm_labeled_apply_of_ne
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (e : Fin n ≃ NeighborhoodVertex c delta root)
    (i j : Fin n) (hij : i ≠ j) :
    (((neighborhoodColorEquivFin3 delta).symm
        (labeledNeighborhoodThreeColoring c hc delta root e i j) :
      NeighborhoodColor delta) : FourColor) =
      c (e i).1 (e j).1 := by
  simp [labeledNeighborhoodThreeColoring, hij]

/-- Every explicitly labeled monochromatic neighbourhood gives a good
`Fin 3`-colouring, ready for a labeled K15/K16 catalogue theorem. -/
theorem labeledNeighborhoodThreeColoring_good
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (e : Fin n ≃ NeighborhoodVertex c delta root) :
    NoMonochromaticTriangle
      (labeledNeighborhoodThreeColoring c hc delta root e) :=
  noMono_mapEdgeColors _ _
    (noMono_relabelVertices _ e
      (neighborhoodThreeColoring_good c hc delta root))

/-- Canonical labeled version obtained directly from a subtype-cardinality
equality. -/
noncomputable def labeledNeighborhoodThreeColoringOfCard
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (hcard : Fintype.card (NeighborhoodVertex c delta root) = n) :
    EdgeColoring (Fin n) (Fin 3) :=
  labeledNeighborhoodThreeColoring c hc delta root
    (neighborhoodVertexEquivFin c delta root hcard)

/-- The subtype-cardinality-indexed labeled version is triangle-free. -/
theorem labeledNeighborhoodThreeColoringOfCard_good
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (hcard : Fintype.card (NeighborhoodVertex c delta root) = n) :
    NoMonochromaticTriangle
      (labeledNeighborhoodThreeColoringOfCard c hc delta root hcard) :=
  labeledNeighborhoodThreeColoring_good c hc delta root _

/-- Canonical labeled version obtained directly from a degree equality. -/
noncomputable def labeledNeighborhoodThreeColoringOfDegree
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (hdegree : colorDegree c delta root = n) :
    EdgeColoring (Fin n) (Fin 3) :=
  labeledNeighborhoodThreeColoring c hc delta root
    (neighborhoodVertexEquivFinOfDegree c delta root hdegree)

/-- The degree-indexed labeled version is triangle-free. -/
theorem labeledNeighborhoodThreeColoringOfDegree_good
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (hdegree : colorDegree c delta root = n) :
    NoMonochromaticTriangle
      (labeledNeighborhoodThreeColoringOfDegree c hc delta root hdegree) :=
  labeledNeighborhoodThreeColoring_good c hc delta root _

#print axioms R4333.neighborhoodThreeColoring_good
#print axioms R4333.labeledNeighborhoodThreeColoring_good
#print axioms R4333.labeledNeighborhoodThreeColoringOfCard_good
#print axioms R4333.labeledNeighborhoodThreeColoringOfDegree_good

end R4333
