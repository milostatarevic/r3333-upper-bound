import R4333Lean.CataloguedNeighborhood

/-!
# Semantic overlaps between two catalogued neighbourhoods

Two monochromatic neighbourhoods of the same four-colour may overlap.  A
weak colour equivalence from each neighbourhood to a critical template sends
the common vertices injectively into both templates.  The two template
colourings agree on those images after applying the relative permutation of
their three colours.

This file records only that semantic fact.  It makes no choice of overlap
normal form and contains no finite enumeration.
-/

namespace R4333

open Finset

/-- The vertices lying simultaneously in the `delta`-neighbourhoods of two
roots. -/
abbrev CommonNeighborhoodVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (leftRoot rightRoot : V) :=
  {x : V // x ∈ colorNeighborhood c delta leftRoot ∩
    colorNeighborhood c delta rightRoot}

/-- Forget the right-neighbourhood membership of a common vertex. -/
def commonNeighborhoodToLeft
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (leftRoot rightRoot : V) :
    CommonNeighborhoodVertex c delta leftRoot rightRoot ↪
      NeighborhoodVertex c delta leftRoot where
  toFun x := ⟨x.1, (Finset.mem_inter.mp x.2).1⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : NeighborhoodVertex c delta leftRoot ↦ z.1) hxy

/-- Forget the left-neighbourhood membership of a common vertex. -/
def commonNeighborhoodToRight
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (leftRoot rightRoot : V) :
    CommonNeighborhoodVertex c delta leftRoot rightRoot ↪
      NeighborhoodVertex c delta rightRoot where
  toFun x := ⟨x.1, (Finset.mem_inter.mp x.2).2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : NeighborhoodVertex c delta rightRoot ↦ z.1) hxy

/-- The cardinality of the common-vertex subtype is the ordinary finite-set
intersection cardinality. -/
theorem commonNeighborhoodVertex_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (leftRoot rightRoot : V) :
    Fintype.card (CommonNeighborhoodVertex c delta leftRoot rightRoot) =
      #(colorNeighborhood c delta leftRoot ∩
        colorNeighborhood c delta rightRoot) := by
  change Fintype.card
      ↑(colorNeighborhood c delta leftRoot ∩
        colorNeighborhood c delta rightRoot) = _
  exact Fintype.card_coe _

/-- A common set of labeled vertices embedded in two three-colour templates.
`relativeColors` converts the left template's colour labels to the right
template's labels. -/
structure TemplateOverlap {L R X : Type*}
    (left : EdgeColoring L ThreeColor)
    (right : EdgeColoring R ThreeColor) where
  leftVertex : X ↪ L
  rightVertex : X ↪ R
  relativeColors : ThreeColor ≃ ThreeColor
  compatible : ∀ x y, x ≠ y →
    relativeColors (left (leftVertex x) (leftVertex y)) =
      right (rightVertex x) (rightVertex y)

namespace TemplateOverlap

/-- Relabel the abstract common set without changing either template image
or the relative colour permutation. -/
def relabel {L R X Y : Type*}
    {left : EdgeColoring L ThreeColor}
    {right : EdgeColoring R ThreeColor}
    (o : TemplateOverlap left right (X := X)) (e : Y ≃ X) :
    TemplateOverlap left right (X := Y) where
  leftVertex := e.toEmbedding.trans o.leftVertex
  rightVertex := e.toEmbedding.trans o.rightVertex
  relativeColors := o.relativeColors
  compatible := by
    intro x y hxy
    exact o.compatible (e x) (e y) (e.injective.ne hxy)

end TemplateOverlap

/-- The actual common vertices, transported into two templates by the two
chosen weak colour equivalences. -/
noncomputable def commonNeighborhoodTemplateOverlap
    {V L R : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (leftRoot rightRoot : V)
    (left : EdgeColoring L ThreeColor)
    (right : EdgeColoring R ThreeColor)
    (leftEquiv : WeakColorEquiv
      (neighborhoodThreeColoring c hc delta leftRoot) left)
    (rightEquiv : WeakColorEquiv
      (neighborhoodThreeColoring c hc delta rightRoot) right) :
    TemplateOverlap left right
      (X := CommonNeighborhoodVertex c delta leftRoot rightRoot) where
  leftVertex :=
    (commonNeighborhoodToLeft c delta leftRoot rightRoot).trans
      leftEquiv.vertex.toEmbedding
  rightVertex :=
    (commonNeighborhoodToRight c delta leftRoot rightRoot).trans
      rightEquiv.vertex.toEmbedding
  relativeColors := leftEquiv.colors.symm.trans rightEquiv.colors
  compatible := by
    intro x y hxy
    let xl := commonNeighborhoodToLeft c delta leftRoot rightRoot x
    let yl := commonNeighborhoodToLeft c delta leftRoot rightRoot y
    let xr := commonNeighborhoodToRight c delta leftRoot rightRoot x
    let yr := commonNeighborhoodToRight c delta leftRoot rightRoot y
    have hxl : xl ≠ yl :=
      (commonNeighborhoodToLeft c delta leftRoot rightRoot).injective.ne hxy
    have hxr : xr ≠ yr :=
      (commonNeighborhoodToRight c delta leftRoot rightRoot).injective.ne hxy
    have hleft := leftEquiv.map_color xl yl hxl
    have hright := rightEquiv.map_color xr yr hxr
    have hinduced :
        neighborhoodThreeColoring c hc delta leftRoot xl yl =
          neighborhoodThreeColoring c hc delta rightRoot xr yr := by
      apply Subtype.ext
      exact (neighborhoodThreeColoring_coe_apply_of_ne
        c hc delta leftRoot xl yl hxl).trans
        (neighborhoodThreeColoring_coe_apply_of_ne
          c hc delta rightRoot xr yr hxr).symm
    change rightEquiv.colors
        (leftEquiv.colors.symm
          (left (leftEquiv.vertex xl) (leftEquiv.vertex yl))) =
      right (rightEquiv.vertex xr) (rightEquiv.vertex yr)
    calc
      rightEquiv.colors
          (leftEquiv.colors.symm
            (left (leftEquiv.vertex xl) (leftEquiv.vertex yl))) =
        rightEquiv.colors
          (neighborhoodThreeColoring c hc delta leftRoot xl yl) := by
            congr 1
            simpa using congrArg leftEquiv.colors.symm hleft.symm
      _ = rightEquiv.colors
          (neighborhoodThreeColoring c hc delta rightRoot xr yr) :=
        congrArg rightEquiv.colors hinduced
      _ = right (rightEquiv.vertex xr) (rightEquiv.vertex yr) := hright

/-- Label an intersection of known cardinality `k` by `Fin k`. -/
noncomputable def commonNeighborhoodVertexEquivFin
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (c : EdgeColoring V FourColor) (delta : FourColor) (leftRoot rightRoot : V)
    (hcard : #(colorNeighborhood c delta leftRoot ∩
      colorNeighborhood c delta rightRoot) = k) :
    Fin k ≃ CommonNeighborhoodVertex c delta leftRoot rightRoot :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, commonNeighborhoodVertex_card, hcard])

/-- The overlap extracted from two catalogue witnesses, with its common
vertices canonically labeled by `Fin k` from an intersection-cardinality
equality. -/
noncomputable def labeledCommonNeighborhoodTemplateOverlap
    {V L R : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (leftRoot rightRoot : V)
    (left : EdgeColoring L ThreeColor)
    (right : EdgeColoring R ThreeColor)
    (hcard : #(colorNeighborhood c delta leftRoot ∩
      colorNeighborhood c delta rightRoot) = k)
    (leftEquiv : WeakColorEquiv
      (neighborhoodThreeColoring c hc delta leftRoot) left)
    (rightEquiv : WeakColorEquiv
      (neighborhoodThreeColoring c hc delta rightRoot) right) :
    TemplateOverlap left right (X := Fin k) :=
  (commonNeighborhoodTemplateOverlap c hc delta leftRoot rightRoot
    left right leftEquiv rightEquiv).relabel
      (commonNeighborhoodVertexEquivFin c delta leftRoot rightRoot hcard)

/-- On every distinct pair of labeled common vertices, the two template edge
colours agree after the relative three-colour permutation. -/
theorem labeledCommonNeighborhoodTemplateOverlap_compatible
    {V L R : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (leftRoot rightRoot : V)
    (left : EdgeColoring L ThreeColor)
    (right : EdgeColoring R ThreeColor)
    (hcard : #(colorNeighborhood c delta leftRoot ∩
      colorNeighborhood c delta rightRoot) = k)
    (leftEquiv : WeakColorEquiv
      (neighborhoodThreeColoring c hc delta leftRoot) left)
    (rightEquiv : WeakColorEquiv
      (neighborhoodThreeColoring c hc delta rightRoot) right)
    (i j : Fin k) (hij : i ≠ j) :
    let o := labeledCommonNeighborhoodTemplateOverlap c hc delta
      leftRoot rightRoot left right hcard leftEquiv rightEquiv
    o.relativeColors (left (o.leftVertex i) (o.leftVertex j)) =
      right (o.rightVertex i) (o.rightVertex j) := by
  exact (labeledCommonNeighborhoodTemplateOverlap c hc delta
    leftRoot rightRoot left right hcard leftEquiv rightEquiv).compatible i j hij

#print axioms R4333.commonNeighborhoodVertex_card
#print axioms R4333.commonNeighborhoodTemplateOverlap
#print axioms R4333.commonNeighborhoodVertexEquivFin
#print axioms R4333.labeledCommonNeighborhoodTemplateOverlap_compatible

end R4333
