import R4333Lean.NeighborhoodThreeColor
import R4333Lean.K15Catalogue

/-!
# Catalogue witnesses for the attaching neighbourhoods

This is the semantic bridge from an actual four-colouring to the finite
critical K15/K16 templates.  It makes no overlap-normal-form or SAT claim.
-/

namespace R4333

open Finset

/-- The induced neighbourhood colouring is weakly isomorphic to any chosen
`Fin n` labeling of it. -/
noncomputable def neighborhoodToLabeledWeakEquiv
    {V : Type*} [Fintype V] [DecidableEq V] {n : Nat}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (e : Fin n ≃ NeighborhoodVertex c delta root) :
    WeakColorEquiv
      (neighborhoodThreeColoring c hc delta root)
      (labeledNeighborhoodThreeColoring c hc delta root e) where
  vertex := e.symm
  colors := neighborhoodColorEquivFin3 delta
  map_color := by
    intro x y hxy
    change neighborhoodColorEquivFin3 delta
        (neighborhoodThreeColoring c hc delta root x y) =
      neighborhoodColorEquivFin3 delta
        (neighborhoodThreeColoring c hc delta root
          (e (e.symm x)) (e (e.symm y)))
    simp

/-- A complete labeled catalogue classifies the actual, unlabeled
monochromatic neighbourhood. -/
theorem neighborhood_classified_of_degree
    {V : Type*} [Fintype V] [DecidableEq V] {n : Nat}
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (hdegree : colorDegree c delta root = n)
    (catalogue : List (EdgeColoring (Fin n) ThreeColor))
    (hcomplete : ThreeColorCatalogueComplete n catalogue) :
    ∃ t ∈ catalogue,
      Nonempty (WeakColorEquiv
        (neighborhoodThreeColoring c hc delta root) t) := by
  let e := neighborhoodVertexEquivFinOfDegree c delta root hdegree
  let d := labeledNeighborhoodThreeColoring c hc delta root e
  have hd : NoMonochromaticTriangle d :=
    labeledNeighborhoodThreeColoring_good c hc delta root e
  obtain ⟨t, ht, ⟨f⟩⟩ := hcomplete.2 d hd
  exact ⟨t, ht, ⟨(neighborhoodToLabeledWeakEquiv c hc delta root e).trans f⟩⟩

/-- Exact critical-template alternative for a monochromatic neighbourhood
whose order is known to lie between 15 and 16. -/
def CriticalNeighborhoodWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V) : Prop :=
  (∃ _hdegree : colorDegree c delta root = 15,
    ∃ t ∈ k15CriticalCatalogue,
      Nonempty (WeakColorEquiv
        (neighborhoodThreeColoring c hc delta root) t)) ∨
  (∃ _hdegree : colorDegree c delta root = 16,
    ∃ t ∈ k16CriticalCatalogue,
      Nonempty (WeakColorEquiv
        (neighborhoodThreeColoring c hc delta root) t))

theorem criticalNeighborhoodWitness_of_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (root : V)
    (hlower : 15 ≤ colorDegree c delta root)
    (hupper : colorDegree c delta root ≤ 16)
    (h15 : ThreeColorCatalogueComplete 15 k15CriticalCatalogue)
    (h16 : ThreeColorCatalogueComplete 16 k16CriticalCatalogue) :
    CriticalNeighborhoodWitness c hc delta root := by
  have hdegree : colorDegree c delta root = 15 ∨
      colorDegree c delta root = 16 := by omega
  rcases hdegree with hdegree | hdegree
  · left
    exact ⟨hdegree,
      neighborhood_classified_of_degree c hc delta root hdegree
        k15CriticalCatalogue h15⟩
  · right
    exact ⟨hdegree,
      neighborhood_classified_of_degree c hc delta root hdegree
        k16CriticalCatalogue h16⟩

/-- Fully semantic Stage-B entrance: the two oriented attaching
neighbourhoods selected by the order-61 theorem both carry checked critical
template witnesses. -/
theorem existsCataloguedAttaching61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (h15 : ThreeColorCatalogueComplete 15 k15CriticalCatalogue)
    (h16 : ThreeColorCatalogueComplete 16 k16CriticalCatalogue) :
    ∃ delta : FourColor, ∃ u v : V,
      u ≠ v ∧ c u v ≠ delta ∧
      14 ≤ colorDegree c (c u v) u ∧
      15 ≤ colorDegree c delta u ∧ colorDegree c delta u ≤ 16 ∧
      15 ≤ colorDegree c delta v ∧ colorDegree c delta v ≤ 16 ∧
      3 ≤ #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ∧
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤ 13 ∧
      colorDegree c (c u v) u +
          #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) ≤
        colorDegree c delta v + 11 ∧
      #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v) + 3 ≤
        colorDegree c delta v ∧
      CriticalNeighborhoodWitness c hc delta u ∧
      CriticalNeighborhoodWitness c hc delta v := by
  obtain ⟨delta, u, v, huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus⟩ :=
    existsAttaching61_oriented hcard c hc
  have huCatalogue := criticalNeighborhoodWitness_of_bounds
    c hc delta u huLower huUpper h15 h16
  have hvCatalogue := criticalNeighborhoodWitness_of_bounds
    c hc delta v hvLower hvUpper h15 h16
  exact ⟨delta, u, v, huv, hedge, hgamma, huLower, huUpper,
    hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
    huCatalogue, hvCatalogue⟩

#print axioms R4333.neighborhood_classified_of_degree
#print axioms R4333.criticalNeighborhoodWitness_of_bounds
#print axioms R4333.existsCataloguedAttaching61

end R4333
