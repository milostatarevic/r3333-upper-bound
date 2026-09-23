import R4333Lean.CataloguedNeighborhood

/-!
# An alternative attaching-obstruction reduction for order 61

This file gives a sufficient condition for the upper bound in terms of
catalogued attaching configurations. Its obstruction remains an explicit
parameter of this auxiliary composition theorem. The complete endpoint
`PricingIntegration.NativeWholeProof.ramsey61` uses the profile reduction.
-/

namespace R4333

open Finset

/-- The exact catalogued attaching configuration forced inside a hypothetical
good four-colouring of K61. -/
def CataloguedAttachingConfiguration
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (u v : V) : Prop :=
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
  CriticalNeighborhoodWitness c hc delta v

/-- The obstruction parameter for the auxiliary attaching reduction:
no good K61 four-colouring contains the forced pair of catalogued critical
neighbourhoods. This definition is not an axiom or a premise of the final
profile-based endpoint. -/
def CataloguedAttachingObstruction61 : Prop :=
  ∀ (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (u v : Fin 61),
      CataloguedAttachingConfiguration c hc delta u v → False

theorem exists_cataloguedAttachingConfiguration61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (h15 : ThreeColorCatalogueComplete 15 k15CriticalCatalogue)
    (h16 : ThreeColorCatalogueComplete 16 k16CriticalCatalogue) :
    ∃ delta : FourColor, ∃ u v : Fin 61,
      CataloguedAttachingConfiguration c hc delta u v := by
  obtain ⟨delta, u, v, huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
      huCatalogue, hvCatalogue⟩ :=
    existsCataloguedAttaching61 (by simp) c hc h15 h16
  exact ⟨delta, u, v, huv, hedge, hgamma, huLower, huUpper,
    hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
    huCatalogue, hvCatalogue⟩

/-- The catalogue-completeness statements and the attaching obstruction
suffice for the upper bound in this alternative composition. -/
theorem noFourColoring_61_of_cataloguedAttachingObstruction
    (h15 : ThreeColorCatalogueComplete 15 k15CriticalCatalogue)
    (h16 : ThreeColorCatalogueComplete 16 k16CriticalCatalogue)
    (hobstruction : CataloguedAttachingObstruction61) :
    ¬ HasFourColoring 61 := by
  rintro ⟨c, hc⟩
  obtain ⟨delta, u, v, hconfig⟩ :=
    exists_cataloguedAttachingConfiguration61 c hc h15 h16
  exact hobstruction c hc delta u v hconfig

#print axioms R4333.exists_cataloguedAttachingConfiguration61
#print axioms R4333.noFourColoring_61_of_cataloguedAttachingObstruction

end R4333
