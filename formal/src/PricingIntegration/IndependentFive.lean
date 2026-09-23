import R4333Lean.CriticalCatalogues
import R4333Lean.CriticalTemplateShadowLaws

namespace PricingIntegration.IndependentFive
open R4333

theorem neighborhood_image
    {c d : EdgeColoring (Fin 16) ThreeColor} (e : WeakColorEquiv c d)
    (q : ThreeColor) (v : Fin 16) :
    (colorNeighborhood c q v).image e.vertex =
      colorNeighborhood d (e.colors q) (e.vertex v) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hne, hq⟩ := (mem_colorNeighborhood c q v x).mp hx
    apply (mem_colorNeighborhood _ _ _ _).mpr
    exact ⟨e.vertex.injective.ne hne,
      (e.map_color v x hne.symm).symm.trans (congrArg e.colors hq)⟩
  · intro hy
    obtain ⟨hne, hq⟩ := (mem_colorNeighborhood _ _ _ _).mp hy
    have hxne : e.vertex.symm y ≠ v := by
      intro h
      apply hne
      simpa using congrArg e.vertex h
    refine Finset.mem_image.mpr ⟨e.vertex.symm y, ?_, e.vertex.apply_symm_apply y⟩
    apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨hxne, e.colors.injective ?_⟩
    calc
      e.colors (c v (e.vertex.symm y)) = d (e.vertex v) y := by
        simpa using e.map_color v (e.vertex.symm y) hxne.symm
      _ = e.colors q := hq

theorem independent_image
    {c d : EdgeColoring (Fin 16) ThreeColor} (e : WeakColorEquiv c d)
    (q : ThreeColor) (S : Finset (Fin 16))
    (hS : IsColorIndependentSet c q S) :
    IsColorIndependentSet d (e.colors q) (S.image e.vertex) := by
  intro x hx y hy hxy hq
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
  have hne : x₀ ≠ y₀ := fun h => hxy (congrArg e.vertex h)
  apply hS x₀ hx₀ y₀ hy₀ hne
  exact e.colors.injective ((e.map_color x₀ y₀ hne).trans hq)

/-- Pulling back the template center through the exact catalogue equivalence
preserves both the physical vertices and the selected color. -/
theorem unique_center_of_equiv
    (c : EdgeColoring (Fin 16) ThreeColor) (twisted : Bool)
    (e : WeakColorEquiv c (k16Template twisted))
    (q : ThreeColor) (S : Finset (Fin 16))
    (hcard : S.card = 5) (hS : IsColorIndependentSet c q S) :
    ∃! v : Fin 16, S = colorNeighborhood c q v := by
  classical
  obtain ⟨v, hv, hu⟩ := k16Template_maxIndependentSet_unique_shadow
    twisted (e.colors q) (S.image e.vertex)
    (by simpa only [Finset.card_image_of_injective _ e.vertex.injective] using hcard)
    (independent_image e q S hS)
  refine ⟨e.vertex.symm v, ?_, ?_⟩
  · apply Finset.image_injective e.vertex.injective
    rw [neighborhood_image]
    simpa using hv
  · intro w hw
    have hw' := congrArg (Finset.image e.vertex) hw
    rw [neighborhood_image] at hw'
    have h := hu (e.vertex w) hw'
    exact e.vertex.injective (by simpa using h)

/-- Every independent five-set in any good three-coloring on sixteen vertices
is the neighborhood of a unique center. Catalogue completeness is discharged
by the existing checked classification, not supplied as a new premise. -/
theorem good_K16_independent_five_unique_center
    (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (q : ThreeColor)
    (S : Finset (Fin 16)) (hcard : S.card = 5)
    (hS : IsColorIndependentSet c q S) :
    ∃! v : Fin 16, S = colorNeighborhood c q v := by
  obtain ⟨t, ht, ⟨e⟩⟩ := k16CriticalCatalogue_complete.2 c hc
  simp only [k16CriticalCatalogue, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact unique_center_of_equiv c false e q S hcard hS
  · exact unique_center_of_equiv c true e q S hcard hS

#print axioms good_K16_independent_five_unique_center
end PricingIntegration.IndependentFive
