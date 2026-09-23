import PricingIntegration.SeedBinding
import PricingIntegration.SeedPhysical
import Ramsey61.CAnchorGeometry

namespace PricingIntegration.SeedBinding
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open Ramsey61.CConcreteFamily Ramsey61.CPhysicalNormalization

/-- Exact456 consumer: compatible physical scopes give one whole-host
permutation, every stored positive and negative unit, and the full concrete
CNF valuation. No seed-unit or encoding assumption remains. -/
theorem partial_geometry_supplies_concrete_case (c : Host)
    (hc : NoMonochromaticTriangle c) (selectors : SelectorX c)
    (hroot : RootConditions c) (hmarked : 15 ≤ colorDegree c (palette 2) 33)
    (i : Fin 456) (g : PartialGeometry c (metadata i)) :
    ∃ e : Vertex ≃ Vertex,
      RootConditions (relabel c e (Equiv.refl _)) ∧
      SeedMatches (relabel c e (Equiv.refl _)) i ∧
      DenseCounter.FormulaSat (baseValuation (relabel c e (Equiv.refl _))) (concreteFamily i) := by
  obtain ⟨e,he,hg,hbase⟩ := partial_geometry_gives_geometry c hc selectors hroot hmarked (metadata i) g
  have hs := geometry_supplies_seed (relabel c e (Equiv.refl _)) i hg
  exact ⟨e,hg.root,hs,(DenseCounter.formulaSat_append _ _ _).mpr
    ⟨hbase,seed_matches_satisfies _ i hs⟩⟩

/-- This explicitly exposes the one unfinished C task for the pricing probe:
construct compatible physical scope maps into the finite metadata census.
The declaration below is a proved implication, not an asserted cover. -/
theorem compatible_physical_census_implies_normalized_cover
    (cover : ∀ c : Host, NoMonochromaticTriangle c → SelectorX c →
      RootConditions c → 15 ≤ colorDegree c (palette 2) 33 →
      ∃ i : Fin 456, Nonempty (PartialGeometry c (metadata i))) :
    NormalizedSeedCover := by
  intro c hc selectors hroot hmarked
  obtain ⟨i,⟨g⟩⟩ := cover c hc selectors hroot hmarked
  obtain ⟨e,hr,hs,_⟩ := partial_geometry_supplies_concrete_case c hc selectors hroot hmarked i g
  exact ⟨e,Equiv.refl _,i,hr,hs⟩

#print axioms partial_geometry_supplies_concrete_case
#print axioms compatible_physical_census_implies_normalized_cover

/-- Orient the two complete root blocks first, preserving one global
coloring and recording the palette permutation. The finite456 construction
therefore needs only555,554,545, never a separate455 seed stratum. -/
theorem three_anchor_census_implies_normalized_cover
    (cover : ∀ c : Host, NoMonochromaticTriangle c → SelectorX c →
      RootConditions c → 15 ≤ colorDegree c (palette 2) 33 →
      CAnchorGeometry.ThreeAnchorShapes c →
      ∃ i : Fin 456, Nonempty (PartialGeometry c (metadata i))) :
    NormalizedSeedCover := by
  intro c hc selectors hroot hmarked
  obtain ⟨e₀,σ,hc',hs',hr',hm',hshape⟩ :=
    CAnchorGeometry.normalized_host_has_three_anchor_shapes c hc selectors hroot hmarked
  obtain ⟨i,⟨g⟩⟩ := cover _ hc' hs' hr' hm' hshape
  obtain ⟨e₁,hr,hs,_⟩ := partial_geometry_supplies_concrete_case _ hc' hs' hr' hm' i g
  exact ⟨e₁.trans e₀,σ,i,hr,hs⟩

#print axioms three_anchor_census_implies_normalized_cover
end PricingIntegration.SeedBinding
