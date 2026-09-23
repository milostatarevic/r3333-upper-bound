import PricingIntegration.AlignedGlue
import PricingIntegration.CSeedConsumer
import PricingC.PhysicalCensus
import Ramsey61.Conditional

set_option autoImplicit false

namespace PricingIntegration.CComplete
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open Ramsey61.CConcreteFamily PricingIntegration.SeedBinding PricingIntegration.SeedCensus

/-- Full geometric coverage of the exact456 stored C seeds, including one
global vertex/palette relabeling. Every mathematical and finite-table premise
of the coverage construction is discharged. No UNSAT result is used here. -/
theorem normalized_seed_cover : NormalizedSeedCover := by
  apply three_anchor_census_implies_normalized_cover
  intro c hc selectors hroot hmarked hshape
  obtain ⟨b,⟨triple⟩⟩ := PricingC.actual_C_supplies_aligned_triple c hc hroot hmarked hshape
  exact ⟨index b,aligned_triple_supplies_partial_geometry c b triple hroot⟩

/-- The original physical_C_to_CNF mathematical bridge is now a proved
theorem for the exact retained family. The sole computational exclusion is
kept separate in the following theorem. -/
theorem physical_C_to_exact_family (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (witness : CExteriorWitness c) :
    ∃ i : Fin 456, Satisfiable (concreteFamily i) :=
  physical_C_to_concrete_family normalized_seed_cover c hc selectors witness

theorem C_exterior_excluded
    (all456_unsat : ∀ i : Fin 456, ¬Satisfiable (concreteFamily i))
    (c : Host) (hc : NoMonochromaticTriangle c) (selectors : SelectorX c)
    (witness : CExteriorWitness c) : False := by
  obtain ⟨i,hi⟩ := physical_C_to_exact_family c hc selectors witness
  exact all456_unsat i hi

#check normalized_seed_cover
#check physical_C_to_exact_family
#check C_exterior_excluded
#print axioms normalized_seed_cover
#print axioms physical_C_to_exact_family
#print axioms C_exterior_excluded
end PricingIntegration.CComplete
