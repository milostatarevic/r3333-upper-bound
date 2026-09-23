import R4333Lean.K16CommonCertificate
import R4333Lean.K16CatalogueFromSRG
import R4333Lean.Attaching61Reduction

/-!
# Fully checked critical K15 and K16 catalogues

This file joins the independently checked incidence leaves, constructive
Clebsch uniqueness, the 72-row complement exhaustion, and the K15 extension
and deletion argument.  No catalogue completeness premise remains.
-/

namespace R4333

/-- Every good three-colouring of K16 is weakly isomorphic to one of the two
explicit critical templates. -/
theorem k16CriticalCatalogue_complete :
    ThreeColorCatalogueComplete 16 k16CriticalCatalogue :=
  k16CriticalCatalogue_complete_of_srg fun c hc ↦
    k16_colorGraph_isSRG c hc (0 : ThreeColor)

/-- Every good three-colouring of K15 is weakly isomorphic to the fixed
deletion of one of the two K16 templates. -/
theorem k15CriticalCatalogue_complete :
    ThreeColorCatalogueComplete 15 k15CriticalCatalogue :=
  k15CriticalCatalogue_complete_of_k16 k16CriticalCatalogue_complete

/-- Unconditional semantic entrance to the finite attaching obstruction. -/
theorem exists_cataloguedAttachingConfiguration61_checked
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ delta : FourColor, ∃ u v : Fin 61,
      CataloguedAttachingConfiguration c hc delta u v :=
  exists_cataloguedAttachingConfiguration61 c hc
    k15CriticalCatalogue_complete k16CriticalCatalogue_complete

/-- An auxiliary sufficient-condition theorem using the attaching obstruction.
The complete endpoint `PricingIntegration.NativeWholeProof.ramsey61` instead
uses the profile reduction and its explicit native computational premise. -/
theorem noFourColoring_61_of_checkedAttachingObstruction
    (hobstruction : CataloguedAttachingObstruction61) :
    ¬ HasFourColoring 61 :=
  noFourColoring_61_of_cataloguedAttachingObstruction
    k15CriticalCatalogue_complete k16CriticalCatalogue_complete hobstruction

#print axioms R4333.k16CriticalCatalogue_complete
#print axioms R4333.k15CriticalCatalogue_complete
#print axioms R4333.exists_cataloguedAttachingConfiguration61_checked
#print axioms R4333.noFourColoring_61_of_checkedAttachingObstruction

end R4333
