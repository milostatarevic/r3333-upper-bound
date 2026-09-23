import R4333Lean.ClebschCompletionClassification
import R4333Lean.ClebschUniqueness

/-!
# From the Clebsch SRG theorem to the K16 catalogue

This file isolates the short ordinary-mathematics tail of the K16
classification.  The finite incidence certificate only has to prove that a
single colour graph is `SRG(16,5,0,2)`; constructive Clebsch uniqueness and
the checked 72-row complement exhaustion then give the two templates.
-/

namespace R4333

local instance colorGraphDecidableRel_catalogue {V C : Type*}
    [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (q : C) :
    DecidableRel (colorGraph c q).Adj := by
  intro u v
  change Decidable (u ≠ v ∧ c u v = q)
  infer_instance

/-- A good K16 colouring is classified as soon as its zero-colour graph has
the Clebsch strongly-regular parameters. -/
theorem k16_classified_of_zeroGraph_srg
    (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c)
    (hsrg : (colorGraph c (0 : ThreeColor)).IsSRGWith 16 5 0 2) :
    ∃ t ∈ k16CriticalCatalogue, Nonempty (WeakColorEquiv c t) := by
  let toUntwisted :
      colorGraph c (0 : ThreeColor) ≃g
        colorGraph k16Untwisted (0 : ThreeColor) :=
    clebschIsoK16Untwisted (colorGraph c (0 : ThreeColor)) hsrg 0
  let toCanonical :
      colorGraph c (0 : ThreeColor) ≃g canonicalClebschGraph :=
    toUntwisted.trans canonicalClebschIsoUntwisted.symm
  exact classified_of_zeroGraph_iso_canonical c hc toCanonical

/-- The general SRG endpoint implies completeness of the explicit two-entry
K16 catalogue. -/
theorem k16CriticalCatalogue_complete_of_srg
    (hsrg : ∀ (c : EdgeColoring (Fin 16) ThreeColor),
      NoMonochromaticTriangle c →
        (colorGraph c (0 : ThreeColor)).IsSRGWith 16 5 0 2) :
    ThreeColorCatalogueComplete 16 k16CriticalCatalogue := by
  constructor
  · intro t ht
    simp [k16CriticalCatalogue] at ht
    rcases ht with rfl | rfl
    · exact k16Untwisted_good
    · exact k16Twisted_good
  · intro c hc
    exact k16_classified_of_zeroGraph_srg c hc (hsrg c hc)

#print axioms R4333.k16_classified_of_zeroGraph_srg
#print axioms R4333.k16CriticalCatalogue_complete_of_srg

end R4333
