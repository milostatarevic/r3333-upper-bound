import PricingIntegration.SeedCensus

namespace PricingIntegration.SeedCensus
open Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open PricingIntegration PricingIntegration.SeedBinding PricingG.Completion72
open PricingC PricingC.PairTables PricingC.AnchorTables
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The root colors assigned by the canonical S embedding are exactly its
three fixed reference palette colors; the marked vertex is never in S. -/
theorem s_physical_tags : ∀ (p : Boundary) (a : Fin 16),
    ((metadata (index p)).maps 1 a).isSome = true →
    physicalTag (((metadata (index p)).maps 1 a).getD 0) =
      if a = 0 then physicalTag 0
      else (some (palette (scopePalette 1 (referenceColor (representativeS (pair p)) 0 a))),false) := by
  decide +kernel

/-- The entire X/S overlap is the common ordered five-anchor. -/
theorem sx_overlap_exact : ∀ (p : Boundary) (a b : Fin 16),
    (metadata (index p)).maps 1 a = (metadata (index p)).maps 0 b ↔
      ∃ j : Fin 5, a = generators j ∧ b = generators j := by decide +kernel

/-- The entire Y/S overlap is the retained, canonically ordered B anchor.
For a star-four seed its extra actual Y point is explicitly outside S. -/
theorem sy_overlap_exact : ∀ (p : Boundary) (a b : Fin 16),
    (metadata (index p)).maps 1 a = (metadata (index p)).maps 2 b ↔
      ∃ j : Fin 5, j.val < size p ∧ a = anchorSource p j ∧ b = yRole p j := by decide +kernel

theorem y_map_present : ∀ (p : Boundary) (a : Fin 16),
    ((metadata (index p)).maps 2 a).isSome = true := by decide +kernel

theorem xy_disjoint : ∀ (p : Boundary) (a b : Fin 16),
    (metadata (index p)).maps 0 a ≠ (metadata (index p)).maps 2 b := by decide +kernel

theorem s_root : ∀ (p : Boundary), (metadata (index p)).maps 1 0 = some 0 := by decide +kernel

#print axioms s_physical_tags
#print axioms sx_overlap_exact
#print axioms sy_overlap_exact
end PricingIntegration.SeedCensus
