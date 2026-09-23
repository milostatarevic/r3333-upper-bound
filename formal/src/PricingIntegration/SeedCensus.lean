import PricingIntegration.SeedCensusData
import PricingIntegration.PhysicalGluing

namespace PricingIntegration.SeedCensus
open Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open PricingIntegration.SeedBinding PricingG.Completion72
open PricingC PricingC.PairTables PricingC.AnchorTables
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- All four strata map to an actual stored seed with the exact required
state triple. Its type includes all36+180+180+60 parameter combinations. -/
theorem states_exact : ∀ p : Boundary,
    (metadata (index p)).states 0 = representativeX (pair p) ∧
    (metadata (index p)).states 1 = representativeS (pair p) ∧
    (metadata (index p)).states 2 = yState p := by decide +kernel

theorem x_map_exact : ∀ (p : Boundary) (a : Fin 16),
    (metadata (index p)).maps 0 a = some ⟨a.val + 1,by omega⟩ := by decide +kernel

theorem s_map_exact : ∀ (p : Boundary) (a : Fin 16),
    (metadata (index p)).maps 1 a = canonicalSMap p a := by decide +kernel

theorem s_present_exact : ∀ (p : Boundary) (a : Fin 16),
    ((metadata (index p)).maps 1 a).isSome = true ↔ omitted p ≠ some a := by decide +kernel

theorem scope_maps_injective : ∀ (p : Boundary) (s : Fin 3) (a b : Fin 16),
    ((metadata (index p)).maps s a).isSome = true →
    (metadata (index p)).maps s a = (metadata (index p)).maps s b → a = b := by decide +kernel

theorem y_map_complete : ∀ (p : Boundary) (v : Vertex),
    (∃ a : Fin 16, (metadata (index p)).maps 2 a = some v) ↔
      17 ≤ v.val ∧ v.val ≤ 32 := by decide +kernel

theorem anchor_overlap : ∀ (p : Boundary) (a : Fin 5), a.val < size p →
    (metadata (index p)).maps 2 (yRole p a) =
      (metadata (index p)).maps 1 (anchorSource p a) ∧
    ((metadata (index p)).maps 1 (anchorSource p a)).isSome = true := by decide +kernel

theorem anchor_source_injective : ∀ (p : Boundary) (a b : Fin 5),
    a.val < size p → b.val < size p → anchorSource p a = anchorSource p b → a = b := by decide +kernel

theorem anchor_source_colors : ∀ (p : Boundary) (a b : Fin 5),
    a.val < size p → b.val < size p → a ≠ b →
    scopePalette 1 (referenceColor (representativeS (pair p))
      (anchorSource p a) (anchorSource p b)) = canonicalColor p a b := by decide +kernel

theorem star_fifth : ∀ (p : Boundary), isStar p = true →
    (metadata (index p)).maps 2 (generators 4) = some 21 ∧
      ¬ InS (metadata (index p)) 21 := by decide +kernel

theorem b_roles_exact : ∀ (p : Fin 6) (v : Fin 16),
    (∃ a : Fin 5, bRoles p a = v) ↔
      v ≠ 0 ∧ referenceColor (representativeS p) 0 v = 1 := by decide +kernel

theorem d_roles_exact : ∀ (p : Fin 6) (v : Fin 16),
    (∃ a : Fin 5, dRoles p a = v) ↔
      v ≠ 0 ∧ referenceColor (representativeS p) 0 v = 2 := by decide +kernel

#print axioms states_exact
#print axioms s_map_exact
#print axioms anchor_source_colors
end PricingIntegration.SeedCensus
