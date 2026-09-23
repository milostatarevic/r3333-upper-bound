import PricingIntegration.SeedCensusData

namespace PricingIntegration.SeedCensus
open PricingIntegration.SeedBinding
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def eraseY : Boundary → Boundary
  | .inl (p,_) => .inl (p,0)
  | .inr (.inl (p,d,_)) => .inr (.inl (p,d,0))
  | .inr (.inr (.inl (p,b,_))) => .inr (.inr (.inl (p,b,0)))
  | .inr (.inr (.inr (p,b,_))) => .inr (.inr (.inr (p,b,0)))

theorem eraseY_fields (p : Boundary) :
    pair (eraseY p) = pair p ∧ omitted (eraseY p) = omitted p ∧
    size (eraseY p) = size p ∧ yRole (eraseY p) = yRole p := by
  rcases p with ⟨p,y⟩ | ⟨p,d,y⟩ | ⟨p,b,y⟩ | ⟨p,b,y⟩ <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- The physical role maps depend only on shape, pair and omission. Selecting
the eventual Y completion changes no physical identification. -/
theorem metadata_maps_eraseY : ∀ (p : Boundary) (s : Fin 3) (a : Fin 16),
    (metadata (index p)).maps s a = (metadata (index (eraseY p))).maps s a := by decide +kernel

theorem anchorSource_eraseY : ∀ (p : Boundary) (a : Fin 5),
    anchorSource p a = anchorSource (eraseY p) a := by decide +kernel

/-- Star and nonstar four-anchors use the same physical colored path in S.
Their Y reference roles differ, as required by the two graph orbits. -/
theorem star_plane_same_anchor : ∀ (p : Fin 6) (b : Fin 5) (y : Fin 6) (z : Fin 2) (a : Fin 4),
    anchorSource (.inr (.inr (.inl (p,b,y)))) (Fin.castLE (by decide) a) =
    anchorSource (.inr (.inr (.inr (p,b,z)))) (Fin.castLE (by decide) a) := by decide +kernel

#print axioms metadata_maps_eraseY
#print axioms star_plane_same_anchor
end PricingIntegration.SeedCensus
