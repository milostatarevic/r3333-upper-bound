import UniformK61.BalancedAnchorPacked
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UniformK61.BalancedAnchor
open UniformK61.BalancedEncodingData

/-- Explicit two-sided inverses certify each complete sixteen-vertex map. -/
theorem chart_inverse : ∀ (k : Chart) (v : Fin 16),
  chartInverse k (chartOrder k v)=v ∧ chartOrder k (chartInverse k v)=v := by decide +kernel

theorem chart_edges : ∀ (k : Chart) (a b : Fin 16),
  R4333.k16Template (chartKind k) (chartOrder k a) (chartOrder k b) =
    stateColor (chartState k) a b := Packed.edges

/-- Successive fixed-color guards enumerate all ordered reference cycles.
The implications prune invalid prefixes without changing the quantified boundary. -/
theorem anchors_exhaustive : ∀ (t : Bool) (a b : Fin 16),
  R4333.k16Template t a b=1 → ∀ c : Fin 16,
  R4333.k16Template t a c=2 → R4333.k16Template t b c=1 → ∀ d : Fin 16,
  R4333.k16Template t a d=2 → R4333.k16Template t b d=2 →
  R4333.k16Template t c d=1 → ∀ e : Fin 16,
  R4333.k16Template t a e=1 → R4333.k16Template t b e=2 →
  R4333.k16Template t c e=2 → R4333.k16Template t d e=1 →
  chartKind (chartFor t a b c)=t ∧
  chartOrder (chartFor t a b c) 0=a ∧ chartOrder (chartFor t a b c) 1=b ∧
  chartOrder (chartFor t a b c) 2=c ∧ chartOrder (chartFor t a b c) 3=d ∧
  chartOrder (chartFor t a b c) 4=e := by decide +kernel

theorem anchor_injective_check : ∀ (t : Bool) (center : Fin 16) (a b : Fin 5),
  anchor t center a=anchor t center b → a=b := by decide +kernel

theorem anchor_colors : ∀ (t : Bool) (center : Fin 16) (a b : Fin 5),
  a≠b → R4333.k16Template t (anchor t center a) (anchor t center b)=reference a b := by decide +kernel

theorem anchor_members : ∀ (t : Bool) (center v : Fin 16),
  (v≠center ∧ R4333.k16Template t center v=0) ↔ ∃ a : Fin 5,anchor t center a=v := by decide +kernel

theorem chart_sizes : coverage.size=320 ∧ inverseCodes.size=320 ∧
  ∀ k : Chart, (chartRow k).state<6 ∧ (chartRow k).order.size=16 := by decide +kernel

#print axioms chart_inverse
#print axioms chart_edges
#print axioms anchors_exhaustive
end UniformK61.BalancedAnchor
