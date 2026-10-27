import PricingIntegration.FixedPhysicalNeighborhood
import PricingIntegration.ABDRootPalette

set_option autoImplicit false

namespace PricingIntegration.BActualFrame
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open PricingIntegration.FixedPhysicalNeighborhood PricingIntegration.ABDRootPalette

/-- The three other colors, in the exact increasing order used by the native
A/B/D template units. -/
def foreign (omitted : Color) : Fin 3 → Color :=
  (![![1,2,3],![0,2,3],![0,1,3],![0,1,2]] : Color → Fin 3 → Color) omitted

def foreignFn (omitted : Color) (i : Fin 3) : {q : FourColor // q ≠ palette omitted} :=
  ⟨palette (foreign omitted i),by fin_cases omitted <;> fin_cases i <;> decide⟩

private theorem foreignFn_bijective : ∀ omitted,Function.Bijective (foreignFn omitted) := by decide
noncomputable def foreignEquiv (omitted : Color) : Fin 3 ≃ {q : FourColor // q ≠ palette omitted} :=
  Equiv.ofBijective (foreignFn omitted) (foreignFn_bijective omitted)

structure Blocks (c : Host) (r : Vertex) where
  free : Fin 5 ↪ Vertex
  mType : Bool
  xType : Bool
  qType : Bool
  m : PhysicalNeighborhoodMap c r (palette 1) (R4333.k15Template mType)
  x : PhysicalNeighborhoodMap c r (palette 2) (R4333.k16Template xType)
  q : PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template qType)
  free_mem : ∀ i,free i ∈ colorNeighborhood c (palette 0) r
  m_palette : m.colors = foreignEquiv 1
  x_palette : x.colors = foreignEquiv 2
  q_palette : q.colors = foreignEquiv 3
  marked_high : q.vertex 15 ∈ Incoming c r

end PricingIntegration.BActualFrame
