import UniformK61.UUChecks
import UniformK61.UUFiniteBridge
set_option autoImplicit false
namespace UniformK61.UUFiniteCover
open Ramsey61 UniformK61.UUSupportData UniformK61.UUSourceDefs
open UniformK61.UUBridgeData

/-- Exhaustive finite normalization of all 66 normalized support pairs and
600 catalogued matrices, for either marked-neighborhood kind. -/
theorem finite_bridge_sound {q : Bool} {p : Pair} {i : Fin 600} {c : Host}
 (w : SourceWitness q p i c) :
 ∃j : MarkedUU.Leaf,∃v : DenseCounter.Valuation,
 DenseCounter.FormulaSat v (MarkedUU.formula q j) := by
 obtain ⟨v,hv⟩:=UUFiniteBridge.finite_bridge_sound_of_residual w (UUChecks.residual_all q p i)
 exact ⟨UUData.leaf (target p i),v,hv⟩

#print axioms finite_bridge_sound
end UniformK61.UUFiniteCover
