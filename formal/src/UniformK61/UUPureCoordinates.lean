import UniformK61.UUSourceDefs
import UniformK61.CommonSoundness

set_option autoImplicit false
namespace UniformK61.UUPureCoordinates
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout
open UniformK61.UUSupportData
open UniformK61.UUSourceDefs

abbrev layout (p : Pair) : Layout := ⟨.D,five p⟩

theorem layout_free (p : Pair) : freeSize (layout p)=(shape p).free := by
  cases h : shape p <;> simp [freeSize,layout,five,h,CompletionC.NativeMatrices.Shape.free]

def matching (p : Pair) (v : Vertex) (u : Core.PhysicalUnit) : Prop :=
  u.positive=member p v ∧ u.u=60 ∧ u.v=v ∧ u.q=3
instance (p : Pair) (v : Vertex) (u : Core.PhysicalUnit) : Decidable (matching p v u) := by
  unfold matching;infer_instance

def membershipCovered (p : Pair) (v : Vertex) : Bool :=
  (CommonFormula.membershipFor (layout p) (leftNats p) (rightNats p)).any fun u => decide (matching p v u)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem membership_covered : ∀p : Pair,∀v : Vertex,v≠0→v≠60→membershipCovered p v=true := by
  decide +kernel

theorem matching_unit (p : Pair) (v : Vertex) (hv : v≠0) (hx : v≠60) :
    ∃u∈CommonFormula.membershipFor (layout p) (leftNats p) (rightNats p),matching p v u := by
  obtain ⟨u,hu,h⟩ := List.any_eq_true.mp (membership_covered p v hv hx)
  exact ⟨u,hu,of_decide_eq_true h⟩

theorem matched_iff (c : Host) (u : Core.PhysicalUnit) (h : Core.UnitMatches c u) :
    c u.u u.v=palette u.q ↔u.positive=true := by
  unfold Core.UnitMatches at h
  cases hb : u.positive <;> simp_all [Core.palette]


def spokeMatching (v : Vertex) (u : Core.PhysicalUnit) : Prop :=
  u.positive=true ∧ u.u=0 ∧ u.v=v ∧ u.q=rootColor v
instance (v : Vertex) (u : Core.PhysicalUnit) : Decidable (spokeMatching v u) := by
  unfold spokeMatching;infer_instance

def spokeCovered (five : Bool) (v : Vertex) : Bool :=
  (CommonFormula.spokes ⟨.D,five⟩).any fun u => decide (spokeMatching v u)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem spoke_covered : ∀five : Bool,∀v : Vertex,v≠0→spokeCovered five v=true := by decide +kernel

theorem matching_spoke (five : Bool) (v : Vertex) (hv : v≠0) :
    ∃u∈CommonFormula.spokes ⟨.D,five⟩,spokeMatching v u := by
  obtain ⟨u,hu,h⟩ := List.any_eq_true.mp (spoke_covered five v hv)
  exact ⟨u,hu,of_decide_eq_true h⟩

end UniformK61.UUPureCoordinates
