import UniformK60.BalancedHost

set_option autoImplicit false
namespace UniformK60.BalancedHost
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK61.BalancedEncodingData

@[simp] theorem cast_anchorIndex {c1 : Bool} {o : Owner} {s : Scope c1}
    (h : AnchorReady o s) (a : Fin 5) :
    Fin.castLE (own_le s) (anchorIndex h a) = anchor (ownKind o s) (center16 s) a :=
  Fin.ext rfl

theorem anchorIndex_injective {c1 : Bool} {o : Owner} {s : Scope c1}
    (h : AnchorReady o s) : Function.Injective (anchorIndex h) := by
  intro a b he
  have hh := congrArg (Fin.castLE (own_le s)) he
  simp only [cast_anchorIndex] at hh
  exact UniformK61.BalancedAnchor.anchor_injective_check _ _ _ _ hh

theorem anchorIndex_ne_center {c1 : Bool} {o : Owner} {s : Scope c1}
    (h : AnchorReady o s) (a : Fin 5) : anchorIndex h a ≠ center s := by
  have ha := (UniformK61.BalancedAnchor.anchor_members (ownKind o s) (center16 s)
    (anchor (ownKind o s) (center16 s) a)).mpr ⟨a,rfl⟩
  intro he
  apply ha.1
  have hh := congrArg (Fin.castLE (own_le s)) he
  simpa only [cast_anchorIndex,center16] using hh

theorem own_zero {c1 : Bool} (s : Scope c1) : foreign (ownColor s) 0 = oppositeColor s := by
  cases s <;> rfl

theorem reference_palette {c1 : Bool} (s : Scope c1) (a b : Fin 5) (hab : a ≠ b) :
    foreign (ownColor s) (UniformK61.BalancedAnchor.reference a b) =
      foreign (oppositeColor s) (UniformK61.BalancedAnchor.reference a b) := by
  cases s <;> simp only [ownColor,oppositeColor] <;> revert hab b a <;> decide

theorem normalized_actual_geometry {c1 : Bool} {c : Host} {o : Owner}
    (hn : Normalized c1 c o) (s : Scope c1) (ready : AnchorReady o s)
    (roles : Fin (otherSize s) → Fin 11 → Nat) (states : Fin 6 → Nat) :
    BalancedEncoding.ActualGeometry c (geometry o s ready roles states) := by
  refine ⟨?_,other_injective s,?_,?_,?_,?_⟩
  · exact named_high c hn.caps (centerVertex s) (oppositeColor s) (by cases s <;> simp only [oppositeColor] <;> decide)
  · exact (own_injective s).comp (anchorIndex_injective ready)
  · intro a
    apply (mem_colorNeighborhood _ _ _ _).mpr
    refine ⟨(own_injective s).ne (anchorIndex_ne_center ready a),?_⟩
    change c (ownVertex s (center s)) (ownVertex s (anchorIndex ready a)) = palette (oppositeColor s)
    have ha := (UniformK61.BalancedAnchor.anchor_members (ownKind o s) (center16 s)
      (anchor (ownKind o s) (center16 s) a)).mpr ⟨a,rfl⟩
    rw [own_template hn s _ _ (anchorIndex_ne_center ready a).symm,cast_anchorIndex]
    change palette (foreign (ownColor s)
      (R4333.k16Template (ownKind o s) (center16 s) (anchor (ownKind o s) (center16 s) a))) = _
    rw [ha.2,own_zero]
  · intro a b hab
    change c (ownVertex s (anchorIndex ready a)) (ownVertex s (anchorIndex ready b)) = _
    rw [own_template hn s _ _ ((anchorIndex_injective ready).ne hab),cast_anchorIndex,cast_anchorIndex,
      UniformK61.BalancedAnchor.anchor_colors _ _ _ _ hab,reference_palette s a b hab]
    rfl
  · intro a b hab
    exact other_template hn s a b hab

/-- Every retained scope of either canonical root layout has its six-state
witness in the same actual coloring. Other vertices may have either C type. -/
theorem normalized_local_witness {c1 : Bool} {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized c1 c o)
    (s : Scope c1) (ready : AnchorReady o s)
    (roles : Fin (otherSize s) → Fin 11 → Nat) (states : Fin 6 → Nat) :
    Nonempty (BalancedEncoding.LocalWitness c (geometry o s ready roles states)) :=
  BalancedEncoding.actual_local_witness hc
    (normalized_actual_geometry hn s ready roles states)

#print axioms normalized_actual_geometry
#print axioms normalized_local_witness
end UniformK60.BalancedHost
