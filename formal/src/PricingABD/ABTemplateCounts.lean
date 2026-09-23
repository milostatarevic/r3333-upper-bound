import PricingABD.ABGeometry
import PricingABD.NativeTemplateDegreeProfiles

set_option autoImplicit false
namespace PricingABD.ABTemplateCounts
open PricingABD.ABLayout PricingABD.ABGeometry PricingABD.NativeTemplateDegreeProfiles

def localColor (own q : Fin 4) : Fin 3 :=
  ⟨if q.val<own.val then q.val else q.val-1,by split_ifs <;> omega⟩

theorem foreign_eq_iff (own q : Fin 4) (hq : q≠own) (r : Fin 3) :
    foreign own r=q ↔ r=localColor own q := by
  exact (by decide : ∀own q : Fin 4,q≠own → ∀r : Fin 3,
    foreign own r=q ↔ r=localColor own q) own q hq r

def internalCount {n : Nat} (own : Fin 4) (c : R4333.EdgeColoring (Fin n) (Fin 3))
    (u : Fin n) (q : Fin 4) : Nat :=
  (List.finRange n).countP (fun v=>decide (u≠v ∧ foreign own (c u v)=q))

theorem internalCount_own {n : Nat} (own : Fin 4) (c : R4333.EdgeColoring (Fin n) (Fin 3)) (u : Fin n) :
    internalCount own c u own=0 := by
  simp [internalCount,foreign_ne]

theorem internalCount_foreign {n : Nat} (own : Fin 4) (c : R4333.EdgeColoring (Fin n) (Fin 3))
    (u : Fin n) (q : Fin 4) (hq : q≠own) :
    internalCount own c u q=rowCount c u (localColor own q) := by
  simp only [internalCount,rowCount,←List.countP_eq_length_filter]
  apply List.countP_congr
  intro v _
  simp [foreign_eq_iff own q hq]

theorem large_internal (own : Fin 4) (t : Bool) (u : Fin 16) (q : Fin 4) :
    internalCount own (R4333.k16Template t) u q=if q=own then 0 else 5 := by
  by_cases h:q=own
  · subst q;rw [if_pos rfl,internalCount_own]
  · rw [if_neg h,internalCount_foreign own _ u q h,k16_rows]

theorem small_internal (own : Fin 4) (t : Bool) (u : Fin 15) (q : Fin 4) :
    internalCount own (R4333.k15Template t) u q=
      if q=own then 0 else if foreign own (R4333.k16Template t ⟨u.val,by omega⟩ 15)=q then 4 else 5 := by
  by_cases h:q=own
  · subst q;rw [if_pos rfl,internalCount_own]
  · rw [if_neg h,internalCount_foreign own _ u q h,k15_rows]
    simp only [foreign_eq_iff own q h]

/-- All K16 choices share the same fixed true count, while a K15 choice
retains precisely its actual distinguished-vertex color table. -/
theorem large_type_invariant (own : Fin 4) (s t : Bool) (u : Fin 16) (q : Fin 4) :
    internalCount own (R4333.k16Template s) u q=internalCount own (R4333.k16Template t) u q := by
  rw [large_internal,large_internal]

#print axioms large_internal
#print axioms small_internal
end PricingABD.ABTemplateCounts
