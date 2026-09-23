import PricingABD.ABFixedCounts
import PricingABD.ABCommands
import PricingABD.KnownSourceDomain

set_option autoImplicit false
namespace PricingABD.ABScheduleTypes
open Ramsey61.DenseCounter PricingABD.ABLayout PricingABD.ABPosition PricingABD.ABGeometry
open PricingABD.ABFixedColor PricingABD.ABKnown PricingABD.ABSourceRows PricingABD.ABSourceDomain
open PricingABD.ABTemplateCounts PricingABD.ABFixedCounts PricingABD.ABRowCounts PricingABD.ABCommands
open PricingIntegration.FoldedThreshold PricingIntegration.NativePrimary

/-- Precisely the template information that can affect folded row counts. -/
def SameSchedule (l : Layout) (s t : Types) : Prop :=
  (leftLarge l=true ∨ s.left=t.left) ∧ (rightLarge l=true ∨ s.right=t.right)

def canonicalTypes (l : Layout) (t : Types) : Types :=
  ⟨if leftLarge l then false else t.left,if rightLarge l then false else t.right,false⟩

theorem canonical_same (l : Layout) (t : Types) : SameSchedule l t (canonicalTypes l t) := by
  constructor
  · by_cases h:leftLarge l=true
    · exact Or.inl h
    · exact Or.inr (by simp [canonicalTypes,h])
  · by_cases h:rightLarge l=true
    · exact Or.inl h
    · exact Or.inr (by simp [canonicalTypes,h])

theorem model_internal_same (large s t : Bool) (h : large=true ∨ s=t)
    (own : Fin 4) (u : Fin (if large then 16 else 15)) (q : Fin 4) :
    internalCount own (model large s) u q=internalCount own (model large t) u q := by
  cases large with
  | false => have he:s=t := h.resolve_left (by decide);subst t;rfl
  | true => exact large_type_invariant own s t u q

theorem positions_count_same {l : Layout} (s t : Types) (h : SameSchedule l s t)
    (includeFree : Bool) (u : Position l) (q : Fin 4) :
    (positions l includeFree).countP (fun v=>positionTruth s u v q)=
      (positions l includeFree).countP (fun v=>positionTruth t u v q) := by
  cases u with
  | free i => rw [count_free,count_free]
  | left i => rw [count_left,count_left];exact model_internal_same _ _ _ h.1 1 i q
  | right i => rw [count_right,count_right];exact model_internal_same _ _ _ h.2 2 i q
  | marked i => rw [count_marked,count_marked,large_type_invariant 3 s.marked t.marked i q]

theorem fixedCount_same {l : Layout} (s t : Types) (h : SameSchedule l s t)
    (includeFree : Bool) (u : Fin (vertexCount l)) (q : Fin 4) :
    fixedCount l s (if includeFree then allLabels l else tailLabels l) u q=
      fixedCount l t (if includeFree then allLabels l else tailLabels l) u q := by
  have hh:=positions_count_same s t h includeFree (decode l u) q
  rw [←fixedCount_positions,←fixedCount_positions] at hh
  simpa using hh

theorem trueFixed_same {l : Layout} (s t : Types) (h : SameSchedule l s t)
    (includeFree : Bool) (u : Fin (vertexCount l)) (q : Fin 4) :
    trueFixed (known l s) (row (if includeFree then allLabels l else tailLabels l) u q)=
      trueFixed (known l t) (row (if includeFree then allLabels l else tailLabels l) u q) := by
  rw [trueFixed_row,trueFixed_row]
  exact fixedCount_same s t h includeFree u q

theorem known_domain_same (l : Layout) (s t : Types) (a : Nat) :
    known l s a=none ↔ known l t a=none := by
  rw [known,known,KnownPull.domain code (code_injective l),KnownPull.domain code (code_injective l)]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  unfold source
  cases hs:fixedColor l s k.u k.v <;> cases ht:fixedColor l t k.u k.v <;>
    have hh:=fixed_domain_independent l s t k.u k.v <;> simp_all

theorem unknown_same (l : Layout) (s t : Types) (xs : List Lit) :
    unknown (known l s) xs=unknown (known l t) xs :=
  PricingABD.KnownSourceDomain.unknown_eq_of_domain _ _ (known_domain_same l s t) xs

theorem high_fixed_zero (l : Layout) (t : Types) :
    trueFixed (known l t) ((allLabels l).map (fun u=>(true,high l u)))=0 := by
  simp [trueFixed,List.countP_map,Function.comp_def,knownValue,known_high]

theorem command_fixed_same {l : Layout} (s t : Types) (h : SameSchedule l s t) (k : Kind l) :
    trueFixed (known l s) (command l k).xs=trueFixed (known l t) (command l k).xs := by
  cases k with
  | freeInterval u q upper => exact trueFixed_same s t h false (ABLayout.free l u) q
  | freePair u q =>
    simp only [command,trueFixed,List.countP_append]
    exact congrArg₂ Nat.add
      (trueFixed_same s t h false (ABLayout.free l u) 0)
      (trueFixed_same s t h false (ABLayout.free l u) (nonzero q))
  | tailNonzero u q => exact trueFixed_same s t h false (ABLayout.tail l u) (nonzero q)
  | tailZero u => exact trueFixed_same s t h true (ABLayout.tail l u) 0
  | cap u q => exact trueFixed_same s t h true u q
  | proxy u => exact trueFixed_same s t h false u (owner l u)
  | highTotal => exact (high_fixed_zero l s).trans (high_fixed_zero l t).symm

/-- Every actual A/B bound uses one of six exact folded-input/target schedules.
It preserves the actual fixed-color source: template type changes only the
proof-only schedule representative, never the physical host coloring. -/
theorem command_schedule_canonical (l : Layout) (t : Types) (k : Kind l) :
    unknown (known l t) (command l k).xs=unknown (known l (canonicalTypes l t)) (command l k).xs ∧
    trueFixed (known l t) (command l k).xs=trueFixed (known l (canonicalTypes l t)) (command l k).xs :=
  ⟨unknown_same l t _ _,command_fixed_same t _ (canonical_same l t) k⟩

#print axioms command_schedule_canonical
end PricingABD.ABScheduleTypes
