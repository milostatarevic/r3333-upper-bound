import PricingABD.ABScheduleTypes

set_option autoImplicit false
namespace PricingABD.ABFastFold
open PricingABD.ABLayout PricingABD.ABPosition PricingABD.ABGeometry PricingABD.ABTemplateCounts
open PricingABD.ABKnown PricingABD.ABSourceRows PricingABD.ABSourceDomain PricingABD.ABFixedCounts
open PricingABD.ABRowCounts PricingABD.ABCommands PricingABD.ABScheduleTypes
open PricingIntegration.NativePrimary PricingIntegration.FoldedThreshold

def modelDegree (own : Fin 4) (large t : Bool) (u : Fin (if large then 16 else 15)) (q : Fin 4) : Nat :=
  match large with
  | true => if q=own then 0 else 5
  | false => if q=own then 0 else if foreign own (R4333.k16Template t ⟨u.val,by have h:=u.isLt;simp only [Bool.false_eq_true,if_false] at h;omega⟩ 15)=q then 4 else 5

theorem modelDegree_correct (own : Fin 4) (large t : Bool)
    (u : Fin (if large then 16 else 15)) (q : Fin 4) :
    modelDegree own large t u q=internalCount own (model large t) u q := by
  cases large with
  | false => exact (small_internal own t u q).symm
  | true => exact (large_internal own t u q).symm

def positionFixed (l : Layout) (t : Types) (includeFree : Bool) (u : Position l) (q : Fin 4) : Nat :=
  match u with
  | .free i => (if includeFree then freeCount l i q else 0)+(if q=3 then 1 else 0)
  | .left i => modelDegree 1 (leftLarge l) t.left i q
  | .right i => modelDegree 2 (rightLarge l) t.right i q
  | .marked i => (if includeFree ∧ i=15 ∧ q=3 then freeSize l else 0)+(if q=3 then 0 else 5)

def rowFixed (l : Layout) (t : Types) (includeFree : Bool) (u : Fin (vertexCount l)) (q : Fin 4) : Nat :=
  positionFixed l t includeFree (decode l u) q

theorem positionFixed_correct (l : Layout) (t : Types) (includeFree : Bool) (u : Position l) (q : Fin 4) :
    positionFixed l t includeFree u q=(positions l includeFree).countP (fun v=>positionTruth t u v q) := by
  cases u with
  | free i => exact (count_free t includeFree i q).symm
  | left i => rw [count_left];exact modelDegree_correct 1 _ _ i q
  | right i => rw [count_right];exact modelDegree_correct 2 _ _ i q
  | marked i => rw [count_marked,large_internal];rfl

theorem rowFixed_correct (l : Layout) (t : Types) (includeFree : Bool) (u : Fin (vertexCount l)) (q : Fin 4) :
    rowFixed l t includeFree u q=trueFixed (known l t) (row (if includeFree then allLabels l else tailLabels l) u q) := by
  rw [trueFixed_row]
  have hh:=fixedCount_positions l t includeFree (decode l u) q
  simpa [rowFixed,positionFixed_correct] using hh.symm

def fixed (l : Layout) (t : Types) : Kind l → Nat
  | .freeInterval u q _ => rowFixed l t false (ABLayout.free l u) q
  | .freePair u q => rowFixed l t false (ABLayout.free l u) 0+rowFixed l t false (ABLayout.free l u) (nonzero q)
  | .tailNonzero u q => rowFixed l t false (ABLayout.tail l u) (nonzero q)
  | .tailZero u => rowFixed l t true (ABLayout.tail l u) 0
  | .cap u q => rowFixed l t true u q
  | .proxy u => rowFixed l t false u (owner l u)
  | .highTotal => 0

def inputs (l : Layout) : Kind l → List Lit
  | .freeInterval u q _ => unknownRow l ⟨false,false,false⟩ (tailLabels l) (ABLayout.free l u) q
  | .freePair u q => unknownRow l ⟨false,false,false⟩ (tailLabels l) (ABLayout.free l u) 0 ++
      unknownRow l ⟨false,false,false⟩ (tailLabels l) (ABLayout.free l u) (nonzero q)
  | .tailNonzero u q => unknownRow l ⟨false,false,false⟩ (tailLabels l) (ABLayout.tail l u) (nonzero q)
  | .tailZero u => unknownRow l ⟨false,false,false⟩ (allLabels l) (ABLayout.tail l u) 0
  | .cap u q => unknownRow l ⟨false,false,false⟩ (allLabels l) u q
  | .proxy u => unknownRow l ⟨false,false,false⟩ (tailLabels l) u (owner l u)
  | .highTotal => (allLabels l).map (fun u=>(true,high l u))

theorem fixed_correct (l : Layout) (t : Types) (k : Kind l) :
    fixed l t k=trueFixed (known l t) (command l k).xs := by
  cases k <;> simp only [fixed,command]
  all_goals first
    | exact rowFixed_correct l t _ _ _
    | exact (high_fixed_zero l t).symm
    | (simp only [trueFixed,List.countP_append];exact congrArg₂ Nat.add (rowFixed_correct l t _ _ _) (rowFixed_correct l t _ _ _))

theorem unknown_row_uncolored (l : Layout) (t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) :
    unknownRow l ⟨false,false,false⟩ domain u q=unknown (known l t) (row domain u q) := by
  rw [unknown_row]
  exact unknown_types _ _ _ _ _ _

theorem inputs_correct (l : Layout) (t : Types) (k : Kind l) :
    inputs l k=unknown (known l t) (command l k).xs := by
  cases k <;> simp only [inputs,command]
  all_goals first
    | exact unknown_row_uncolored l t _ _ _
    | (simp only [unknown,List.filter_append];exact congrArg₂ List.append (unknown_row_uncolored l t _ _ _) (unknown_row_uncolored l t _ _ _))
    | (simp [unknown,List.filter_map,Function.comp_def,knownValue,known_high])

#print axioms fixed_correct
#print axioms inputs_correct
end PricingABD.ABFastFold
