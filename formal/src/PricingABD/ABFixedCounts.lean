import PricingABD.ABSourceDomain
import PricingABD.ABTemplateCounts

set_option autoImplicit false
namespace PricingABD.ABFixedCounts
open PricingABD.ABLayout PricingABD.ABPosition PricingABD.ABGeometry PricingABD.ABFixedColor
open PricingABD.ABSourceDomain PricingABD.ABTemplateCounts PricingABD.ABSourceRows PricingABD.ABRowCounts

@[simp] theorem optional_truth {α : Type} [DecidableEq α] (u v : α) (r q : Fin 4) :
    (if u=v then none else some r).any (fun r=>decide (r=q))=decide (u≠v ∧ r=q) := by
  by_cases h:u=v <;> simp [h]

def freeCount (l : Layout) (u : Fin (freeSize l)) (q : Fin 4) : Nat :=
  (List.finRange (freeSize l)).countP (fun v=>decide (u≠v ∧ freeColor l u v=q))

theorem mark_count (q : Fin 4) :
    (List.finRange 16).countP (fun v:Fin 16=>(if v=15 then some (3:Fin 4) else none).any (fun r=>decide (r=q)))=
      if q=3 then 1 else 0 := by
  exact (by decide : ∀q:Fin 4,
    (List.finRange 16).countP (fun v:Fin 16=>(if v=15 then some (3:Fin 4) else none).any (fun r=>decide (r=q)))=
      if q=3 then 1 else 0) q

theorem count_free {l : Layout} (t : Types) (includeFree : Bool) (u : Fin (freeSize l)) (q : Fin 4) :
    (positions l includeFree).countP (fun v=>positionTruth t (.free u) v q)=
      (if includeFree then freeCount l u q else 0)+(if q=3 then 1 else 0) := by
  cases includeFree <;>
    simp [positions,List.countP_append,List.countP_map,Function.comp_def,positionTruth,positionColor,optional_truth,freeCount,mark_count]

theorem count_left {l : Layout} (t : Types) (includeFree : Bool) (u : Fin (leftSize l)) (q : Fin 4) :
    (positions l includeFree).countP (fun v=>positionTruth t (.left u) v q)=
      internalCount 1 (model (leftLarge l) t.left) u q := by
  cases includeFree <;>
    simp [positions,List.countP_append,List.countP_map,Function.comp_def,positionTruth,positionColor,optional_truth,internalCount] <;> rfl

theorem count_right {l : Layout} (t : Types) (includeFree : Bool) (u : Fin (rightSize l)) (q : Fin 4) :
    (positions l includeFree).countP (fun v=>positionTruth t (.right u) v q)=
      internalCount 2 (model (rightLarge l) t.right) u q := by
  cases includeFree <;>
    simp [positions,List.countP_append,List.countP_map,Function.comp_def,positionTruth,positionColor,optional_truth,internalCount] <;> rfl

theorem three_flip (q : Fin 4) : (3:Fin 4)=q ↔ q=3 := eq_comm

theorem count_marked {l : Layout} (t : Types) (includeFree : Bool) (u : Fin 16) (q : Fin 4) :
    (positions l includeFree).countP (fun v=>positionTruth t (.marked u) v q)=
      (if includeFree ∧ u=15 ∧ q=3 then freeSize l else 0)+
      internalCount 3 (R4333.k16Template t.marked) u q := by
  cases includeFree <;> by_cases hu:u=15 <;> by_cases hq:q=3 <;>
    simp [positions,List.countP_append,List.countP_map,Function.comp_def,positionTruth,positionColor,optional_truth,internalCount,hu,hq,three_flip]

#print axioms count_left
#print axioms count_marked
end PricingABD.ABFixedCounts
