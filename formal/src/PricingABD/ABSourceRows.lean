import PricingABD.ABKnown

set_option autoImplicit false
namespace PricingABD.ABSourceRows
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter PricingABD.ABLayout
open PricingABD.ABGeometry PricingABD.ABFixedColor PricingABD.ABKnown
open PricingIntegration.NativePrimaryCore PricingIntegration.NativePrimary PricingIntegration.FoldedThreshold

def unknownRow (l : Layout) (t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) : List Lit :=
  ((neighbors domain u).filter (fun v=>(fixedColor l t u v).isNone)).map (fun v=>(true,edgeVar u v q))

def fixedCount (l : Layout) (t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) : Nat :=
  (neighbors domain u).countP (fun v=>fixedTruth l t u v q)

theorem unknown_mapped (l : Layout) (t : Types) (u : Fin (vertexCount l)) (q : Fin 4)
    (xs : List (Fin (vertexCount l))) (hn : ∀v∈xs,u≠v) :
    unknown (known l t) (xs.map (fun v=>(true,edgeVar u v q)))=
      (xs.filter (fun v=>(fixedColor l t u v).isNone)).map (fun v=>(true,edgeVar u v q)) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have hv:=hn v (List.mem_cons_self)
    have hx : ∀w∈xs,u≠w := fun w hw=>hn w (List.mem_cons_of_mem v hw)
    simp only [List.map_cons,unknown,List.filter_cons] at ih ⊢
    rw [known_isNone l t u v q hv]
    split_ifs <;> simp [ih hx]

theorem trueFixed_mapped (l : Layout) (t : Types) (u : Fin (vertexCount l)) (q : Fin 4)
    (xs : List (Fin (vertexCount l))) (hn : ∀v∈xs,u≠v) :
    trueFixed (known l t) (xs.map (fun v=>(true,edgeVar u v q)))=
      xs.countP (fun v=>fixedTruth l t u v q) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have hv:=hn v (List.mem_cons_self)
    have hx : ∀w∈xs,u≠w := fun w hw=>hn w (List.mem_cons_of_mem v hw)
    simp only [trueFixed,List.map_cons,List.countP_cons] at ih ⊢
    rw [known_true l t u v q hv,ih hx]

theorem unknown_row (l : Layout) (t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) :
    unknown (known l t) (row domain u q)=unknownRow l t domain u q := by
  apply unknown_mapped
  intro v hv
  exact ((List.mem_filter.mp hv).2 |> of_decide_eq_true).symm

theorem trueFixed_row (l : Layout) (t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) :
    trueFixed (known l t) (row domain u q)=fixedCount l t domain u q := by
  apply trueFixed_mapped
  intro v hv
  exact ((List.mem_filter.mp hv).2 |> of_decide_eq_true).symm

theorem unknown_types (l : Layout) (s t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) : unknownRow l s domain u q=unknownRow l t domain u q := by
  unfold unknownRow
  congr 1
  apply List.filter_congr
  intro v _
  exact fixed_domain_independent l s t u v

#print axioms unknown_row
#print axioms trueFixed_row
#print axioms unknown_types
end PricingABD.ABSourceRows
