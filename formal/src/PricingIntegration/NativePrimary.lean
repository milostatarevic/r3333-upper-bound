import PricingIntegration.NativePrimaryCore
import PricingIntegration.FoldedThreshold
import PricingABD.ABLayout

set_option autoImplicit false
namespace PricingIntegration.NativePrimary
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter Finset
open PricingABD.ABLayout PricingIntegration.NativePrimaryCore PricingIntegration.FoldedThreshold

theorem vertex_bounds (l : Layout) : 50≤vertexCount l ∧ vertexCount l≤53 := by
  have := sizes l
  omega

noncomputable def indexColor {c : Host} {l : Layout} (f : Frame c l) : Coloring (vertexCount l) :=
  ⟨fun u v=>c (f.vertex u) (f.vertex v),fun u v=>c.color_symm _ _⟩

def high (l : Layout) (u : Fin (vertexCount l)) : Nat := edgeLimit (vertexCount l)+u.val
def primaryLimit (l : Layout) : Nat := edgeLimit (vertexCount l)+vertexCount l

noncomputable def primary {c : Host} {l : Layout} (f : Frame c l) : Valuation := fun a=>
  if h : edgeLimit (vertexCount l)≤a ∧ a<primaryLimit l then
    decide (f.vertex ⟨a-edgeLimit (vertexCount l),by unfold primaryLimit at h;omega⟩ ∈ Incoming c f.root)
  else physicalValuation (indexColor f) a

theorem primary_high {c : Host} {l : Layout} (f : Frame c l) (u : Fin (vertexCount l)) :
    primary f (high l u)=true ↔ f.vertex u∈Incoming c f.root := by
  have hr : edgeLimit (vertexCount l)≤high l u ∧ high l u<primaryLimit l := by
    dsimp [high,primaryLimit];omega
  rw [primary,dif_pos hr]
  simp only [high,Nat.add_sub_cancel_left,decide_eq_true_eq]

theorem primary_edge {c : Host} {l : Layout} (f : Frame c l)
    (u v : Fin (vertexCount l)) (q : Fin 4) (hne : u≠v) :
    primary f (edgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  have hb:=(edgeVar_bounds (vertex_bounds l) u v q hne).2
  rw [primary,dif_neg (by omega)]
  exact physicalValuation_edge (vertex_bounds l) (indexColor f) u v q hne

theorem primary_ordered {c : Host} {l : Layout} (f : Frame c l)
    (u v : Fin (vertexCount l)) (q : Fin 4) (huv : u<v) :
    primary f (orderedEdgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  simpa only [NativePrimaryCore.edgeVar,if_pos huv] using primary_edge f u v q (ne_of_lt huv)

theorem primary_ordered_false {c : Host} {l : Layout} (f : Frame c l)
    (u v : Fin (vertexCount l)) (q : Fin 4) (huv : u<v) :
    primary f (orderedEdgeVar u v q)=false ↔ c (f.vertex u) (f.vertex v)≠palette q := by
  rw [Bool.eq_false_iff]
  exact not_congr (primary_ordered f u v q huv)

@[simp] theorem boolTrue (b : Bool) : (b==true)=b := by cases b <;> rfl
def neighbors {n : Nat} (domain : List (Fin n)) (u : Fin n) : List (Fin n) := domain.filter (fun v=>v≠u)
def row {n : Nat} (domain : List (Fin n)) (u : Fin n) (q : Fin 4) : List Lit :=
  (neighbors domain u).map (fun v=>(true,edgeVar u v q))
def physicalSet {c : Host} {l : Layout} (f : Frame c l) (domain : List (Fin (vertexCount l))) : Finset (Fin 61) :=
  domain.toFinset.image f.vertex

theorem row_count {c : Host} {l : Layout} (f : Frame c l)
    (domain : List (Fin (vertexCount l))) (hn : domain.Nodup) (u : Fin (vertexCount l)) (q : Fin 4) :
    count (primary f) (row domain u q)=
      (colorNeighborhood c (palette q) (f.vertex u)∩physicalSet f domain).card := by
  classical
  simp only [count,row,List.countP_map,Function.comp_def,value,boolTrue]
  have heq : List.countP (fun v=>primary f (edgeVar u v q)) (neighbors domain u)=
      List.countP (fun v=>decide (c (f.vertex u) (f.vertex v)=palette q)) (neighbors domain u) := by
    apply List.countP_congr
    intro v hv
    have hne : u≠v:=((List.mem_filter.mp hv).2 |> of_decide_eq_true).symm
    simpa using primary_edge f u v q hne
  rw [heq,List.countP_eq_length_filter]
  let ls:=(neighbors domain u).filter (fun v=>decide (c (f.vertex u) (f.vertex v)=palette q))
  have hnodup : ls.Nodup := (hn.filter _).filter _
  have hset : ls.toFinset.image f.vertex=colorNeighborhood c (palette q) (f.vertex u)∩physicalSet f domain := by
    ext x
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_filter,ls,neighbors,decide_eq_true_eq,mem_inter,physicalSet,mem_colorNeighborhood]
    constructor
    · rintro ⟨v,⟨⟨hv,hne⟩,hcol⟩,rfl⟩
      exact ⟨⟨f.vertex.injective.ne hne,hcol⟩,v,hv,rfl⟩
    · rintro ⟨⟨hne,hcol⟩,v,hv,rfl⟩
      exact ⟨v,⟨⟨hv,fun h=>hne (congrArg f.vertex h)⟩,hcol⟩,rfl⟩
  rw [←hset,Finset.card_image_of_injective _ f.vertex.injective,List.toFinset_card_of_nodup hnodup]

#print axioms primary_edge
#print axioms primary_high
#print axioms row_count
end PricingIntegration.NativePrimary
