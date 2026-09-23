import PricingABD.B52Core
import PricingIntegration.FoldedThreshold

namespace PricingABD.BPrimary
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore Finset
open PricingABD.BPhysicalBounds
open PricingIntegration.FoldedThreshold
@[simp] theorem boolTrue (b : Bool) : (b == true)=b := by cases b <;> rfl

noncomputable def indexColor {c : Host} (f : Frame c) : B52Core.Coloring :=
  ⟨fun u v => c (f.vertex u) (f.vertex v),fun u v => c.color_symm _ _⟩
noncomputable def primary {c : Host} (f : Frame c) : Valuation := fun a =>
  if h : 5305 ≤ a ∧ a < 5357 then
    decide (f.vertex ⟨a-5305,by omega⟩ ∈ Incoming c f.root)
  else B52Core.physicalValuation (indexColor f) a

def high (u : Fin 52) : Nat := 5305+u.val

theorem primary_high {c : Host} (f : Frame c) (u : Fin 52) :
    primary f (high u)=true ↔ f.vertex u ∈ Incoming c f.root := by
  have hr : 5305≤high u ∧ high u<5357 := by dsimp [high];omega
  rw [primary,dif_pos hr]
  simp only [high,Nat.add_sub_cancel_left,decide_eq_true_eq]
theorem primary_edge {c : Host} (f : Frame c) (u v : Fin 52) (q : Fin 4) (hne : u≠v) :
    primary f (B52Core.edgeVar u v q)=true ↔ c (f.vertex u) (f.vertex v)=palette q := by
  have hb := (B52Core.edgeVar_bounds u v q hne).2
  rw [primary,dif_neg (by omega)]
  exact B52Core.physicalValuation_edge (indexColor f) u v q hne

def allLabels : List (Fin 52) := List.finRange 52
 def tailLabels : List (Fin 52) := (List.finRange 47).map tailLabel
 def neighbors (domain : List (Fin 52)) (u : Fin 52) : List (Fin 52) := domain.filter (fun v => v≠u)
 def row (domain : List (Fin 52)) (u : Fin 52) (q : Fin 4) : List Lit :=
   (neighbors domain u).map (fun v => (true,B52Core.edgeVar u v q))
 def physicalSet {c : Host} (f : Frame c) (domain : List (Fin 52)) : Finset (Fin 61) := domain.toFinset.image f.vertex

 theorem row_count {c : Host} (f : Frame c) (domain : List (Fin 52)) (hn : domain.Nodup) (u : Fin 52) (q : Fin 4) :
    count (primary f) (row domain u q) =
      (colorNeighborhood c (palette q) (f.vertex u) ∩ physicalSet f domain).card := by
  classical
  simp only [count,row,List.countP_map,Function.comp_def,value,boolTrue]
  have heq : List.countP (fun v => primary f (B52Core.edgeVar u v q)) (neighbors domain u) =
      List.countP (fun v => decide (c (f.vertex u) (f.vertex v)=palette q)) (neighbors domain u) := by
    apply List.countP_congr
    intro v hv
    have hne : u≠v := ((List.mem_filter.mp hv).2 |> of_decide_eq_true).symm
    simpa using primary_edge f u v q hne
  rw [heq,List.countP_eq_length_filter]
  let ls := (neighbors domain u).filter (fun v => decide (c (f.vertex u) (f.vertex v)=palette q))
  have hnodup : ls.Nodup := (hn.filter _).filter _
  have hset : ls.toFinset.image f.vertex = colorNeighborhood c (palette q) (f.vertex u) ∩ physicalSet f domain := by
    ext x
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_filter,ls,neighbors,decide_eq_true_eq,mem_inter,physicalSet,mem_colorNeighborhood]
    constructor
    · rintro ⟨v,⟨⟨hv,hne⟩,hcol⟩,rfl⟩
      exact ⟨⟨f.vertex.injective.ne hne,hcol⟩,v,hv,rfl⟩
    · rintro ⟨⟨hne,hcol⟩,v,hv,rfl⟩
      exact ⟨v,⟨⟨hv,fun h => hne (congrArg f.vertex h)⟩,hcol⟩,rfl⟩
  rw [←hset,Finset.card_image_of_injective _ f.vertex.injective,List.toFinset_card_of_nodup hnodup]
 theorem all_row_count {c : Host} (f : Frame c) (u : Fin 52) (q : Fin 4) :
    count (primary f) (row allLabels u q)=retainedDegree f u q := by
  change count (primary f) (row (List.finRange 52) u q)=_
  rw [row_count f _ (List.nodup_finRange 52)]
  rfl
 theorem tail_row_count {c : Host} (f : Frame c) (u : Fin 52) (q : Fin 4) :
    count (primary f) (row tailLabels u q)=tailCount f u q := by
  change count (primary f) (row ((List.finRange 47).map tailLabel) u q)=_
  rw [row_count f _ (List.nodup_finRange 47 |>.map tailLabel_injective)]
  congr 2
 theorem high_count {c : Host} (f : Frame c) :
    count (primary f) (allLabels.map (fun u => (true,high u)))=(Incoming c f.root ∩ retained f).card := by
  classical
  simp only [count,List.countP_map,Function.comp_def,value,boolTrue]
  have heq : List.countP (fun u => primary f (high u)) allLabels =
      List.countP (fun u => decide (f.vertex u ∈ Incoming c f.root)) allLabels := by
    apply List.countP_congr
    intro u hu
    simpa using primary_high f u
  rw [heq,List.countP_eq_length_filter]
  let ls := allLabels.filter (fun u => decide (f.vertex u∈Incoming c f.root))
  have hn : ls.Nodup := (List.nodup_finRange 52).filter _
  have hs : ls.toFinset.image f.vertex=Incoming c f.root ∩ retained f := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      have hh : f.vertex u ∈ Incoming c f.root := by simpa [ls,allLabels] using hu
      exact mem_inter.mpr ⟨hh,mem_image.mpr ⟨u,mem_univ _,rfl⟩⟩
    · intro hx
      obtain ⟨hh,hr⟩ := mem_inter.mp hx
      obtain ⟨u,_,rfl⟩ := mem_image.mp hr
      exact mem_image.mpr ⟨u,by simpa [ls,allLabels] using hh,rfl⟩
  rw [←hs,card_image_of_injective _ f.vertex.injective,List.toFinset_card_of_nodup hn]

 theorem retained_caps {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (u : Fin 52) (q : Fin 4) :
    retainedDegree f u q ≤ if q=owner u then 15 else 16 := by
  have hroot : f.root ∉ retained f := by
    intro h
    obtain ⟨i,_,he⟩ := mem_image.mp h
    exact f.ne_root i he
  have hs : colorNeighborhood c (palette q) (f.vertex u) ∩ retained f ⊆
      (colorNeighborhood c (palette q) (f.vertex u)).erase f.root := by
    intro v hv
    exact mem_erase.mpr ⟨fun he => hroot (he ▸ (mem_inter.mp hv).2),(mem_inter.mp hv).1⟩
  have hle := card_le_card hs
  have hcap := fourColor_colorDegree_le_sixteen c hc (palette q) (f.vertex u)
  change (colorNeighborhood c (palette q) (f.vertex u)).card≤16 at hcap
  change retainedDegree f u q≤_ at hle
  by_cases hq : q=owner u
  · have hr : f.root ∈ colorNeighborhood c (palette q) (f.vertex u) := by
      apply (mem_colorNeighborhood _ _ _ _).mpr
      exact ⟨(f.ne_root u).symm,by rw [c.color_symm,f.spokes,hq]⟩
    have hh := card_erase_add_one hr
    rw [if_pos hq]
    omega
  · rw [if_neg hq]
    exact le_trans (le_trans hle (card_le_card (erase_subset _ _))) hcap

#print axioms row_count
#print axioms high_count
#print axioms retained_caps
end PricingABD.BPrimary
