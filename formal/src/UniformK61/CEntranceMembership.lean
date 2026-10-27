import UniformK61.CEntranceSupportIndex
set_option autoImplicit false
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingIntegration.PairAdmission
open CompletionC.NativeMatrices CompletionC.SupportEdges
open Formula
variable {c : Host} {five lt rt : Bool}

theorem spokes_match (b : Blocks c five lt rt) : Core.UnitsMatch (coloring b) (spokes) := by
  intro u hu
  simp only [spokes,List.mem_append] at hu
  rcases hu with ((h|h)|h)|h
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [lowVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (lowVertex i))=palette 0
      rw [fullMap_root,fullMap_low]
      exact ((mem_colorNeighborhood _ _ _ _).mp (low_mem b i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [leftVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (leftVertex i))=palette 1
      rw [fullMap_root,fullMap_left]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.left.mem_neighborhood i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [rightVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (rightVertex i))=palette 2
      rw [fullMap_root,fullMap_right]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.right.mem_neighborhood i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [markedVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (markedVertex i))=palette 3
      rw [fullMap_root,fullMap_marked]
      exact ((mem_colorNeighborhood _ _ _ _).mp (marked_mem b.entrance i)).2

theorem signed_match (d : Host) (u v : Vertex) (q : Color) (P : Prop) [Decidable P]
    (hne : u≠v) (he : d u v=palette q ↔ P) : Core.UnitMatches d ⟨decide P,u,v,q⟩ := by
  refine ⟨hne,?_⟩
  by_cases h : P
  · simp only [h,decide_true,if_true];exact he.mpr h
  · simp only [h,decide_false];exact fun hq => h (he.mp hq)

theorem membershipFor_match (b : Blocks c five lt rt) (hc : NoMonochromaticTriangle c) (ls rs : Finset Nat)
    (hl : ∀v : Fin (16),c (b.entrance.mark) (b.left.vertex v)=palette 3 ↔ v.val∈ls)
    (hr : ∀v : Fin (16),c (b.entrance.mark) (b.right.vertex v)=palette 3 ↔ v.val∈rs) :
    Core.UnitsMatch (coloring b) (membershipFor five ls rs) := by
  intro u hu
  simp only [membershipFor,List.mem_append] at hu
  rcases hu with ((h|h)|h)|h
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    apply signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [lowVertex] at hh;have := freeSize_le_five five;omega
    · change c (fullMap b 60) (fullMap b (lowVertex i))=palette 3 ↔ _
      rw [fullMap_mark,fullMap_low]
      constructor
      · intro he
        by_contra hn
        exact omitted_not_marked b _ (low_omitted b i (by omega)) he
      · intro hi
        simp only [low,hi,dif_pos]
        exact b.free_own _
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    apply signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [leftVertex] at hh;have := freeSize_le_five five;omega
    · change c (fullMap b 60) (fullMap b (leftVertex i))=palette 3 ↔ _
      simpa only [fullMap_mark,fullMap_left] using hl i
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    apply signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [rightVertex] at hh;have := freeSize_le_five five;omega
    · change c (fullMap b 60) (fullMap b (rightVertex i))=palette 3 ↔ _
      simpa only [fullMap_mark,fullMap_right] using hr i
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have hh := congrArg Fin.val he;dsimp [markedVertex] at hh;omega
    · change c (fullMap b 60) (fullMap b (markedVertex ⟨i.val,by omega⟩))≠palette 3
      rw [fullMap_mark,fullMap_marked]
      exact neighborhood_avoids_own_color c hc (b.entrance.mark_mem)
        (marked_mem b.entrance ⟨i.val,by omega⟩)
        (by
          rw [←marked_last b.entrance]
          apply (marked_injective b.entrance).ne
          intro he
          have hval : (13 : Nat)=i.val := congrArg (fun x : Fin 14 => x.val) he
          have hi := i.isLt
          omega)

theorem membership_match (b : Blocks c five lt rt) (hc : NoMonochromaticTriangle c) (p : Fin 737)
    (hl : ∀v : Fin (16),c (b.entrance.mark) (b.left.vertex v)=palette 3 ↔ v.val∈(PricingIntegration.PairAdmission.retained p).left)
    (hr : ∀v : Fin (16),c (b.entrance.mark) (b.right.vertex v)=palette 3 ↔ v.val∈(PricingIntegration.PairAdmission.retained p).right) :
    Core.UnitsMatch (coloring b) (membership five p) :=
  membershipFor_match b hc _ _ hl hr

end UniformK61.CEntrance
