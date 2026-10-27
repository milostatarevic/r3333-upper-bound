import UniformK61.CommonFormula

set_option autoImplicit false
namespace UniformK61.CommonSoundness
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativeSupportIndex CompletionC.SupportEdges
open UniformK61.CommonHost UniformK61.CommonFormula
variable {c : Host} {l : Layout} {t : Types}

theorem spokes_match (b : Blocks c l t) : Core.UnitsMatch (coloring b) (spokes l) := by
  intro u hu
  simp only [spokes,List.mem_append] at hu
  rcases hu with ((h|h)|h)|h
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [lowVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (lowVertex l i))=palette 0
      rw [fullMap_root,fullMap_low]
      exact ((mem_colorNeighborhood _ _ _ _).mp (low_mem b i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [leftVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (leftVertex l i))=palette 1
      rw [fullMap_root,fullMap_left]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.left.mem_neighborhood i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [rightVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (rightVertex l i))=palette 2
      rw [fullMap_root,fullMap_right]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.right.mem_neighborhood i)).2
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have := congrArg Fin.val he;simp [markedVertex] at this;omega
    · change c (fullMap b 0) (fullMap b (markedVertex l i))=palette 3
      rw [fullMap_root,fullMap_marked]
      exact ((mem_colorNeighborhood _ _ _ _).mp (b.marked.mem_neighborhood i)).2

theorem ordered_ne {n : Nat} (ab : Fin n×Fin n) (h : ab∈ABGeometry.orderedPairs n) : ab.1≠ab.2 := by
  simp only [ABGeometry.orderedPairs,List.mem_flatMap,List.mem_map] at h
  obtain ⟨a,_,d,hd,rfl⟩ := h
  exact ne_of_lt (by simpa using (List.mem_filter.mp hd).2)

theorem edge_match (b : Blocks c l t) (a d : Fin (vertexCount l)) (q : Color)
    (hne : a≠d) (he : c (physical b a) (physical b d)=palette q) :
    Core.UnitMatches (coloring b) (edgeUnit l (a,d,q)) := by
  refine ⟨(retain_injective l).ne hne,?_⟩
  change c (fullMap b (retain l a)) (fullMap b (retain l d))=palette q
  simpa only [fullMap_retain] using he

theorem templates_match (b : Blocks c l t) : Core.UnitsMatch (coloring b) (templates l t) := by
  intro u hu
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hu
  simp only [templateEdges,List.mem_append] at he
  rcases he with (h|h)|h
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp h
    apply edge_match b _ _ _ ((ABLayout.left_injective l).ne (ordered_ne ab hab))
    exact left_edges b _ _ (ordered_ne ab hab)
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp h
    apply edge_match b _ _ _ ((ABLayout.right_injective l).ne (ordered_ne ab hab))
    exact right_edges b _ _ (ordered_ne ab hab)
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp h
    apply edge_match b _ _ _ ((ABLayout.marked_injective l).ne (ordered_ne ab hab))
    exact marked_edges b _ _ (ordered_ne ab hab)

theorem free_match (b : Blocks c l t) (hg : Geometry t (frame b)) :
    Core.UnitsMatch (coloring b) (freeShape l) := by
  intro u hu
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hu
  obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp he
  exact edge_match b _ _ _ ((ABLayout.free_injective l).ne (ordered_ne ab hab))
    (hg.free _ _ (ordered_ne ab hab))

theorem label61_eq {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (p : Fin 737) (hf : freeSize l=(pairTable p).shape.free)
    (hp : PricingIntegration.PairAdmission.retained p=sourceRecord b (pairTable p).shape)
    (a : Fin (pairTable p).shape.dimension) :
    label61 l p a.val=retain l (supportIndex b (pairTable p).shape hf p hp a) := by
  apply Fin.ext
  dsimp [label61]
  rw [label_supportIndex b p hf hp a]
  exact Nat.mod_eq_of_lt (retain l (supportIndex b (pairTable p).shape hf p hp a)).isLt

theorem word_match (b z : Blocks c l t) (p : Fin 737)
    (hf : freeSize l=(pairTable p).shape.free)
    (hp : PricingIntegration.PairAdmission.retained p=sourceRecord b (pairTable p).shape)
    (j : Fin (pairTable p).count)
    (hmat : ∀a d : Fin (pairTable p).shape.dimension,a≠d→
      c ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp a))
        ((frame z).vertex (supportIndex b (pairTable p).shape hf p hp d))=
      palette (matrix (pairTable p).shape ((pairTable p).representative j) a d)) :
    Core.UnitsMatch (coloring z) (word l p j) := by
  intro u hu
  have hm : u∈rawWord l p j := by
    unfold word at hu
    split_ifs at hu
    · exact (List.mem_mergeSort).mp hu
    · exact hu
  obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hm
  have hn : ab.1≠ab.2 := by
    rcases List.mem_append.mp hab with h|h
    · rcases List.mem_append.mp h with h|h
      · exact product_ne _ 0 1 (by decide) ab h
      · exact product_ne _ 0 2 (by decide) ab h
    · exact product_ne _ 1 2 (by decide) ab h
  have hs := (supportIndex_injective b (pairTable p).shape hf p hp).ne hn
  change label61 l p ab.1.val≠label61 l p ab.2.val ∧ _
  rw [label61_eq b p hf hp ab.1,label61_eq b p hf hp ab.2]
  refine ⟨(retain_injective l).ne hs,?_⟩
  change c (fullMap z (retain l _)) (fullMap z (retain l _))=_
  simpa only [fullMap_retain,frame,Core.palette] using hmat _ _ hn

theorem signed_match (d : Host) (u v : Vertex) (q : Color) (P : Prop) [Decidable P]
    (hne : u≠v) (he : d u v=palette q ↔ P) : Core.UnitMatches d ⟨decide P,u,v,q⟩ := by
  refine ⟨hne,?_⟩
  by_cases h : P
  · simp only [h,decide_true,if_true];exact he.mpr h
  · simp only [h,decide_false];exact fun hq => h (he.mp hq)

theorem membershipFor_match (b : Blocks c l t) (hc : NoMonochromaticTriangle c) (ls rs : Finset Nat)
    (hl : ∀v : Fin (leftSize l),c (b.marked.vertex 15) (b.left.vertex v)=palette 3 ↔ v.val∈ls)
    (hr : ∀v : Fin (rightSize l),c (b.marked.vertex 15) (b.right.vertex v)=palette 3 ↔ v.val∈rs) :
    Core.UnitsMatch (coloring b) (membershipFor l ls rs) := by
  intro u hu
  simp only [membershipFor,List.mem_append] at hu
  rcases hu with ((h|h)|h)|h
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    apply signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [lowVertex] at hh;have := sizes l;omega
    · change c (fullMap b 60) (fullMap b (lowVertex l i))=palette 3 ↔ _
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
    · intro he;have hh := congrArg Fin.val he;dsimp [leftVertex] at hh;have := sizes l;unfold lowSize tailSize at hh;omega
    · change c (fullMap b 60) (fullMap b (leftVertex l i))=palette 3 ↔ _
      simpa only [fullMap_mark,fullMap_left] using hl i
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    apply signed_match
    · intro he;have hh := congrArg Fin.val he;dsimp [rightVertex] at hh;have := sizes l;unfold lowSize tailSize at hh;omega
    · change c (fullMap b 60) (fullMap b (rightVertex l i))=palette 3 ↔ _
      simpa only [fullMap_mark,fullMap_right] using hr i
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he;have hh := congrArg Fin.val he;dsimp [markedVertex] at hh;omega
    · change c (fullMap b 60) (fullMap b (markedVertex l ⟨i.val,by omega⟩))≠palette 3
      rw [fullMap_mark,fullMap_marked]
      exact neighborhood_avoids_own_color c hc (b.marked.mem_neighborhood 15)
        (b.marked.mem_neighborhood ⟨i.val,by omega⟩)
        (b.marked.vertex.injective.ne (by
          intro he
          have hval : (15 : Nat)=i.val := congrArg (fun x : Fin 16 => x.val) he
          have hi := i.isLt
          omega))

theorem membership_match (b : Blocks c l t) (hc : NoMonochromaticTriangle c) (p : Fin 737)
    (hl : ∀v : Fin (leftSize l),c (b.marked.vertex 15) (b.left.vertex v)=palette 3 ↔ v.val∈(PricingIntegration.PairAdmission.retained p).left)
    (hr : ∀v : Fin (rightSize l),c (b.marked.vertex 15) (b.right.vertex v)=palette 3 ↔ v.val∈(PricingIntegration.PairAdmission.retained p).right) :
    Core.UnitsMatch (coloring b) (membership l p) :=
  membershipFor_match b hc _ _ hl hr

end UniformK61.CommonSoundness
