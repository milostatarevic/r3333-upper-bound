import PricingABD.ABLayout

set_option autoImplicit false
namespace PricingABD.ABPhysicalBounds
open Ramsey61 Ramsey61.CEncodingCore Finset PricingABD.ABLayout
 def support {c : Host} {l : Layout} (f : Frame c l) : Finset (Fin 61) := univ.image (fun i : Fin (freeSize l) => f.vertex (ABLayout.free l i))
 def tailSet {c : Host} {l : Layout} (f : Frame c l) : Finset (Fin 61) := univ.image (fun i : Fin (tailSize l) => f.vertex (ABLayout.tail l i))
 def retained {c : Host} {l : Layout} (f : Frame c l) : Finset (Fin 61) := univ.image f.vertex

 theorem support_card {c : Host} {l : Layout} (f : Frame c l) : (support f).card=freeSize l := by
  unfold support
  rw [card_image_of_injective _ (show Function.Injective (fun i : Fin (freeSize l) => f.vertex (ABLayout.free l i)) from f.vertex.injective.comp (ABLayout.free_injective l))];simp
 theorem tail_card {c : Host} {l : Layout} (f : Frame c l) : (tailSet f).card=tailSize l := by
  unfold tailSet
  rw [card_image_of_injective _ (show Function.Injective (fun i : Fin (tailSize l) => f.vertex (ABLayout.tail l i)) from f.vertex.injective.comp (ABLayout.tail_injective l))];simp
 theorem support_subset {c : Host} {l : Layout} (f : Frame c l) : support f ⊆ colorNeighborhood c (palette 0) f.root := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  exact (mem_colorNeighborhood _ _ _ _).mpr ⟨f.ne_root _,(f.spokes _).trans (congrArg palette ((ABLayout.owner_free l i)))⟩
 theorem tail_subset {c : Host} {l : Layout} (f : Frame c l) : tailSet f ⊆ criticalTail c f.root (palette 0) := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  apply mem_sdiff.mpr
  refine ⟨mem_erase.mpr ⟨f.ne_root _,mem_univ _⟩,?_⟩
  intro hm
  have hcol := ((mem_colorNeighborhood _ _ _ _).mp hm).2
  rw [f.spokes] at hcol
  exact (ABLayout.owner_tail_nonzero l i) (palette_injective hcol)
 theorem actual_tail {c : Host} {l : Layout} (f : Frame c l) : tailSet f=criticalTail c f.root (palette 0) := by
  have hs : colorNeighborhood c (palette 0) f.root ⊆ (univ : Finset (Fin 61)).erase f.root := by
    intro v hv;exact mem_erase.mpr ⟨((mem_colorNeighborhood _ _ _ _).mp hv).1,mem_univ _⟩
  have hcard : (criticalTail c f.root (palette 0)).card=tailSize l := by
    rw [criticalTail,card_sdiff_of_subset hs]
    change _-colorDegree c (palette 0) f.root=tailSize l
    rw [f.low_degree]
    have hh:=sizes l
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    unfold lowSize
    omega
  exact eq_of_subset_of_card_le (tail_subset f) (by rw [tail_card,hcard])
 theorem retained_eq {c : Host} {l : Layout} (f : Frame c l) : retained f=retainedTailAndSupport c f.root (palette 0) (support f) := by
  rw [retainedTailAndSupport,←actual_tail]
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    by_cases hi : i.val<freeSize l
    · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨⟨i.val,hi⟩,mem_univ _,rfl⟩))
    · apply mem_union.mpr;left
      refine mem_image.mpr ⟨⟨i.val-freeSize l,by have hi:=i.isLt;unfold vertexCount at hi;omega⟩,mem_univ _,?_⟩
      congr 1;apply Fin.ext;dsimp [ABLayout.tail];omega
  · intro hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨ABLayout.tail l i,mem_univ _,rfl⟩
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨ABLayout.free l i,mem_univ _,rfl⟩

 def retainedDegree {c : Host} {l : Layout} (f : Frame c l) (u : Fin (vertexCount l)) (q : Fin 4) : Nat :=
  (colorNeighborhood c (palette q) (f.vertex u) ∩ retained f).card
 def tailCount {c : Host} {l : Layout} (f : Frame c l) (u : Fin (vertexCount l)) (q : Fin 4) : Nat :=
  (colorNeighborhood c (palette q) (f.vertex u) ∩ tailSet f).card

 theorem tailCount_eq {c : Host} {l : Layout} (f : Frame c l) (u : Fin (vertexCount l)) (q : Fin 4) :
    tailCount f u q=tailDegree c f.root (palette 0) (f.vertex u) (palette q) := by rw [tailCount,actual_tail];rfl
 theorem free_mem {c : Host} {l : Layout} (f : Frame c l) (i : Fin (freeSize l)) : f.vertex (ABLayout.free l i) ∈ colorNeighborhood c (palette 0) f.root :=
  support_subset f (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
 theorem tail_mem {c : Host} {l : Layout} (f : Frame c l) (i : Fin (tailSize l)) : f.vertex (ABLayout.tail l i) ∈ criticalTail c f.root (palette 0) :=
  tail_subset f (mem_image.mpr ⟨i,mem_univ _,rfl⟩)

#print axioms actual_tail
#print axioms retained_eq
end PricingABD.ABPhysicalBounds
