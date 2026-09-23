import Ramsey61.ABDTailBounds
import Ramsey61.CEncodingCore

namespace PricingABD.BPhysicalBounds
open Ramsey61 Ramsey61.CEncodingCore Finset

 def owner (i : Fin 52) : Fin 4 := if i.val<5 then 0 else if i.val<20 then 1 else if i.val<36 then 2 else 3
 def freeLabel (i : Fin 5) : Fin 52 := ⟨i.val,by omega⟩
 def tailLabel (i : Fin 47) : Fin 52 := ⟨5+i.val,by omega⟩
 theorem freeLabel_injective : Function.Injective freeLabel := by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 52 => x.val) h
 theorem tailLabel_injective : Function.Injective tailLabel := by intro i j h;apply Fin.ext;have hh:=congrArg (fun x : Fin 52 => x.val) h;dsimp [tailLabel]at hh;omega
 theorem owner_free (i : Fin 5) : owner (freeLabel i)=0 := by simp [owner,freeLabel]
 theorem owner_tail_nonzero (i : Fin 47) : owner (tailLabel i)≠0 := by
  simp only [owner,tailLabel]
  split_ifs <;> norm_num at * <;> omega

 /-- Actual selected B root, its retained five low-cell vertices, and all47
critical-tail vertices. Every vertex is embedded in the same physical host. -/
 structure Frame (c : Host) where
  root : Fin 61
  vertex : Fin 52 ↪ Fin 61
  ne_root : ∀ i,vertex i≠root
  spokes : ∀ i,c root (vertex i)=palette (owner i)
  low_degree : colorDegree c (palette 0) root=13
  selected : 47≤H c root
  marked_high : vertex 51 ∈ Incoming c root

 def support {c : Host} (f : Frame c) : Finset (Fin 61) := univ.image (fun i : Fin 5 => f.vertex (freeLabel i))
 def tailSet {c : Host} (f : Frame c) : Finset (Fin 61) := univ.image (fun i : Fin 47 => f.vertex (tailLabel i))
 def retained {c : Host} (f : Frame c) : Finset (Fin 61) := univ.image f.vertex

 theorem support_card {c : Host} (f : Frame c) : (support f).card=5 := by
  unfold support
  rw [card_image_of_injective _ (show Function.Injective (fun i : Fin 5 => f.vertex (freeLabel i)) from f.vertex.injective.comp freeLabel_injective)];simp
 theorem tail_card {c : Host} (f : Frame c) : (tailSet f).card=47 := by
  unfold tailSet
  rw [card_image_of_injective _ (show Function.Injective (fun i : Fin 47 => f.vertex (tailLabel i)) from f.vertex.injective.comp tailLabel_injective)];simp
 theorem support_subset {c : Host} (f : Frame c) : support f ⊆ colorNeighborhood c (palette 0) f.root := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  exact (mem_colorNeighborhood _ _ _ _).mpr ⟨f.ne_root _,(f.spokes _).trans (congrArg palette (owner_free i))⟩
 theorem tail_subset {c : Host} (f : Frame c) : tailSet f ⊆ criticalTail c f.root (palette 0) := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  apply mem_sdiff.mpr
  refine ⟨mem_erase.mpr ⟨f.ne_root _,mem_univ _⟩,?_⟩
  intro hm
  have hcol := ((mem_colorNeighborhood _ _ _ _).mp hm).2
  rw [f.spokes] at hcol
  exact owner_tail_nonzero i (palette_injective hcol)
 theorem actual_tail {c : Host} (f : Frame c) : tailSet f=criticalTail c f.root (palette 0) := by
  have hs : colorNeighborhood c (palette 0) f.root ⊆ (univ : Finset (Fin 61)).erase f.root := by
    intro v hv;exact mem_erase.mpr ⟨((mem_colorNeighborhood _ _ _ _).mp hv).1,mem_univ _⟩
  have hcard : (criticalTail c f.root (palette 0)).card=47 := by
    rw [criticalTail,card_sdiff_of_subset hs]
    change _-colorDegree c (palette 0) f.root=47
    rw [f.low_degree]
    simp
  exact eq_of_subset_of_card_le (tail_subset f) (by rw [tail_card,hcard])
 theorem retained_eq {c : Host} (f : Frame c) : retained f=retainedTailAndSupport c f.root (palette 0) (support f) := by
  rw [retainedTailAndSupport,←actual_tail]
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    by_cases hi : i.val<5
    · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨⟨i.val,hi⟩,mem_univ _,rfl⟩))
    · apply mem_union.mpr;left
      refine mem_image.mpr ⟨⟨i.val-5,by omega⟩,mem_univ _,?_⟩
      congr 1;apply Fin.ext;dsimp [tailLabel];omega
  · intro hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨tailLabel i,mem_univ _,rfl⟩
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨freeLabel i,mem_univ _,rfl⟩

 def retainedDegree {c : Host} (f : Frame c) (u : Fin 52) (q : Fin 4) : Nat :=
  (colorNeighborhood c (palette q) (f.vertex u) ∩ retained f).card
 def tailCount {c : Host} (f : Frame c) (u : Fin 52) (q : Fin 4) : Nat :=
  (colorNeighborhood c (palette q) (f.vertex u) ∩ tailSet f).card

 theorem tailCount_eq {c : Host} (f : Frame c) (u : Fin 52) (q : Fin 4) :
    tailCount f u q=tailDegree c f.root (palette 0) (f.vertex u) (palette q) := by rw [tailCount,actual_tail];rfl
 theorem free_mem {c : Host} (f : Frame c) (i : Fin 5) : f.vertex (freeLabel i) ∈ colorNeighborhood c (palette 0) f.root :=
  support_subset f (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
 theorem tail_mem {c : Host} (f : Frame c) (i : Fin 47) : f.vertex (tailLabel i) ∈ criticalTail c f.root (palette 0) :=
  tail_subset f (mem_image.mpr ⟨i,mem_univ _,rfl⟩)

 theorem free_bounds {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (i : Fin 5) (q : Fin 4) (hq : q≠0) :
    11≤tailCount f (freeLabel i) 0 ∧ tailCount f (freeLabel i) 0≤15 ∧
    7≤tailCount f (freeLabel i) q ∧ tailCount f (freeLabel i) q≤14 ∧
    22≤tailCount f (freeLabel i) 0+tailCount f (freeLabel i) q := by
  simp only [tailCount_eq]
  have h := free_vertex_tail_intervals c hc f.root (palette 0) (f.vertex (freeLabel i)) (free_mem f i)
    (palette q) (palette_injective.ne hq)
  rw [f.low_degree]at h
  omega
 theorem tail_nonzero_bounds {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (i : Fin 47) (q : Fin 4) (hq : q≠0) :
    6≤tailCount f (tailLabel i) q ∧ (q≠owner (tailLabel i) → 7≤tailCount f (tailLabel i) q) := by
  rw [tailCount_eq]
  have h := tail_vertex_nonzero_degree_lower c hc f.root (palette 0) (f.vertex (tailLabel i)) (palette q) (palette_injective.ne hq)
  refine ⟨h.1,?_⟩
  intro hqown
  exact h.2 (by rw [f.spokes];exact palette_injective.ne hqown)
 theorem tail_zero_bound {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (i : Fin 47) :
    4≤retainedDegree f (tailLabel i) 0 := by
  have h := tail_vertex_retained_low_degree c hc f.root (palette 0) (f.vertex (tailLabel i)) (tail_mem f i)
    (support f) (support_subset f)
  rw [support_card,f.low_degree,←retained_eq]at h
  change 12+5≤retainedDegree f (tailLabel i) 0+13 at h
  omega
 theorem surviving_high_count {c : Host} (f : Frame c) : 39≤(Incoming c f.root ∩ retained f).card := by
  have h := (supplied_ABD_surviving_high_counts c f.root (palette 0) (support f) (support_subset f)).2.1 f.low_degree f.selected
  rw [support_card,←retained_eq]at h
  exact h
 theorem high_free_proxy {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (i : Fin 5)
    (hi : f.vertex (freeLabel i) ∈ Incoming c f.root) : 14≤tailCount f (freeLabel i) 0 := by
  have hh := ((mem_highOwnNeighborSupport _ _ _).mp hi).2
  rw [f.spokes,owner_free]at hh
  rw [tailCount_eq]
  exact genuine_high_free_vertex_proxy c hc f.root (palette 0) _ (free_mem f i) hh
 theorem high_tail_proxy {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (i : Fin 47)
    (hi : f.vertex (tailLabel i) ∈ Incoming c f.root) : 9≤tailCount f (tailLabel i) (owner (tailLabel i)) := by
  have h := genuine_high_tail_vertex_proxy c hc f.root (palette 0) _ (tail_mem f i) hi
  rw [f.spokes]at h
  rwa [tailCount_eq]

#print axioms free_bounds
#print axioms surviving_high_count
#print axioms high_tail_proxy
end PricingABD.BPhysicalBounds
