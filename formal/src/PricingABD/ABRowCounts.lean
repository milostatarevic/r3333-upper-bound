import PricingABD.ABPhysicalBounds
import PricingIntegration.NativePrimary

set_option autoImplicit false
namespace PricingABD.ABRowCounts
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore Finset PricingABD.ABLayout PricingABD.ABPhysicalBounds
open PricingIntegration.NativePrimary PricingIntegration.FoldedThreshold

def allLabels (l : Layout) : List (Fin (vertexCount l)) := List.finRange (vertexCount l)
def tailLabels (l : Layout) : List (Fin (vertexCount l)) := (List.finRange (tailSize l)).map (ABLayout.tail l)
 theorem all_row_count {c : Host} {l : Layout} (f : Frame c l) (u : Fin (vertexCount l)) (q : Fin 4) :
    count (primary f) (row (allLabels l) u q)=retainedDegree f u q := by
  change count (primary f) (row (List.finRange (vertexCount l)) u q)=_
  rw [row_count f _ (List.nodup_finRange (vertexCount l))]
  simp [physicalSet,retainedDegree,retained]
 theorem tail_row_count {c : Host} {l : Layout} (f : Frame c l) (u : Fin (vertexCount l)) (q : Fin 4) :
    count (primary f) (row (tailLabels l) u q)=tailCount f u q := by
  change count (primary f) (row ((List.finRange (tailSize l)).map (ABLayout.tail l)) u q)=_
  rw [row_count f _ (List.nodup_finRange (tailSize l) |>.map (ABLayout.tail_injective l))]
  unfold tailCount
  congr 2
  ext x
  simp only [physicalSet,tailSet,Finset.mem_image,List.mem_toFinset,List.mem_map,List.mem_finRange,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨v,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨ABLayout.tail l i,⟨i,rfl⟩,rfl⟩
 theorem high_count {c : Host} {l : Layout} (f : Frame c l) :
    count (primary f) ((allLabels l).map (fun u => (true,high l u)))=(Incoming c f.root ∩ retained f).card := by
  classical
  simp only [count,List.countP_map,Function.comp_def,value,boolTrue]
  have heq : List.countP (fun u => primary f (high l u)) (allLabels l) =
      List.countP (fun u => decide (f.vertex u ∈ Incoming c f.root)) (allLabels l) := by
    apply List.countP_congr
    intro u hu
    simpa using primary_high f u
  rw [heq,List.countP_eq_length_filter]
  let ls := (allLabels l).filter (fun u => decide (f.vertex u∈Incoming c f.root))
  have hn : ls.Nodup := (List.nodup_finRange (vertexCount l)).filter _
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

#print axioms tail_row_count
#print axioms high_count
end PricingABD.ABRowCounts
