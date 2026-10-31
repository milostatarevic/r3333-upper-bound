import UniformK60.BalancedHostBraceRow
import UniformK60.BalancedProjectedRowSupport

set_option autoImplicit false
namespace UniformK60.BalancedHostBraceRealSupport
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedGeometry UniformK60.BalancedProjectedHost
open UniformK60.BalancedHostBraceGeometry UniformK60.BalancedHostBraceFrame
open UniformK60.BalancedHostBraceRow UniformK60.ThreeSupportFrame

/-- The selected row support is the whole actual real-cell marked support,
including the negative membership information at every other real vertex. -/
theorem real_image {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600) :
    univ.image (fun j : Fin (rowShape (target g i)).right =>
      (rowReal a i).vertex (BalancedProjectedRowSupport.realOrder (target g i) j))=
      support c root mark 2 := by
  have hmark : mark∈colorNeighborhood c (palette 3) root := by
    simpa only [a.root_eq,a.mark_eq] using a.frame.mark_mem
  have hsub : univ.image (fun j : Fin (rowShape (target g i)).right =>
      (rowReal a i).vertex (BalancedProjectedRowSupport.realOrder (target g i) j))⊆
      support c root mark 2 := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hv
    have hm := (rowReal a i).mem_neighborhood (BalancedProjectedRowSupport.realOrder (target g i) j)
    have hne := distinct_root_cells hm hmark (by decide)
    have he := row_marked a p i (realIndex (target g i) j)
    rw [row_real_vertex] at he
    exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr ⟨hne,he⟩,hm⟩
  have hcount : (support c root mark 2).card=(geometryShape g).right := by
    have he := congrArg Finset.card (ClassificationSupports.support_image (side:=true) a.real hmark)
    rw [card_image_of_injective _ a.real.vertex.injective,a.real_support] at he
    have hg : (geometrySupport g).card=(geometryShape g).right := by
      rw [geometrySupport,card_image_of_injective _ (realOrder_injective g),card_univ,Fintype.card_fin]
    exact he.symm.trans hg
  apply eq_of_subset_of_card_le hsub
  have hinj : Function.Injective (fun j : Fin (rowShape (target g i)).right =>
      (rowReal a i).vertex (BalancedProjectedRowSupport.realOrder (target g i) j)) := by
    intro x y h
    exact BalancedProjectedRowSupport.realOrder_injective _ ((rowReal a i).vertex.injective h)
  rw [hcount,card_image_of_injective _ hinj,card_univ,Fintype.card_fin,
    congrArg CompletionC.NativeMatrices.Shape.right (structural g i).1]

#print axioms real_image
end UniformK60.BalancedHostBraceRealSupport
