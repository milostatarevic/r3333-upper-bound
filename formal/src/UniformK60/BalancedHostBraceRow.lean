import UniformK60.BalancedHostBraceFrame
import UniformK60.BalancedProjectedHost

/-! The projected finite action moves the real support by one automorphism
of the entire actual16-cell. The two low supports are merely reordered. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.BalancedHostBraceRow
open Ramsey61 Finset UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedGeometry UniformK60.BalancedProjectedHost
open UniformK60.BalancedHostBraceGeometry UniformK60.BalancedHostBraceFrame
open UniformK60.ThreeSupportFrame UniformK60.NativeCatalogue CompletionC.NativeMatrices

private theorem inverse_group (g : Geometry) (i : Fin 600) (a : Fin 15) :
    BalancedProjectedData.group (geometryShape g) (inverse g i a)=BalancedProjectedData.group (geometryShape g) a := by
  have h := (structural g i).2.2.2.2.2.1 (inverse g i a)
  rw [(structural g i).2.2.2.2.1] at h
  exact h.symm

theorem reordered_mem {c : Host} (g : Geometry)
    (f : Frame c (geometryShape g).free (geometryShape g).left (geometryShape g).right)
    (p : Equiv.Perm (Fin (geometryShape g).free)) (a : Fin (geometryShape g).dimension) :
    reorderedVertex (geometryShape g) f p a∈colorNeighborhood c
      (palette (BalancedProjectedData.group (geometryShape g) (Fin.castLE (geometry_dimensions g).2.1 a))) f.root := by
  rw [reorderedVertex_formula]
  unfold BalancedProjectedData.group
  by_cases h0 : a.val<(geometryShape g).free
  · simp only [Fin.coe_castLE,if_pos h0,dif_pos h0]
    exact f.free_mem _
  · simp only [Fin.coe_castLE,if_neg h0,dif_neg h0]
    by_cases h1 : a.val<(geometryShape g).free+(geometryShape g).left
    · have h1' : a.val<(geometryShape g).free+5 := by rw [←(geometry_dimensions g).1];exact h1
      simp only [dif_pos h1,if_pos h1']
      exact f.left_mem _
    · have h1' : ¬a.val<(geometryShape g).free+5 := by rw [←(geometry_dimensions g).1];exact h1
      simp only [dif_neg h1,if_neg h1',if_pos a.isLt]
      exact f.right_mem _

theorem reordered_marked {c : Host} (g : Geometry)
    (f : Frame c (geometryShape g).free (geometryShape g).left (geometryShape g).right)
    (p : Equiv.Perm (Fin (geometryShape g).free)) (a : Fin (geometryShape g).dimension) :
    c f.mark (reorderedVertex (geometryShape g) f p a)=palette 3 := by
  rw [reorderedVertex_formula]
  split_ifs
  · exact f.marked_free _
  · exact f.marked_left _
  · exact f.marked_right _

theorem row_mem {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600)
    (v : Fin (rowShape (target g i)).dimension) :
    rowEmbedding g a.frame p i v∈colorNeighborhood c
      (palette (BalancedProjectedData.group (rowShape (target g i)) (rowPadded g i v))) root := by
  have hm := reordered_mem g a.frame p (nativeOfRow g i v)
  change rowEmbedding g a.frame p i v∈colorNeighborhood c
    (palette (BalancedProjectedData.group (geometryShape g) (inverse g i (rowPadded g i v)))) a.frame.root at hm
  rw [inverse_group,a.root_eq,←(structural g i).1] at hm
  exact hm

theorem row_marked {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600)
    (v : Fin (rowShape (target g i)).dimension) :
    c mark (rowEmbedding g a.frame p i v)=palette 3 := by
  have h := reordered_marked g a.frame p (nativeOfRow g i v)
  rw [a.mark_eq] at h
  exact h

def freeIndex (r : Row) (j : Fin (rowShape r).free) : Fin (rowShape r).dimension :=
  ⟨j.val,by have h:=Shape.dimension_sum (rowShape r);have hj:=j.isLt;omega⟩
def fakeIndex (r : Row) (j : Fin 5) : Fin (rowShape r).dimension :=
  ⟨(rowShape r).free+j.val,by
    have h:=Shape.dimension_sum (rowShape r);have h5:=(row_dimensions r).1;have hj:=j.isLt;omega⟩
def realIndex (r : Row) (j : Fin (rowShape r).right) : Fin (rowShape r).dimension :=
  ⟨(rowShape r).free+5+j.val,by
    have h:=Shape.dimension_sum (rowShape r);have h5:=(row_dimensions r).1;have hj:=j.isLt;omega⟩

theorem freeIndex_injective (r : Row) : Function.Injective (freeIndex r) := by
  intro a b h;apply Fin.ext
  exact congrArg (fun v : Fin (rowShape r).dimension => v.val) h
theorem fakeIndex_injective (r : Row) : Function.Injective (fakeIndex r) := by
  intro a b h;apply Fin.ext;have hh:=congrArg Fin.val h;change _+a.val=_+b.val at hh;omega

set_option maxRecDepth 100000 in
theorem group_free : ∀ r j,BalancedProjectedData.group (rowShape r) (Fin.castLE (row_dimensions r).2.1 (freeIndex r j))=0 := by decide
set_option maxRecDepth 100000 in
theorem group_fake : ∀ r j,BalancedProjectedData.group (rowShape r) (Fin.castLE (row_dimensions r).2.1 (fakeIndex r j))=1 := by decide

noncomputable def rowFree {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600) :
    Fin (rowShape (target g i)).free↪Vertex :=
  ⟨fun j => rowEmbedding g a.frame p i (freeIndex (target g i) j),
    (rowEmbedding g a.frame p i).injective.comp (freeIndex_injective _)⟩
noncomputable def rowFake {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600) :
    Fin 5↪Vertex :=
  ⟨fun j => rowEmbedding g a.frame p i (fakeIndex (target g i) j),
    (rowEmbedding g a.frame p i).injective.comp (fakeIndex_injective _)⟩

theorem rowFree_image {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600) :
    univ.image (rowFree a p i)=support c root mark 0 := by
  have hsub : univ.image (rowFree a p i)⊆support c root mark 0 := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hv
    have hm := row_mem a p i (freeIndex (target g i) j)
    dsimp only [rowPadded] at hm
    rw [group_free] at hm
    have hmark : mark∈colorNeighborhood c (palette 3) root := by
      simpa only [a.root_eq,a.mark_eq] using a.frame.mark_mem
    have hne := distinct_root_cells hm hmark (by decide)
    exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr
      ⟨hne,row_marked a p i _⟩,hm⟩
  apply eq_of_subset_of_card_le hsub
  rw [←a.free_image,card_image_of_injective _ a.frame.free.injective,
    card_image_of_injective _ (rowFree a p i).injective,card_univ,card_univ,Fintype.card_fin,Fintype.card_fin,
    (structural g i).1]

theorem rowFake_image {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600) :
    univ.image (rowFake a p i)=support c root mark 1 := by
  have hsub : univ.image (rowFake a p i)⊆support c root mark 1 := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hv
    have hm := row_mem a p i (fakeIndex (target g i) j)
    dsimp only [rowPadded] at hm
    rw [group_fake] at hm
    have hmark : mark∈colorNeighborhood c (palette 3) root := by
      simpa only [a.root_eq,a.mark_eq] using a.frame.mark_mem
    have hne := distinct_root_cells hm hmark (by decide)
    exact mem_inter.mpr ⟨(mem_colorNeighborhood _ _ _ _).mpr
      ⟨hne,row_marked a p i _⟩,hm⟩
  apply eq_of_subset_of_card_le hsub
  rw [←a.fake_image,card_image_of_injective _ a.frame.left.injective,
    card_image_of_injective _ (rowFake a p i).injective,card_univ,card_univ,Fintype.card_fin,Fintype.card_fin,
    (geometry_dimensions g).1]

noncomputable def rowReal {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (i : Fin 600) :
    PhysicalNeighborhoodMap c root (palette 2) (R4333.k16Template (rowKind (target g i))) where
  vertex := (realEquiv g i).symm.toEmbedding.trans a.real.vertex
  mem_neighborhood j := a.real.mem_neighborhood _
  covers_neighborhood v hv := by
    obtain ⟨j,hj⟩ := a.real.covers_neighborhood v hv
    exact ⟨realEquiv g i j,by simpa using hj⟩
  colors := a.real.colors
  map_color u v huv := by
    change c (a.real.vertex ((realEquiv g i).symm u))
      (a.real.vertex ((realEquiv g i).symm v))=_
    rw [a.real.map_color _ _ ((realEquiv g i).symm.injective.ne huv)]
    have hp := realEquiv_preserves g i ((realEquiv g i).symm u)
      ((realEquiv g i).symm v) ((realEquiv g i).symm.injective.ne huv)
    simp only [Equiv.apply_symm_apply] at hp
    rw [←hp,(structural g i).2.1]

theorem rowReal_palette {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (i : Fin 600) :
    (rowReal a i).colors=foreignEquiv 2 := a.real_palette

private theorem real_group (g : Geometry) (j : Fin 5) (hj : j.val<(geometryShape g).right) :
    BalancedProjectedData.group (geometryShape g) (BalancedProjectedFinite.realIndex g j)=2 := by
  have hd := Shape.dimension_sum (geometryShape g)
  have hl := (geometry_dimensions g).1
  have h0 : ¬(geometryShape g).free+5+j.val<(geometryShape g).free := by omega
  have h1 : ¬(geometryShape g).free+5+j.val<(geometryShape g).free+5 := by omega
  have h2 : (geometryShape g).free+5+j.val<(geometryShape g).dimension := by omega
  simp only [BalancedProjectedData.group,BalancedProjectedFinite.realIndex,Fin.val_mk,if_neg h0,if_neg h1,if_pos h2]

/-- Exact agreement of the projected real-support labels with a coordinate
change of the whole physical16-cell, not just a support-only bijection. -/
theorem row_real_vertex {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free))
    (i : Fin 600) (j : Fin (rowShape (target g i)).right) :
    rowEmbedding g a.frame p i (realIndex (target g i) j)=
      (rowReal a i).vertex (rowRealSupport (target g i)
        ⟨j.val,by have h:=(row_dimensions (target g i)).2.2;have hj:=j.isLt;omega⟩) := by
  have hs := (structural g i).1
  let jj : Fin 5 := ⟨j.val,by have h:=(row_dimensions (target g i)).2.2;have hj:=j.isLt;omega⟩
  have hj : jj.val<(geometryShape g).right := by change j.val<_ ;rw [←hs];exact j.isLt
  let v := inverse g i (BalancedProjectedFinite.realIndex g jj)
  have hg : BalancedProjectedData.group (geometryShape g) v=2 :=
    (inverse_group g i _).trans (real_group g jj hj)
  have h0 : ¬v.val<(geometryShape g).free := by
    intro h;simp [BalancedProjectedData.group,h] at hg
  have h1 : ¬v.val<(geometryShape g).free+5 := by
    intro h;simp [BalancedProjectedData.group,h0,h] at hg
  have h2 : v.val<(geometryShape g).dimension := by
    by_contra h;simp [BalancedProjectedData.group,h0,h1,h] at hg
  have hleft := (geometry_dimensions g).1
  have hsum := Shape.dimension_sum (geometryShape g)
  have hright := (geometry_dimensions g).2.2
  have hdiff : v.val-(geometryShape g).free-5<(geometryShape g).right := by omega
  have h5 : v.val-((geometryShape g).free+5)<5 := by omega
  have hv : (nativeOfRow g i (realIndex (target g i) j)).val=v.val := by
    change (inverse g i (rowPadded g i (realIndex (target g i) j))).val=v.val
    have he : rowPadded g i (realIndex (target g i) j)=BalancedProjectedFinite.realIndex g jj := by
      apply Fin.ext
      change (rowShape (target g i)).free+5+j.val=(geometryShape g).free+5+jj.val
      rw [congrArg Shape.free hs]
    rw [he]
  change reorderedVertex (geometryShape g) a.frame p (nativeOfRow g i (realIndex (target g i) j))=_
  rw [reorderedVertex_formula]
  have hn0 : ¬(nativeOfRow g i (realIndex (target g i) j)).val<(geometryShape g).free := by rw [hv];exact h0
  have hn1 : ¬(nativeOfRow g i (realIndex (target g i) j)).val<
      (geometryShape g).free+(geometryShape g).left := by rw [hv,hleft];exact h1
  simp only [dif_neg hn0,dif_neg hn1]
  rw [a.real_vertex]
  change a.real.vertex (realOrder g _) = a.real.vertex ((realEquiv g i).symm (rowRealSupport (target g i) jj))
  rw [inverse_real_coordinates g i jj hj]
  apply congrArg a.real.vertex
  unfold realOrder
  apply congrArg (geometryRealOrder g)
  apply Fin.ext
  change (nativeOfRow g i (realIndex (target g i) j)).val-(geometryShape g).free-(geometryShape g).left=
    (v.val-((geometryShape g).free+5))%5
  rw [hv,hleft,Nat.mod_eq_of_lt h5]
  omega

#print axioms row_real_vertex
end UniformK60.BalancedHostBraceRow
