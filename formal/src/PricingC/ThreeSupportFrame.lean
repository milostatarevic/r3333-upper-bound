import PricingC.Rooted555PhysicalComplete
import PricingC.Rooted45PhysicalComplete
import PricingABD.Rooted455Free

namespace PricingC.ThreeSupportFrame
open Ramsey61 Ramsey61.CEncodingCore
open PricingC.Rooted45Orientation (Cycle)

/-- One actual root and high marked vertex, three disjoint root-cell supports,
and the original ordered foreignP4/C5 patterns. No free-row pattern or
abstract compatible coloring is assumed. -/
structure Frame (c:Host) (nf nl nr:Nat) where
 root:Vertex
 mark:Vertex
 free:Fin nf↪Vertex
 left:Fin nl↪Vertex
 right:Fin nr↪Vertex
 mark_mem:mark∈colorNeighborhood c (palette 3) root
 free_mem:∀i,free i∈colorNeighborhood c (palette 0) root
 left_mem:∀i,left i∈colorNeighborhood c (palette 1) root
 right_mem:∀i,right i∈colorNeighborhood c (palette 2) root
 marked_free:∀i,c mark (free i)=palette 3
 marked_left:∀i,c mark (left i)=palette 3
 marked_right:∀i,c mark (right i)=palette 3
 left_edges:∀i j,i≠j → c (left i) (left j)=(if Cycle nl i.val j.val then palette 0 else palette 2)
 right_edges:∀i j,i≠j → c (right i) (right j)=(if Cycle nr i.val j.val then palette 0 else palette 1)

abbrev Parts (nf nl nr:Nat):=Fin nf ⊕ (Fin nl ⊕ (Fin nr ⊕ Fin 1))
abbrev order (nf nl nr:Nat):=nf+(nl+(nr+1))

def indexEquiv (nf nl nr:Nat):Parts nf nl nr≃Fin (order nf nl nr):=
 (Equiv.sumCongr (Equiv.refl (Fin nf))
  ((Equiv.sumCongr (Equiv.refl (Fin nl)) (finSumFinEquiv:Fin nr⊕Fin 1≃Fin (nr+1))).trans
   (finSumFinEquiv:Fin nl⊕Fin (nr+1)≃Fin (nl+(nr+1))))).trans finSumFinEquiv

def label0 {nf nl nr:Nat} (i:Fin nf):Fin (order nf nl nr):=⟨i.val,by dsimp [order];omega⟩
def label1 {nf nl nr:Nat} (i:Fin nl):Fin (order nf nl nr):=⟨nf+i.val,by dsimp [order];omega⟩
def label2 {nf nl nr:Nat} (i:Fin nr):Fin (order nf nl nr):=⟨nf+(nl+i.val),by dsimp [order];omega⟩
def rootLabel (nf nl nr:Nat):Fin (order nf nl nr):=⟨nf+(nl+nr),by dsimp [order];omega⟩

theorem index_free {nf nl nr:Nat} (i:Fin nf):indexEquiv nf nl nr (Sum.inl i)=label0 i:=rfl
theorem index_left {nf nl nr:Nat} (i:Fin nl):indexEquiv nf nl nr (Sum.inr (Sum.inl i))=label1 i:=rfl
theorem index_right {nf nl nr:Nat} (i:Fin nr):indexEquiv nf nl nr (Sum.inr (Sum.inr (Sum.inl i)))=label2 i:=rfl
theorem index_root (nf nl nr:Nat):indexEquiv nf nl nr (Sum.inr (Sum.inr (Sum.inr 0)))=rootLabel nf nl nr:=rfl

def partsVertex {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr):Parts nf nl nr→Vertex:=
 Sum.elim f.free (Sum.elim f.left (Sum.elim f.right (fun _=>f.root)))

theorem parts_injective {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr):Function.Injective (partsVertex f):=by
 have hn0 i:f.free i≠f.root:=((mem_colorNeighborhood _ _ _ _).mp (f.free_mem i)).1
 have hn1 i:f.left i≠f.root:=((mem_colorNeighborhood _ _ _ _).mp (f.left_mem i)).1
 have hn2 i:f.right i≠f.root:=((mem_colorNeighborhood _ _ _ _).mp (f.right_mem i)).1
 have h01 i j:f.free i≠f.left j:=PricingABD.SupportTransport.distinct_root_cells (f.free_mem i) (f.left_mem j) (by decide)
 have h02 i j:f.free i≠f.right j:=PricingABD.SupportTransport.distinct_root_cells (f.free_mem i) (f.right_mem j) (by decide)
 have h12 i j:f.left i≠f.right j:=PricingABD.SupportTransport.distinct_root_cells (f.left_mem i) (f.right_mem j) (by decide)
 intro a b hab
 rcases a with a|a|a|a <;> rcases b with b|b|b|b
 all_goals simp only [partsVertex,Sum.elim_inl,Sum.elim_inr] at hab
 · exact congrArg Sum.inl (f.free.injective hab)
 · exact False.elim (h01 _ _ hab)
 · exact False.elim (h02 _ _ hab)
 · exact False.elim (hn0 _ hab)
 · exact False.elim (h01 _ _ hab.symm)
 · exact congrArg (Sum.inr∘Sum.inl) (f.left.injective hab)
 · exact False.elim (h12 _ _ hab)
 · exact False.elim (hn1 _ hab)
 · exact False.elim (h02 _ _ hab.symm)
 · exact False.elim (h12 _ _ hab.symm)
 · exact congrArg (Sum.inr∘Sum.inr∘Sum.inl) (f.right.injective hab)
 · exact False.elim (hn2 _ hab)
 · exact False.elim (hn0 _ hab.symm)
 · exact False.elim (hn1 _ hab.symm)
 · exact False.elim (hn2 _ hab.symm)
 · congr 3;exact Subsingleton.elim _ _

noncomputable def physical {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr):Fin (order nf nl nr)↪Vertex:=
 (indexEquiv nf nl nr).symm.toEmbedding.trans ⟨partsVertex f,parts_injective f⟩

@[simp] theorem physical_free {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i:Fin nf):physical f (label0 i)=f.free i:=by
 change partsVertex f ((indexEquiv nf nl nr).symm (label0 i))=_
 rw[←index_free,Equiv.symm_apply_apply];rfl
@[simp] theorem physical_left {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i:Fin nl):physical f (label1 i)=f.left i:=by
 change partsVertex f ((indexEquiv nf nl nr).symm (label1 i))=_
 rw[←index_left,Equiv.symm_apply_apply];rfl
@[simp] theorem physical_right {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i:Fin nr):physical f (label2 i)=f.right i:=by
 change partsVertex f ((indexEquiv nf nl nr).symm (label2 i))=_
 rw[←index_right,Equiv.symm_apply_apply];rfl
@[simp] theorem physical_root {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr):physical f (rootLabel nf nl nr)=f.root:=by
 change partsVertex f ((indexEquiv nf nl nr).symm (rootLabel nf nl nr))=_
 rw[←index_root,Equiv.symm_apply_apply];rfl

theorem label_cases {nf nl nr:Nat} (i:Fin (order nf nl nr)):
 i=rootLabel nf nl nr ∨ (∃j,i=label0 j) ∨ (∃j,i=label1 j) ∨ ∃j,i=label2 j:=by
 obtain ⟨a,rfl⟩:=(indexEquiv nf nl nr).surjective i
 rcases a with a|a|a|a
 · exact Or.inr (Or.inl ⟨a,index_free a⟩)
 · exact Or.inr (Or.inr (Or.inl ⟨a,index_left a⟩))
 · exact Or.inr (Or.inr (Or.inr ⟨a,index_right a⟩))
 · left;have ha:a=0:=Subsingleton.elim _ _;rw[ha,index_root]

theorem physical_marked {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i:Fin (order nf nl nr)):
 c f.mark (physical f i)=palette 3:=by
 rcases label_cases i with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · rw[physical_root,c.color_symm];exact ((mem_colorNeighborhood _ _ _ _).mp f.mark_mem).2
 · rw[physical_free];exact f.marked_free i
 · rw[physical_left];exact f.marked_left i
 · rw[physical_right];exact f.marked_right i

theorem physical_ne_mark {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr) (i:Fin (order nf nl nr)):
 f.mark≠physical f i:=by
 rcases label_cases i with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · rw[physical_root];exact ((mem_colorNeighborhood _ _ _ _).mp f.mark_mem).1
 · rw[physical_free];exact PricingABD.SupportTransport.distinct_root_cells f.mark_mem (f.free_mem i) (by decide)
 · rw[physical_left];exact PricingABD.SupportTransport.distinct_root_cells f.mark_mem (f.left_mem i) (by decide)
 · rw[physical_right];exact PricingABD.SupportTransport.distinct_root_cells f.mark_mem (f.right_mem i) (by decide)

theorem physical_avoids_three {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr)
 (hc:NoMonochromaticTriangle c) (i j:Fin (order nf nl nr)) (hij:i≠j):
 c (physical f i) (physical f j)≠palette 3:=by
 intro he
 exact hc f.mark (physical f i) (physical f j)
  ⟨physical_ne_mark f i,physical_ne_mark f j,(physical f).injective.ne hij⟩
  ⟨(physical_marked f i).trans (physical_marked f j).symm,(physical_marked f j).trans he.symm⟩

open PricingABD.P15PhysicalRooted (threeIndex threeIndex_palette palette_threeIndex threeIndex_injective_on)
noncomputable def restoredColoring {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr):
 R4333.EdgeColoring (Fin (order nf nl nr)) (Fin 3) where
 color i j:=threeIndex (c (physical f i) (physical f j))
 color_symm i j:=congrArg threeIndex (c.color_symm _ _)

theorem restored_good {c:Host} {nf nl nr:Nat} (f:Frame c nf nl nr)
 (hc:NoMonochromaticTriangle c):R4333.NoMonochromaticTriangle (restoredColoring f):=by
 intro a b d hd hm
 apply hc (physical f a) (physical f b) (physical f d)
  ⟨(physical f).injective.ne hd.1,(physical f).injective.ne hd.2.1,(physical f).injective.ne hd.2.2⟩
 exact ⟨threeIndex_injective_on (physical_avoids_three f hc a b hd.1) (physical_avoids_three f hc a d hd.2.1) hm.1,
  threeIndex_injective_on (physical_avoids_three f hc a d hd.2.1) (physical_avoids_three f hc b d hd.2.2) hm.2⟩

#print axioms restored_good
end PricingC.ThreeSupportFrame
