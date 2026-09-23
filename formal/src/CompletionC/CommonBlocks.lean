import PricingABD.ABGeometry
import PricingIntegration.NativeSupportConsumers
set_option autoImplicit false
namespace CompletionC.CommonBlocks
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.BActualFrame

/-- Complete native critical cells and the entire actual low-cell support
of one genuine marked endpoint, all in the same host and palette. -/
structure Blocks (c:Host) (l:Layout) (types:Types) where
 root:Vertex
 free:Fin (freeSize l)↪Vertex
 left:PhysicalNeighborhoodMap c root (palette 1) (model (leftLarge l) types.left)
 right:PhysicalNeighborhoodMap c root (palette 2) (model (rightLarge l) types.right)
 marked:PhysicalNeighborhoodMap c root (palette 3) (R4333.k16Template types.marked)
 free_mem:∀i,free i∈colorNeighborhood c (palette 0) root
 left_palette:left.colors=foreignEquiv 1
 right_palette:right.colors=foreignEquiv 2
 marked_palette:marked.colors=foreignEquiv 3
 low_degree:colorDegree c (palette 0) root=lowSize l
 selected:tailSize l≤H c root
 marked_high:15≤colorDegree c (palette 3) (marked.vertex 15)
 free_own:∀i,c (marked.vertex 15) (free i)=palette 3
 free_exact:∀v,v∈attachingSupport c root (palette 3) (marked.vertex 15) (palette 0)↔∃i,free i=v

abbrev Parts (l:Layout):=Fin (freeSize l) ⊕ (Fin (leftSize l) ⊕ (Fin (rightSize l) ⊕ Fin 16))
def indexOwner {l:Layout}:Parts l→Fin 4
 | .inl _=>0
 | .inr (.inl _)=>1
 | .inr (.inr (.inl _))=>2
 | .inr (.inr (.inr _))=>3

def indexEquiv (l:Layout):Parts l≃Fin (vertexCount l):=
 ((Equiv.sumCongr (Equiv.refl (Fin (freeSize l)))
   ((Equiv.sumCongr (Equiv.refl (Fin (leftSize l))) finSumFinEquiv).trans finSumFinEquiv)).trans
  finSumFinEquiv).trans (finCongr (by unfold vertexCount tailSize;omega))

theorem index_free (l:Layout) (i:Fin (freeSize l)):
 indexEquiv l (.inl i)=ABLayout.free l i:=by
 apply Fin.ext
 simp [indexEquiv,ABLayout.free,finSumFinEquiv]
theorem index_left (l:Layout) (i:Fin (leftSize l)):
 indexEquiv l (.inr (.inl i))=ABLayout.left l i:=by
 apply Fin.ext
 simp [indexEquiv,ABLayout.left,ABLayout.leftStart,finSumFinEquiv]
theorem index_right (l:Layout) (i:Fin (rightSize l)):
 indexEquiv l (.inr (.inr (.inl i)))=ABLayout.right l i:=by
 apply Fin.ext
 simp [indexEquiv,ABLayout.right,ABLayout.rightStart,finSumFinEquiv,Nat.add_assoc]
theorem index_marked (l:Layout) (i:Fin 16):
 indexEquiv l (.inr (.inr (.inr i)))=ABLayout.marked l i:=by
 apply Fin.ext
 simp [indexEquiv,ABLayout.marked,ABLayout.markedStart,finSumFinEquiv,Nat.add_assoc]

theorem owner_index (l:Layout) (i:Parts l):ABLayout.owner l (indexEquiv l i)=indexOwner i:=by
 rcases i with i|i|i|i
 · rw[index_free];exact owner_free l i
 · rw[index_left];exact owner_left l i
 · rw[index_right];exact owner_right l i
 · rw[index_marked];exact owner_marked l i

def partsVertex {c:Host} {l:Layout} {types:Types} (b:Blocks c l types):Parts l→Vertex
 | .inl i=>b.free i
 | .inr (.inl i)=>b.left.vertex i
 | .inr (.inr (.inl i))=>b.right.vertex i
 | .inr (.inr (.inr i))=>b.marked.vertex i

theorem parts_mem {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (i:Parts l):
 partsVertex b i∈colorNeighborhood c (palette (indexOwner i)) b.root:=by
 rcases i with i|i|i|i
 · exact b.free_mem i
 · exact b.left.mem_neighborhood i
 · exact b.right.mem_neighborhood i
 · exact b.marked.mem_neighborhood i

private theorem same_block {l:Layout} (i j:Parts l) (h:indexOwner i=indexOwner j):
 (∃a b:Fin (freeSize l),i=.inl a ∧ j=.inl b) ∨
 (∃a b:Fin (leftSize l),i=.inr (.inl a) ∧ j=.inr (.inl b)) ∨
 (∃a b:Fin (rightSize l),i=.inr (.inr (.inl a)) ∧ j=.inr (.inr (.inl b))) ∨
 (∃a b:Fin 16,i=.inr (.inr (.inr a)) ∧ j=.inr (.inr (.inr b))):=by
 rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> simp_all [indexOwner]

theorem parts_injective {c:Host} {l:Layout} {types:Types} (b:Blocks c l types):
 Function.Injective (partsVertex b):=by
 intro i j he
 have ho:indexOwner i=indexOwner j:=by
  apply palette_injective
  exact (((mem_colorNeighborhood _ _ _ _).mp (parts_mem b i)).2.symm.trans
   (congrArg (c b.root) he)).trans (((mem_colorNeighborhood _ _ _ _).mp (parts_mem b j)).2)
 rcases same_block i j ho with ⟨u,v,rfl,rfl⟩|⟨u,v,rfl,rfl⟩|⟨u,v,rfl,rfl⟩|⟨u,v,rfl,rfl⟩
 · exact congrArg Sum.inl (b.free.injective he)
 · exact congrArg (fun a=>Sum.inr (Sum.inl a)) (b.left.vertex.injective he)
 · exact congrArg (fun a=>Sum.inr (Sum.inr (Sum.inl a))) (b.right.vertex.injective he)
 · exact congrArg (fun a=>Sum.inr (Sum.inr (Sum.inr a))) (b.marked.vertex.injective he)

noncomputable def physical {c:Host} {l:Layout} {types:Types} (b:Blocks c l types):Fin (vertexCount l)↪Vertex:=
 (indexEquiv l).symm.toEmbedding.trans ⟨partsVertex b,parts_injective b⟩

@[simp] theorem physical_free {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (i:Fin (freeSize l)):
 physical b (ABLayout.free l i)=b.free i:=by
 change partsVertex b ((indexEquiv l).symm (ABLayout.free l i))=_
 rw[←index_free,Equiv.symm_apply_apply];rfl
@[simp] theorem physical_left {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (i:Fin (leftSize l)):
 physical b (ABLayout.left l i)=b.left.vertex i:=by
 change partsVertex b ((indexEquiv l).symm (ABLayout.left l i))=_
 rw[←index_left,Equiv.symm_apply_apply];rfl
@[simp] theorem physical_right {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (i:Fin (rightSize l)):
 physical b (ABLayout.right l i)=b.right.vertex i:=by
 change partsVertex b ((indexEquiv l).symm (ABLayout.right l i))=_
 rw[←index_right,Equiv.symm_apply_apply];rfl
@[simp] theorem physical_marked {c:Host} {l:Layout} {types:Types} (b:Blocks c l types) (i:Fin 16):
 physical b (ABLayout.marked l i)=b.marked.vertex i:=by
 change partsVertex b ((indexEquiv l).symm (ABLayout.marked l i))=_
 rw[←index_marked,Equiv.symm_apply_apply];rfl

noncomputable def frame {c:Host} {l:Layout} {types:Types} (b:Blocks c l types):Frame c l where
 root:=b.root
 vertex:=physical b
 ne_root i:=((mem_colorNeighborhood _ _ _ _).mp (parts_mem b ((indexEquiv l).symm i))).1
 spokes:=by
  intro i
  change c b.root (partsVertex b ((indexEquiv l).symm i))=palette (ABLayout.owner l i)
  have h:=((mem_colorNeighborhood _ _ _ _).mp (parts_mem b ((indexEquiv l).symm i))).2
  simpa only [←owner_index,Equiv.apply_symm_apply] using h
 low_degree:=b.low_degree
 selected:=b.selected
 marked_high:=by
  change physical b (ABLayout.marked l 15)∈Incoming c b.root
  rw[physical_marked]
  have h:=(mem_colorNeighborhood _ _ _ _).mp (b.marked.mem_neighborhood 15)
  apply (mem_highOwnNeighborSupport _ _ _).mpr
  exact ⟨h.1,by simpa only[h.2] using b.marked_high⟩

private theorem native_palette (own:Fin 4) (q:Fin 3):
 (foreignEquiv own q).val=palette (ABGeometry.foreign own q):=by
 fin_cases own <;> fin_cases q <;> rfl

theorem left_edges {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (u v:Fin (leftSize l)) (huv:u≠v):
 c ((frame b).vertex (ABLayout.left l u)) ((frame b).vertex (ABLayout.left l v))=
 palette (ABGeometry.foreign 1 (model (leftLarge l) types.left u v)):=by
 change c (physical b _) (physical b _)=_
 rw[physical_left,physical_left,b.left.map_color u v huv,b.left_palette,native_palette]

theorem right_edges {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (u v:Fin (rightSize l)) (huv:u≠v):
 c ((frame b).vertex (ABLayout.right l u)) ((frame b).vertex (ABLayout.right l v))=
 palette (ABGeometry.foreign 2 (model (rightLarge l) types.right u v)):=by
 change c (physical b _) (physical b _)=_
 rw[physical_right,physical_right,b.right.map_color u v huv,b.right_palette,native_palette]

theorem marked_edges {c:Host} {l:Layout} {types:Types} (b:Blocks c l types)
 (u v:Fin 16) (huv:u≠v):
 c ((frame b).vertex (ABLayout.marked l u)) ((frame b).vertex (ABLayout.marked l v))=
 palette (ABGeometry.foreign 3 (R4333.k16Template types.marked u v)):=by
 change c (physical b _) (physical b _)=_
 rw[physical_marked,physical_marked,b.marked.map_color u v huv,b.marked_palette,native_palette]

#print axioms parts_injective
#print axioms frame
end CompletionC.CommonBlocks
