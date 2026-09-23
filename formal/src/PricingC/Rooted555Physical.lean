import PricingC.Rooted555Free
import PricingABD.P15PhysicalRooted

namespace PricingC.Rooted555
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.P15PhysicalRooted (threeIndex palette_threeIndex threeIndex_injective_on)

/-- Concrete physical555 support data. The two foreign C5 orders are fixed;
the free five-set has no prescribed internal pattern. All lie in the same
marked color3 neighborhood and in their actual root-color cells. -/
structure Physical555 (c : Host) where
 root : Vertex
 mark : Vertex
 own : Fin 5 ↪ Vertex
 left : Fin 5 ↪ Vertex
 right : Fin 5 ↪ Vertex
 mark_mem : mark ∈ colorNeighborhood c (palette 3) root
 own_mem : ∀i,own i ∈ colorNeighborhood c (palette 0) root
 left_mem : ∀i,left i ∈ colorNeighborhood c (palette 1) root
 right_mem : ∀i,right i ∈ colorNeighborhood c (palette 2) root
 marked_own : ∀i,c mark (own i)=palette 3
 marked_left : ∀i,c mark (left i)=palette 3
 marked_right : ∀i,c mark (right i)=palette 3
 left_edges : ∀i j,i≠j → c (left i) (left j)=palette (Fin.castLE (by decide) (canonical1 i j))
 right_edges : ∀i j,i≠j → c (right i) (right j)=palette (Fin.castLE (by decide) (canonical2 i j))

abbrev Parts := Fin 5 ⊕ (Fin 5 ⊕ (Fin 5 ⊕ Fin 1))

def partIndex : Parts ≃ Fin 16 :=
 (Equiv.sumCongr (Equiv.refl (Fin 5))
  ((Equiv.sumCongr (Equiv.refl (Fin 5)) (finSumFinEquiv : Fin 5 ⊕ Fin 1 ≃ Fin 6)).trans
   (finSumFinEquiv : Fin 5 ⊕ Fin 6 ≃ Fin 11))).trans
   (finSumFinEquiv : Fin 5 ⊕ Fin 11 ≃ Fin 16)

@[simp] theorem partIndex_own (i : Fin 5) : partIndex (Sum.inl i)=label0 i := rfl
@[simp] theorem partIndex_left (i : Fin 5) : partIndex (Sum.inr (Sum.inl i))=label1 i := rfl
@[simp] theorem partIndex_right (i : Fin 5) : partIndex (Sum.inr (Sum.inr (Sum.inl i)))=label2 i := by
 apply Fin.ext
 simp [partIndex,label2,finSumFinEquiv]
 omega
@[simp] theorem partIndex_root : partIndex (Sum.inr (Sum.inr (Sum.inr 0)))=15 := rfl

def partsVertex {c : Host} (f : Physical555 c) : Parts → Vertex :=
 Sum.elim f.own (Sum.elim f.left (Sum.elim f.right (fun _ => f.root)))

theorem partsVertex_injective {c : Host} (f : Physical555 c) : Function.Injective (partsVertex f) := by
 have hn0 i : f.own i≠f.root := ((mem_colorNeighborhood _ _ _ _).mp (f.own_mem i)).1
 have hn1 i : f.left i≠f.root := ((mem_colorNeighborhood _ _ _ _).mp (f.left_mem i)).1
 have hn2 i : f.right i≠f.root := ((mem_colorNeighborhood _ _ _ _).mp (f.right_mem i)).1
 have hd01 i j : f.own i≠f.left j := PricingABD.SupportTransport.distinct_root_cells (f.own_mem i) (f.left_mem j) (by decide)
 have hd02 i j : f.own i≠f.right j := PricingABD.SupportTransport.distinct_root_cells (f.own_mem i) (f.right_mem j) (by decide)
 have hd12 i j : f.left i≠f.right j := PricingABD.SupportTransport.distinct_root_cells (f.left_mem i) (f.right_mem j) (by decide)
 intro a b hab
 rcases a with a|a|a|a <;> rcases b with b|b|b|b
 all_goals simp only [partsVertex,Sum.elim_inl,Sum.elim_inr] at hab
 · exact congrArg Sum.inl (f.own.injective hab)
 · exact False.elim (hd01 _ _ hab)
 · exact False.elim (hd02 _ _ hab)
 · exact False.elim (hn0 _ hab)
 · exact False.elim (hd01 _ _ hab.symm)
 · exact congrArg (Sum.inr ∘ Sum.inl) (f.left.injective hab)
 · exact False.elim (hd12 _ _ hab)
 · exact False.elim (hn1 _ hab)
 · exact False.elim (hd02 _ _ hab.symm)
 · exact False.elim (hd12 _ _ hab.symm)
 · exact congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) (f.right.injective hab)
 · exact False.elim (hn2 _ hab)
 · exact False.elim (hn0 _ hab.symm)
 · exact False.elim (hn1 _ hab.symm)
 · exact False.elim (hn2 _ hab.symm)
 · congr 3;exact Subsingleton.elim _ _

noncomputable def physical {c : Host} (f : Physical555 c) : Fin 16 ↪ Vertex :=
 partIndex.symm.toEmbedding.trans ⟨partsVertex f,partsVertex_injective f⟩

@[simp] theorem physical_own {c : Host} (f : Physical555 c) (i : Fin 5) : physical f (label0 i)=f.own i := by
 change partsVertex f (partIndex.symm (label0 i))=_
 rw [←partIndex_own,Equiv.symm_apply_apply]
 rfl
@[simp] theorem physical_left {c : Host} (f : Physical555 c) (i : Fin 5) : physical f (label1 i)=f.left i := by
 change partsVertex f (partIndex.symm (label1 i))=_
 rw [←partIndex_left,Equiv.symm_apply_apply]
 rfl
@[simp] theorem physical_right {c : Host} (f : Physical555 c) (i : Fin 5) : physical f (label2 i)=f.right i := by
 change partsVertex f (partIndex.symm (label2 i))=_
 rw [←partIndex_right,Equiv.symm_apply_apply]
 rfl
@[simp] theorem physical_root {c : Host} (f : Physical555 c) : physical f 15=f.root := by
 change partsVertex f (partIndex.symm 15)=_
 rw [←partIndex_root,Equiv.symm_apply_apply]
 rfl

theorem label_cases (i : Fin 16) : i=15 ∨ (∃j,i=label0 j) ∨ (∃j,i=label1 j) ∨ ∃j,i=label2 j := by
 obtain ⟨a,rfl⟩ := partIndex.surjective i
 rcases a with a|a|a|a
 · exact Or.inr (Or.inl ⟨a,partIndex_own a⟩)
 · exact Or.inr (Or.inr (Or.inl ⟨a,partIndex_left a⟩))
 · exact Or.inr (Or.inr (Or.inr ⟨a,partIndex_right a⟩))
 · left
   have ha:a=0 := Subsingleton.elim _ _
   rw [ha,partIndex_root]

theorem physical_marked {c : Host} (f : Physical555 c) (i : Fin 16) : c f.mark (physical f i)=palette 3 := by
 rcases label_cases i with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · rw [physical_root,c.color_symm]
   exact ((mem_colorNeighborhood _ _ _ _).mp f.mark_mem).2
 · rw [physical_own];exact f.marked_own i
 · rw [physical_left];exact f.marked_left i
 · rw [physical_right];exact f.marked_right i

theorem physical_ne_mark {c : Host} (f : Physical555 c) (i : Fin 16) : f.mark≠physical f i := by
 rcases label_cases i with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
 · rw [physical_root];exact ((mem_colorNeighborhood _ _ _ _).mp f.mark_mem).1
 · rw [physical_own];exact PricingABD.SupportTransport.distinct_root_cells f.mark_mem (f.own_mem i) (by decide)
 · rw [physical_left];exact PricingABD.SupportTransport.distinct_root_cells f.mark_mem (f.left_mem i) (by decide)
 · rw [physical_right];exact PricingABD.SupportTransport.distinct_root_cells f.mark_mem (f.right_mem i) (by decide)

theorem physical_avoids_three {c : Host} (f : Physical555 c) (hc : NoMonochromaticTriangle c)
 (i j : Fin 16) (hij:i≠j) : c (physical f i) (physical f j)≠palette 3 := by
 intro he
 exact hc f.mark (physical f i) (physical f j)
  ⟨physical_ne_mark f i,physical_ne_mark f j,(physical f).injective.ne hij⟩
  ⟨(physical_marked f i).trans (physical_marked f j).symm,(physical_marked f j).trans he.symm⟩

noncomputable def restoredColoring {c : Host} (f : Physical555 c) : R4333.EdgeColoring (Fin 16) (Fin 3) where
 color i j:=threeIndex (c (physical f i) (physical f j))
 color_symm i j:=congrArg threeIndex (c.color_symm _ _)

theorem restored_good {c : Host} (f : Physical555 c) (hc : NoMonochromaticTriangle c) :
 R4333.NoMonochromaticTriangle (restoredColoring f) := by
 intro a b d hd hm
 apply hc (physical f a) (physical f b) (physical f d)
  ⟨(physical f).injective.ne hd.1,(physical f).injective.ne hd.2.1,(physical f).injective.ne hd.2.2⟩
 exact ⟨threeIndex_injective_on (physical_avoids_three f hc a b hd.1) (physical_avoids_three f hc a d hd.2.1) hm.1,
  threeIndex_injective_on (physical_avoids_three f hc a d hd.2.1) (physical_avoids_three f hc b d hd.2.2) hm.2⟩

#print axioms restored_good
end PricingC.Rooted555
