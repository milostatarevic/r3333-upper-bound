import PricingC.OwnFive15Data

namespace PricingC.OwnFive15
open R4333 PricingABD.TemplateNormalization

def label (i : Fin 5) : Fin 15 := ⟨i.val,by omega⟩
theorem label_injective : Function.Injective label := by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 15=>x.val) h
theorem label_ne_root (i : Fin 5) : label i≠14 := by intro h;have:=congrArg Fin.val h;dsimp [label] at this;omega

def freeLift (p : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 15) :=
 finSumFinEquiv.symm.trans ((Equiv.sumCongr p (Equiv.refl (Fin 10))).trans finSumFinEquiv)

theorem freeLift_label (p : Equiv.Perm (Fin 5)) (i : Fin 5) : freeLift p (label i)=label (p i) := by
 change freeLift p ((finSumFinEquiv : Fin 5 ⊕ Fin 10 ≃ Fin 15) (Sum.inl i))=(finSumFinEquiv : Fin 5 ⊕ Fin 10 ≃ Fin 15) (Sum.inl (p i))
 simp [freeLift]

theorem freeLift_ge5 (p : Equiv.Perm (Fin 5)) (i : Fin 15) (hi : 5 ≤ i.val) : freeLift p i=i := by
 have he : i=(finSumFinEquiv : Fin 5 ⊕ Fin 10 ≃ Fin 15) (Sum.inr (⟨i.val-5,by omega⟩ : Fin 10)) := by
  apply Fin.ext;change i.val=5+(i.val-5);omega
 rw [he]
 simp [freeLift]

def relabelFree (c : EdgeColoring (Fin 15) ThreeColor) (p : Equiv.Perm (Fin 5)) : EdgeColoring (Fin 15) ThreeColor :=
 relabelVertices c (freeLift p)

theorem relabelFree_good (c : EdgeColoring (Fin 15) ThreeColor) (p : Equiv.Perm (Fin 5))
 (hc:NoMonochromaticTriangle c) : NoMonochromaticTriangle (relabelFree c p) :=
 noMono_relabelVertices c (freeLift p) hc

/-- The only required incidence is that exactly the first five actual points
are joined to the actual root by color0. The two foreign blocks need not
have the same size, and neither is permuted by this operation. -/
theorem free_C5_normalization (c : EdgeColoring (Fin 15) ThreeColor)
 (hc:NoMonochromaticTriangle c)
 (hs:∀i,i≠14 → (c 14 i=0 ↔ i.val<5)) :
 ∃p:Equiv.Perm (Fin 5),∀i j,i≠j → (relabelFree c p) (label i) (label j)=canonical i j := by
 have hd0 : colorDegree c 0 14=5 := by
  have hn : colorNeighborhood c 0 14={0,1,2,3,4} := by
   ext i
   fin_cases i <;> simp [mem_colorNeighborhood,hs]
  unfold colorDegree
  rw [hn]
  decide
 obtain ⟨t,e,he⟩ := k15_color_preserving_complete c hc
 let r:=e.symm 14
 have hr:e r=14 := e.apply_symm_apply _
 have hd:colorDegree (k15Template t) 0 r=5 := by
  rw [←degree_of_color_preserving c (k15Template t) e he,hr]
  exact hd0
 obtain ⟨hinj,hcomplete,hcolors⟩ := ownOrder_properties t r hd
 obtain ⟨p0,hp0⟩ := PricingABD.Rooted455Entrance.factors_through_enumeration (ownOrder t r)
  (fun i=>e.symm (label i)) hinj (e.symm.injective.comp label_injective) (by
   intro i
   apply hcomplete _ (by intro hh;apply label_ne_root i;rw [←e.apply_symm_apply (label i),hh,hr])
   rw [←he _ _ (by intro h;apply label_ne_root i;rw [←e.apply_symm_apply (label i),←h,hr]),hr,Equiv.apply_symm_apply]
   exact (hs _ (label_ne_root i)).mpr i.isLt)
 refine ⟨p0.symm,?_⟩
 intro i j hij
 change c (freeLift p0.symm (label i)) (freeLift p0.symm (label j))=_
 rw [freeLift_label,freeLift_label]
 have hh := he (e.symm (label (p0.symm i))) (e.symm (label (p0.symm j)))
  (e.symm.injective.ne (label_injective.ne (p0.symm.injective.ne hij)))
 simp only [Equiv.apply_symm_apply] at hh
 rw [hh,hp0,hp0,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
 exact hcolors i j hij

#print axioms free_C5_normalization
end PricingC.OwnFive15
