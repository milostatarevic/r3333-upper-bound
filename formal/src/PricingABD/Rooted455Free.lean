import PricingABD.Rooted455Entrance

namespace PricingABD.Rooted455Free
open R4333 PricingABD.TemplateNormalization PricingABD.Rooted455Data PricingABD.Rooted455Entrance

def canonicalPerm0 : Fin 10 → Fin 4 → Fin 4 := ![![1,2,0,3],![0,1,2,3],![0,1,2,3],![1,2,0,3],![1,0,3,2],![0,2,1,3],![2,1,0,3],![0,1,2,3],![2,1,0,3],![0,1,3,2]]
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem canonicalPerm0_bijective : ∀ r,Function.Bijective (canonicalPerm0 r) := by decide +kernel
noncomputable def canonicalEquiv0 (r : Fin 10) : Equiv.Perm (Fin 4) := Equiv.ofBijective (canonicalPerm0 r) (canonicalPerm0_bijective r)

theorem canonicalPerm0_colors : ∀ r : Fin 10, ∀ i j : Fin 4,i≠j →
    k15Template (rootTwisted r) (neighbor0 r (canonicalPerm0 r i)) (neighbor0 r (canonicalPerm0 r j))=canonical0 i j := by decide +kernel

def freeLift (p : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 15) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr p (Equiv.refl (Fin 11))).trans finSumFinEquiv)

theorem freeLift_label0 (p : Equiv.Perm (Fin 4)) (i : Fin 4) : freeLift p (label0 i)=label0 (p i) := by
  change freeLift p ((finSumFinEquiv : Fin 4 ⊕ Fin 11 ≃ Fin 15) (Sum.inl i))=(finSumFinEquiv : Fin 4 ⊕ Fin 11 ≃ Fin 15) (Sum.inl (p i))
  simp [freeLift]

theorem freeLift_ge4 (p : Equiv.Perm (Fin 4)) (i : Fin 15) (hi : 4 ≤ i.val) : freeLift p i=i := by
  have he : i=(finSumFinEquiv : Fin 4 ⊕ Fin 11 ≃ Fin 15) (Sum.inr (⟨i.val-4,by omega⟩ : Fin 11)) := by
    apply Fin.ext
    change i.val=4+(i.val-4)
    omega
  rw [he]
  simp [freeLift]

def relabelFree (c : EdgeColoring (Fin 15) ThreeColor) (p : Equiv.Perm (Fin 4)) : EdgeColoring (Fin 15) ThreeColor where
  color i j := c (freeLift p i) (freeLift p j)
  color_symm i j := c.color_symm _ _

theorem relabelFree_good (c : EdgeColoring (Fin 15) ThreeColor) (p : Equiv.Perm (Fin 4))
    (hc : NoMonochromaticTriangle c) : NoMonochromaticTriangle (relabelFree c p) := by
  intro a b d hd hm
  exact hc _ _ _ ⟨(freeLift p).injective.ne hd.1,(freeLift p).injective.ne hd.2.1,(freeLift p).injective.ne hd.2.2⟩ hm

/-- Only root spokes are needed to obtain the finite rooted template choice;
no P4 condition on the free block has been assumed. -/
theorem rooted_from_spokes (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (hs : ∀ i,i≠14 → c 14 i=group i) :
    ∃ r : Fin 10, ∃ e : Fin 15 ≃ Fin 15,e (rootVertex r)=14 ∧
      ∀ u v,u≠v → c (e u) (e v)=k15Template (rootTwisted r) u v := by
  have hd0 : colorDegree c 0 14=4 := by
    have hn : colorNeighborhood c 0 14 = {0,1,2,3} := by
      ext i;fin_cases i <;> simp [mem_colorNeighborhood,hs,group]
    unfold colorDegree;rw [hn];decide
  obtain ⟨t,e,he⟩ := k15_color_preserving_complete c hc
  have hd : colorDegree (k15Template t) 0 (e.symm 14)=4 := by
    rw [←degree_of_color_preserving c (k15Template t) e he,Equiv.apply_symm_apply];exact hd0
  obtain ⟨r,ht,hr⟩ := roots_complete t (e.symm 14) hd
  refine ⟨r,e,?_,?_⟩
  · rw [hr];exact e.apply_symm_apply _
  · rw [ht];exact he

/-- The arbitrary free four-set becomes the canonical P4 by reordering only
those same four physical vertices. This is derived from critical classification. -/
theorem free_P4_normalization (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (hs : ∀ i,i≠14 → c 14 i=group i) :
    ∃ p : Equiv.Perm (Fin 4),∀ i j,i≠j →
      (relabelFree c p) (label0 i) (label0 j)=canonical0 i j := by
  obtain ⟨r,e,hr,he⟩ := rooted_from_spokes c hc hs
  obtain ⟨p0,hp0⟩ := group_map hr he label0 label0_injective label0_ne_root 0
    (fun i => (hs _ (label0_ne_root i)).trans (group_label0 i))
    (neighbor0 r) (neighbor0_injective r) (neighbor0_complete r)
  let p := (canonicalEquiv0 r).trans p0.symm
  refine ⟨p,?_⟩
  intro i j hij
  change c (freeLift p (label0 i)) (freeLift p (label0 j))=_
  rw [freeLift_label0,freeLift_label0]
  have hne : e.symm (label0 (p i))≠e.symm (label0 (p j)) := e.symm.injective.ne (label0_injective.ne (p.injective.ne hij))
  have hh := he _ _ hne
  simp only [Equiv.apply_symm_apply] at hh
  rw [hh,hp0,hp0]
  change k15Template (rootTwisted r) (neighbor0 r (p0 (p0.symm (canonicalEquiv0 r i))))
      (neighbor0 r (p0 (p0.symm (canonicalEquiv0 r j))))=_
  simp only [Equiv.apply_symm_apply]
  exact canonicalPerm0_colors r i j hij

/-- Both foreign blocks retain their original labels and colors. -/
theorem whole_rooted_normalization (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (hs : ∀ i,i≠14 → c 14 i=group i)
    (h1 : ∀ i j,i≠j → c (label1 i) (label1 j)=canonical1 i j)
    (h2 : ∀ i j,i≠j → c (label2 i) (label2 j)=canonical2 i j) :
    ∃ p : Equiv.Perm (Fin 4),CanonicalRooted455 (relabelFree c p) := by
  obtain ⟨p,hp⟩ := free_P4_normalization c hc hs
  refine ⟨p,?_,hp,?_,?_⟩
  · intro i hi
    change c (freeLift p 14) (freeLift p i)=group i
    rw [freeLift_ge4 p 14 (by decide)]
    by_cases hlow : i.val < 4
    · have hx : i=label0 ⟨i.val,hlow⟩ := rfl
      rw [hx,freeLift_label0,hs _ (label0_ne_root _),group_label0,group_label0]
    · rw [freeLift_ge4 p i (by omega)]
      exact hs i hi
  · intro i j hij
    change c (freeLift p (label1 i)) (freeLift p (label1 j))=_
    rw [freeLift_ge4 p _ (by dsimp [label1];omega),freeLift_ge4 p _ (by dsimp [label1];omega)]
    exact h1 i j hij
  · intro i j hij
    change c (freeLift p (label2 i)) (freeLift p (label2 j))=_
    rw [freeLift_ge4 p _ (by dsimp [label2];omega),freeLift_ge4 p _ (by dsimp [label2];omega)]
    exact h2 i j hij

#print axioms free_P4_normalization
#print axioms whole_rooted_normalization
end PricingABD.Rooted455Free
