import PricingC.Rooted555Entrance

namespace PricingC.Rooted555
open R4333 PricingABD.TemplateNormalization

def canonicalPerm0 : Fin 2 → Fin 5 → Fin 5 := ![![0,1,4,2,3],![0,1,4,2,3]]
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem canonicalPerm0_bijective : ∀ r,Function.Bijective (canonicalPerm0 r) := by decide +kernel
noncomputable def canonicalEquiv0 (r : Fin 2) : Equiv.Perm (Fin 5) := Equiv.ofBijective (canonicalPerm0 r) (canonicalPerm0_bijective r)

theorem canonicalPerm0_colors : ∀ r : Fin 2, ∀ i j : Fin 5,i≠j →
    k16Template (rootTwisted r) (neighbor0 r (canonicalPerm0 r i)) (neighbor0 r (canonicalPerm0 r j))=canonical0 i j := by decide +kernel

def freeLift (p : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 16) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr p (Equiv.refl (Fin 11))).trans finSumFinEquiv)

theorem freeLift_label0 (p : Equiv.Perm (Fin 5)) (i : Fin 5) : freeLift p (label0 i)=label0 (p i) := by
  change freeLift p ((finSumFinEquiv : Fin 5 ⊕ Fin 11 ≃ Fin 16) (Sum.inl i))=(finSumFinEquiv : Fin 5 ⊕ Fin 11 ≃ Fin 16) (Sum.inl (p i))
  simp [freeLift]

theorem freeLift_ge5 (p : Equiv.Perm (Fin 5)) (i : Fin 16) (hi : 5 ≤ i.val) : freeLift p i=i := by
  have he : i=(finSumFinEquiv : Fin 5 ⊕ Fin 11 ≃ Fin 16) (Sum.inr (⟨i.val-5,by omega⟩ : Fin 11)) := by
    apply Fin.ext
    change i.val=5+(i.val-5)
    omega
  rw [he]
  simp [freeLift]

def relabelFree (c : EdgeColoring (Fin 16) ThreeColor) (p : Equiv.Perm (Fin 5)) : EdgeColoring (Fin 16) ThreeColor where
  color i j := c (freeLift p i) (freeLift p j)
  color_symm i j := c.color_symm _ _

theorem relabelFree_good (c : EdgeColoring (Fin 16) ThreeColor) (p : Equiv.Perm (Fin 5))
    (hc : NoMonochromaticTriangle c) : NoMonochromaticTriangle (relabelFree c p) := by
  intro a b d hd hm
  exact hc _ _ _ ⟨(freeLift p).injective.ne hd.1,(freeLift p).injective.ne hd.2.1,(freeLift p).injective.ne hd.2.2⟩ hm

/-- The arbitrary free five-set becomes the canonical C5 by reordering only
those same five physical vertices. This is derived from critical classification. -/
theorem free_C5_normalization (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (hs : ∀ i,i≠15 → c 15 i=group i) :
    ∃ p : Equiv.Perm (Fin 5),∀ i j,i≠j →
      (relabelFree c p) (label0 i) (label0 j)=canonical0 i j := by
  obtain ⟨r,e,hr,he⟩ := normalized_root c hc
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
  change k16Template (rootTwisted r) (neighbor0 r (p0 (p0.symm (canonicalEquiv0 r i))))
      (neighbor0 r (p0 (p0.symm (canonicalEquiv0 r j))))=_
  simp only [Equiv.apply_symm_apply]
  exact canonicalPerm0_colors r i j hij

/-- Both foreign blocks retain their original labels and colors. -/
theorem whole_rooted_normalization (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (hs : ∀ i,i≠15 → c 15 i=group i)
    (h1 : ∀ i j,i≠j → c (label1 i) (label1 j)=canonical1 i j)
    (h2 : ∀ i j,i≠j → c (label2 i) (label2 j)=canonical2 i j) :
    ∃ p : Equiv.Perm (Fin 5),CanonicalRooted555 (relabelFree c p) := by
  obtain ⟨p,hp⟩ := free_C5_normalization c hc hs
  refine ⟨p,?_,hp,?_,?_⟩
  · intro i hi
    change c (freeLift p 15) (freeLift p i)=group i
    rw [freeLift_ge5 p 15 (by decide)]
    by_cases hlow : i.val < 5
    · have hx : i=label0 ⟨i.val,hlow⟩ := rfl
      rw [hx,freeLift_label0,hs _ (label0_ne_root _),group_label0,group_label0]
    · rw [freeLift_ge5 p i (by omega)]
      exact hs i hi
  · intro i j hij
    change c (freeLift p (label1 i)) (freeLift p (label1 j))=_
    rw [freeLift_ge5 p _ (by dsimp [label1];omega),freeLift_ge5 p _ (by dsimp [label1];omega)]
    exact h1 i j hij
  · intro i j hij
    change c (freeLift p (label2 i)) (freeLift p (label2 j))=_
    rw [freeLift_ge5 p _ (by dsimp [label2];omega),freeLift_ge5 p _ (by dsimp [label2];omega)]
    exact h2 i j hij

#print axioms free_C5_normalization
#print axioms whole_rooted_normalization
end PricingC.Rooted555
