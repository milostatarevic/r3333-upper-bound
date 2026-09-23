import PricingC.Rooted555Data

namespace PricingC.Rooted555
open R4333 PricingABD.TemplateNormalization

def group (i : Fin 16) : ThreeColor := if i.val < 5 then 0 else if i.val < 10 then 1 else 2

def label0 (i : Fin 5) : Fin 16 := ⟨i.val,by omega⟩
def label1 (i : Fin 5) : Fin 16 := ⟨5+i.val,by omega⟩
def label2 (i : Fin 5) : Fin 16 := ⟨10+i.val,by omega⟩

theorem label0_injective : Function.Injective label0 := by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 16 => x.val) h
theorem label1_injective : Function.Injective label1 := by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp [label1] at this;omega
theorem label2_injective : Function.Injective label2 := by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp [label2] at this;omega

theorem label0_ne_root (i : Fin 5) : label0 i ≠ 15 := by intro h;have:=congrArg Fin.val h;dsimp [label0] at this;omega
theorem label1_ne_root (i : Fin 5) : label1 i ≠ 15 := by intro h;have:=congrArg Fin.val h;dsimp [label1] at this;omega
theorem label2_ne_root (i : Fin 5) : label2 i ≠ 15 := by intro h;have:=congrArg Fin.val h;dsimp [label2] at this;omega

theorem group_label0 (i : Fin 5) : group (label0 i)=0 := by simp [group,label0]
theorem group_label1 (i : Fin 5) : group (label1 i)=1 := by simp [group,label1];omega
theorem group_label2 (i : Fin 5) : group (label2 i)=2 := by simp [group,label2];omega

structure CanonicalRooted555 (c : EdgeColoring (Fin 16) ThreeColor) : Prop where
  root_edges : ∀ i,i≠15 → c 15 i=group i
  zero_edges : ∀ i j,i≠j → c (label0 i) (label0 j)=canonical0 i j
  one_edges : ∀ i j,i≠j → c (label1 i) (label1 j)=canonical1 i j
  two_edges : ∀ i j,i≠j → c (label2 i) (label2 j)=canonical2 i j

theorem normalized_root (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ r : Fin 2, ∃ e : Fin 16 ≃ Fin 16,e (rootVertex r)=15 ∧
      ∀ u v,u≠v → c (e u) (e v)=k16Template (rootTwisted r) u v := by
  obtain ⟨t,e,hr,he⟩ := k16_rooted_color_preserving_complete c hc 15
  cases t with
  | false => exact ⟨0,e,hr,he⟩
  | true => exact ⟨1,e,hr,he⟩

theorem group_map {c : EdgeColoring (Fin 16) ThreeColor}
    {r : Fin 2} {e : Fin 16 ≃ Fin 16} (hr : e (rootVertex r)=15)
    (he : ∀ u v,u≠v → c (e u) (e v)=k16Template (rootTwisted r) u v)
    (label : Fin 5 → Fin 16) (hl : Function.Injective label)
    (hroot : ∀ i,label i≠15) (q : ThreeColor)
    (hcolor : ∀ i,c 15 (label i)=q)
    (neighbor : Fin 5 → Fin 16) (hn : Function.Injective neighbor)
    (hcomplete : ∀ x,x≠rootVertex r → k16Template (rootTwisted r) (rootVertex r) x=q → ∃ j,neighbor j=x) :
    ∃ p : Equiv.Perm (Fin 5),∀ i,e.symm (label i)=neighbor (p i) := by
  apply PricingABD.Rooted455Entrance.factors_through_enumeration neighbor (fun i => e.symm (label i)) hn (e.symm.injective.comp hl)
  intro i
  have hne : e.symm (label i)≠rootVertex r := by
    intro hh
    apply hroot i
    rw [←e.apply_symm_apply (label i),hh,hr]
  apply hcomplete _ hne
  rw [←he _ _ hne.symm,hr,Equiv.apply_symm_apply]
  exact hcolor i

/-- The actual root and all physical colors are retained. There are exactly
2×10×10×10 canonical rooted support choices, before duplicate word removal. -/
theorem rooted_isomorphism_cover (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (h : CanonicalRooted555 c) :
    ∃ r : Fin 2, ∃ e : Fin 16 ≃ Fin 16, ∃ a b d : Fin 10,
      e (rootVertex r)=15 ∧
      (∀ u v,u≠v → c (e u) (e v)=k16Template (rootTwisted r) u v) ∧
      (∀ i,e.symm (label0 i)=iso0 r a i) ∧
      (∀ i,e.symm (label1 i)=iso1 r b i) ∧
      (∀ i,e.symm (label2 i)=iso2 r d i) := by
  obtain ⟨r,e,hr,he⟩ := normalized_root c hc
  obtain ⟨p0,hp0⟩ := group_map hr he label0 label0_injective label0_ne_root 0
    (fun i => (h.root_edges _ (label0_ne_root i)).trans (group_label0 i))
    (neighbor0 r) (neighbor0_injective r) (neighbor0_complete r)
  obtain ⟨p1,hp1⟩ := group_map hr he label1 label1_injective label1_ne_root 1
    (fun i => (h.root_edges _ (label1_ne_root i)).trans (group_label1 i))
    (neighbor1 r) (neighbor1_injective r) (neighbor1_complete r)
  obtain ⟨p2,hp2⟩ := group_map hr he label2 label2_injective label2_ne_root 2
    (fun i => (h.root_edges _ (label2_ne_root i)).trans (group_label2 i))
    (neighbor2 r) (neighbor2_injective r) (neighbor2_complete r)
  have compat (l : Fin 5 → Fin 16) (hl : Function.Injective l)
      (neighbors : Fin 5 → Fin 16) (p : Equiv.Perm (Fin 5))
      (hp : ∀ i,e.symm (l i)=neighbors (p i)) (i j : Fin 5) (hij : i≠j) :
      k16Template (rootTwisted r) (neighbors (p i)) (neighbors (p j))=c (l i) (l j) := by
    rw [←hp i,←hp j,←he _ _ (e.symm.injective.ne (hl.ne hij))]
    simp
  obtain ⟨k0,hk0⟩ := PricingABD.Rooted455Data.perm5_complete p0
  obtain ⟨k1,hk1⟩ := PricingABD.Rooted455Data.perm5_complete p1
  obtain ⟨k2,hk2⟩ := PricingABD.Rooted455Data.perm5_complete p2
  obtain ⟨a,ha⟩ := iso0_complete r k0 (by
    intro i j hij;rw [hk0];exact (compat label0 label0_injective (neighbor0 r) p0 hp0 i j hij).trans (h.zero_edges i j hij))
  obtain ⟨b,hb⟩ := iso1_complete r k1 (by
    intro i j hij;rw [hk1];exact (compat label1 label1_injective (neighbor1 r) p1 hp1 i j hij).trans (h.one_edges i j hij))
  obtain ⟨d,hd⟩ := iso2_complete r k2 (by
    intro i j hij;rw [hk2];exact (compat label2 label2_injective (neighbor2 r) p2 hp2 i j hij).trans (h.two_edges i j hij))
  refine ⟨r,e,a,b,d,hr,he,?_,?_,?_⟩
  · intro i;rw [hp0,←hk0];exact ha i
  · intro i;rw [hp1,←hk1];exact hb i
  · intro i;rw [hp2,←hk2];exact hd i

#print axioms rooted_isomorphism_cover
end PricingC.Rooted555
