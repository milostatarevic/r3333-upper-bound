import PricingABD.Rooted455Data

namespace PricingABD.Rooted455Entrance
open R4333 PricingABD.TemplateNormalization PricingABD.Rooted455Data

/-- An injective enumeration into an already exhausted finite neighborhood is
exactly a permutation of its reference enumeration. No orbit premise is used. -/
theorem factors_through_enumeration {k n : Nat} (a f : Fin k → Fin n)
    (ha : Function.Injective a) (hf : Function.Injective f)
    (hm : ∀ i,∃ j,a j=f i) :
    ∃ p : Equiv.Perm (Fin k),∀ i,f i=a (p i) := by
  classical
  choose p hp using hm
  have hi : Function.Injective p := by
    intro i j h
    apply hf
    rw [←hp i,←hp j,h]
  let e := Equiv.ofBijective p ⟨hi,Finite.surjective_of_injective hi⟩
  exact ⟨e,fun i => (hp i).symm⟩

def group (i : Fin 15) : ThreeColor := if i.val < 4 then 0 else if i.val < 9 then 1 else 2

def label0 (i : Fin 4) : Fin 15 := ⟨i.val,by omega⟩
def label1 (i : Fin 5) : Fin 15 := ⟨4+i.val,by omega⟩
def label2 (i : Fin 5) : Fin 15 := ⟨9+i.val,by omega⟩

theorem label0_injective : Function.Injective label0 := by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 15 => x.val) h
theorem label1_injective : Function.Injective label1 := by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp [label1] at this;omega
theorem label2_injective : Function.Injective label2 := by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp [label2] at this;omega

theorem label0_ne_root (i : Fin 4) : label0 i ≠ 14 := by intro h;have:=congrArg Fin.val h;dsimp [label0] at this;omega
theorem label1_ne_root (i : Fin 5) : label1 i ≠ 14 := by intro h;have:=congrArg Fin.val h;dsimp [label1] at this;omega
theorem label2_ne_root (i : Fin 5) : label2 i ≠ 14 := by intro h;have:=congrArg Fin.val h;dsimp [label2] at this;omega

theorem group_label0 (i : Fin 4) : group (label0 i)=0 := by simp [group,label0]
theorem group_label1 (i : Fin 5) : group (label1 i)=1 := by simp [group,label1];omega
theorem group_label2 (i : Fin 5) : group (label2 i)=2 := by simp [group,label2];omega

structure CanonicalRooted455 (c : EdgeColoring (Fin 15) ThreeColor) : Prop where
  root_edges : ∀ i,i≠14 → c 14 i=group i
  zero_edges : ∀ i j,i≠j → c (label0 i) (label0 j)=canonical0 i j
  one_edges : ∀ i j,i≠j → c (label1 i) (label1 j)=canonical1 i j
  two_edges : ∀ i j,i≠j → c (label2 i) (label2 j)=canonical2 i j

theorem degree_zero (c : EdgeColoring (Fin 15) ThreeColor) (h : CanonicalRooted455 c) :
    colorDegree c 0 14=4 := by
  have hn : colorNeighborhood c 0 14 = {0,1,2,3} := by
    ext i
    fin_cases i <;> simp [mem_colorNeighborhood,h.root_edges,group]
  unfold colorDegree
  rw [hn]
  decide

/-- The root degree selects the exact ten root cases after the palette is
absorbed by an automorphism of the entire critical template. -/
theorem normalized_root (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (h : CanonicalRooted455 c) :
    ∃ r : Fin 10, ∃ e : Fin 15 ≃ Fin 15,e (rootVertex r)=14 ∧
      ∀ u v,u≠v → c (e u) (e v)=k15Template (rootTwisted r) u v := by
  obtain ⟨t,e,he⟩ := k15_color_preserving_complete c hc
  have hd : colorDegree (k15Template t) 0 (e.symm 14)=4 := by
    rw [←degree_of_color_preserving c (k15Template t) e he,Equiv.apply_symm_apply]
    exact degree_zero c h
  obtain ⟨r,ht,hr⟩ := roots_complete t (e.symm 14) hd
  refine ⟨r,e,?_,?_⟩
  · rw [hr];exact e.apply_symm_apply _
  · rw [ht];exact he

/-- Extract a rooted group permutation with its actual colors retained. -/
theorem group_map {c : EdgeColoring (Fin 15) ThreeColor}
    {r : Fin 10} {e : Fin 15 ≃ Fin 15} (hr : e (rootVertex r)=14)
    (he : ∀ u v,u≠v → c (e u) (e v)=k15Template (rootTwisted r) u v)
    {k : Nat} (label : Fin k → Fin 15) (hl : Function.Injective label)
    (hroot : ∀ i,label i≠14) (q : ThreeColor)
    (hcolor : ∀ i,c 14 (label i)=q)
    (neighbor : Fin k → Fin 15) (hn : Function.Injective neighbor)
    (hcomplete : ∀ x,x≠rootVertex r → k15Template (rootTwisted r) (rootVertex r) x=q → ∃ j,neighbor j=x) :
    ∃ p : Equiv.Perm (Fin k),∀ i,e.symm (label i)=neighbor (p i) := by
  apply factors_through_enumeration neighbor (fun i => e.symm (label i)) hn (e.symm.injective.comp hl)
  intro i
  have hne : e.symm (label i)≠rootVertex r := by
    intro hh
    apply hroot i
    rw [←e.apply_symm_apply (label i),hh,hr]
  apply hcomplete _ hne
  rw [←he _ _ hne.symm,hr,Equiv.apply_symm_apply]
  exact hcolor i

/-- The three support isomorphisms belong to the exact 2×10×10 finite list.
This statement quantifies over arbitrary good rooted colorings, not table rows. -/
theorem rooted_isomorphism_cover (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) (h : CanonicalRooted455 c) :
    ∃ r : Fin 10, ∃ e : Fin 15 ≃ Fin 15, ∃ a : Fin 2, ∃ b d : Fin 10,
      e (rootVertex r)=14 ∧
      (∀ u v,u≠v → c (e u) (e v)=k15Template (rootTwisted r) u v) ∧
      (∀ i,e.symm (label0 i)=iso0 r a i) ∧
      (∀ i,e.symm (label1 i)=iso1 r b i) ∧
      (∀ i,e.symm (label2 i)=iso2 r d i) := by
  obtain ⟨r,e,hr,he⟩ := normalized_root c hc h
  obtain ⟨p0,hp0⟩ := group_map hr he label0 label0_injective label0_ne_root 0
    (fun i => (h.root_edges _ (label0_ne_root i)).trans (group_label0 i))
    (neighbor0 r) (neighbor0_injective r) (neighbor0_complete r)
  obtain ⟨p1,hp1⟩ := group_map hr he label1 label1_injective label1_ne_root 1
    (fun i => (h.root_edges _ (label1_ne_root i)).trans (group_label1 i))
    (neighbor1 r) (neighbor1_injective r) (neighbor1_complete r)
  obtain ⟨p2,hp2⟩ := group_map hr he label2 label2_injective label2_ne_root 2
    (fun i => (h.root_edges _ (label2_ne_root i)).trans (group_label2 i))
    (neighbor2 r) (neighbor2_injective r) (neighbor2_complete r)
  have compat {k : Nat} (l : Fin k → Fin 15) (hl : Function.Injective l)
      (neighbors : Fin k → Fin 15) (p : Equiv.Perm (Fin k))
      (hp : ∀ i,e.symm (l i)=neighbors (p i)) (i j : Fin k) (hij : i≠j) :
      k15Template (rootTwisted r) (neighbors (p i)) (neighbors (p j))=c (l i) (l j) := by
    rw [←hp i,←hp j,←he _ _ (e.symm.injective.ne (hl.ne hij))]
    simp
  obtain ⟨k0,hk0⟩ := perm4_complete p0
  obtain ⟨k1,hk1⟩ := perm5_complete p1
  obtain ⟨k2,hk2⟩ := perm5_complete p2
  obtain ⟨a,ha⟩ := iso0_complete_at r k0 (by
    intro i j hij;rw [hk0];exact (compat label0 label0_injective (neighbor0 r) p0 hp0 i j hij).trans (h.zero_edges i j hij))
  obtain ⟨b,hb⟩ := iso1_complete_at r k1 (by
    intro i j hij;rw [hk1];exact (compat label1 label1_injective (neighbor1 r) p1 hp1 i j hij).trans (h.one_edges i j hij))
  obtain ⟨d,hd⟩ := iso2_complete_at r k2 (by
    intro i j hij;rw [hk2];exact (compat label2 label2_injective (neighbor2 r) p2 hp2 i j hij).trans (h.two_edges i j hij))
  refine ⟨r,e,a,b,d,hr,he,?_,?_,?_⟩
  · intro i;rw [hp0,←hk0];exact ha i
  · intro i;rw [hp1,←hk1];exact hb i
  · intro i;rw [hp2,←hk2];exact hd i

#print axioms rooted_isomorphism_cover
#check rooted_isomorphism_cover
end PricingABD.Rooted455Entrance
