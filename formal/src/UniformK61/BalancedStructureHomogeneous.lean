import UniformK61.BalancedStructureLocal
set_option autoImplicit false
namespace UniformK61.BalancedStructure
open Ramsey61 Finset

/-- A nonempty internally color-closed set contains two disjoint internal
neighborhoods, each of size at least n-11. -/
theorem closed_inside_lower (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (i j : FourColor) (hij : j≠i)
    (hn : 15≤colorDegree c i r) (S : Finset (Fin 61))
    (hsub : S⊆colorNeighborhood c i r) (hne : S.Nonempty)
    (hclosed : ∀v∈S,inside c r i j v⊆S) :
    2*(colorDegree c i r-11)≤S.card := by
  obtain ⟨v,hv⟩ := hne
  have hvd := (inside_degree_bounds c hc r i j hij v (hsub hv)).1
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<(inside c r i j v).card by omega)
  have hus := hclosed v hv hu
  have hud := (inside_degree_bounds c hc r i j hij u (hsub hus)).1
  have dis : Disjoint (inside c r i j v) (inside c r i j u) :=
    (colorNeighborhoods_disjoint_of_edge c hc j v u (mem_inter.mp hu).1).mono
      inter_subset_left inter_subset_left
  have hs := card_le_card (union_subset (hclosed v hv) (hclosed u hus))
  rw [card_union_of_disjoint dis] at hs
  omega

/-- Connectivity in the exact form needed for propagating any vertex flag:
no nontrivial partition of a critical neighborhood can be closed under an
internal color. This is the elementary component-size proof at orders15/16. -/
theorem critical_predicate_constant (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (i j : FourColor) (hij : j≠i) (hn : 15≤colorDegree c i r)
    (P : Fin 61→Prop)
    (hedge : ∀v∈colorNeighborhood c i r,∀w∈colorNeighborhood c i r,
      v≠w → c v w=j → (P v↔P w)) :
    ∀v∈colorNeighborhood c i r,∀w∈colorNeighborhood c i r,P v↔P w := by
  classical
  have upper := fourColor_colorDegree_le_sixteen c hc i r
  have forward : ∀v∈colorNeighborhood c i r,∀w∈colorNeighborhood c i r,P v→P w := by
    intro v hv w hw hpv
    by_contra hnw
    let A := (colorNeighborhood c i r).filter P
    let B := (colorNeighborhood c i r).filter (fun x => ¬P x)
    have ha : 2*(colorDegree c i r-11)≤A.card := by
      apply closed_inside_lower c hc r i j hij hn A (filter_subset _ _) ⟨v,mem_filter.mpr ⟨hv,hpv⟩⟩
      intro x hx y hy
      obtain ⟨hxS,hxP⟩ := mem_filter.mp hx
      obtain ⟨hyN,hyS⟩ := mem_inter.mp hy
      obtain ⟨hne,he⟩ := (mem_colorNeighborhood _ _ _ _).mp hyN
      exact mem_filter.mpr ⟨hyS,(hedge x hxS y hyS hne.symm he).mp hxP⟩
    have hb : 2*(colorDegree c i r-11)≤B.card := by
      apply closed_inside_lower c hc r i j hij hn B (filter_subset _ _) ⟨w,mem_filter.mpr ⟨hw,hnw⟩⟩
      intro x hx y hy
      obtain ⟨hxS,hxP⟩ := mem_filter.mp hx
      obtain ⟨hyN,hyS⟩ := mem_inter.mp hy
      obtain ⟨hne,he⟩ := (mem_colorNeighborhood _ _ _ _).mp hyN
      exact mem_filter.mpr ⟨hyS,fun hyP => hxP ((hedge x hxS y hyS hne.symm he).mpr hyP)⟩
    have total : A.card+B.card=colorDegree c i r := card_filter_add_card_filter_not P
    omega
  intro v hv w hw
  exact ⟨forward v hv w hw,forward w hw v hv⟩

/-- All high-color flags agree within every actual critical neighborhood. -/
theorem critical_homogeneous (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) (r : Fin 61) (i : FourColor)
    (hn : 15≤colorDegree c i r) :
    ∀v∈colorNeighborhood c i r,∀w∈colorNeighborhood c i r,∀j : FourColor,
      (15≤colorDegree c j v ↔ 15≤colorDegree c j w) := by
  intro v hv w hw j
  by_cases hji : j=i
  · subst j
    have both (u : Fin 61) (hu : u∈colorNeighborhood c i r) : 15≤colorDegree c i u := by
      obtain ⟨hne,he⟩ := (mem_colorNeighborhood _ _ _ _).mp hu
      have h := synchronized_endpoint_highness c sync r u hne
      rw [he] at h
      exact h.mp hn
    exact ⟨fun _ => both w hw,fun _ => both v hv⟩
  · apply critical_predicate_constant c hc r i j hji hn (fun x => 15≤colorDegree c j x) _ v hv w hw
    intro x _ y _ hne he
    have h := synchronized_endpoint_highness c sync x y hne.symm
    simpa only [he] using h

#print axioms critical_homogeneous
end UniformK61.BalancedStructure
