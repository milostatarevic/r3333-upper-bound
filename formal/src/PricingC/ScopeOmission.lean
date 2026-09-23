import PricingC.PhysicalPair

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CAnchorGeometry PairTables

/-- A high physical scope has no absent reference point or exactly one;
no extra omission cases are silently discarded. -/
theorem reference_scope_omission {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}} {state : Fin 72}
    (s : ReferenceScope c owner omitted pal state)
    (hhigh : 15 ≤ colorDegree c omitted owner) :
    s.present = univ ∨ ∃ o : Fin 16, s.present = univ.erase o := by
  classical
  have hcard : 15 ≤ s.present.card := by rw [s.card_eq_degree]; exact hhigh
  have hcomp : s.presentᶜ.card ≤ 1 := by
    have ht := Finset.card_add_card_compl s.present
    simp only [Fintype.card_fin] at ht
    omega
  rcases Nat.eq_zero_or_pos s.presentᶜ.card with hz | hp
  · left
    have he : s.presentᶜ = ∅ := Finset.card_eq_zero.mp hz
    have h := congrArg (fun t : Finset (Fin 16) => tᶜ) he
    simpa only [compl_compl,compl_empty] using h
  · right
    have hh : s.presentᶜ.card = 1 := by omega
    obtain ⟨o,ho⟩ := Finset.card_eq_one.mp hh
    refine ⟨o,?_⟩
    have h := congrArg (fun t : Finset (Fin 16) => tᶜ) ho
    have hh : ({o} : Finset (Fin 16))ᶜ = univ.erase o := by ext v; simp
    simpa only [compl_compl,hh] using h

/-- The formal omission is different from S's physical root and every
point of the shared full five-anchor. -/
theorem pair_omission_excludes_anchor {c : Host} (p : PhysicalXSPair c)
    (o : Fin 16) (ho : p.s.present = univ.erase o) :
    o ≠ 0 ∧ ∀ j, o ≠ generators j := by
  constructor
  · intro e
    have h := p.root_present
    simpa [ho,e] using h
  · intro j e
    have h := p.s_anchor_present j
    simpa [ho,e] using h

 def sRoles (k : Fin 6) (q : Fin 3) : Finset (Fin 16) :=
  univ.filter fun v => v ≠ 0 ∧ PricingG.Completion72.referenceColor (representativeS k) 0 v = q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
 theorem sRoles_card (k : Fin 6) (q : Fin 3) : (sRoles k q).card = 5 := by
  fin_cases k <;> fin_cases q <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
 theorem sRoles_zero : ∀ k : Fin 6, sRoles k 0 = univ.image generators := by decide

/-- Exact physical root-cell intersections are the retained present
reference roles; this simultaneously records all positive and absent roles. -/
theorem pair_support_card (c : Host) (p : PhysicalXSPair c) (q : Fin 3) (r : Color)
    (hpal : (paletteS q).val = palette r) :
    (p.s.present ∩ sRoles p.pair q).card = anchorSize c r := by
  classical
  let f (u : Fin 16) (hu : u ∈ p.s.present ∩ sRoles p.pair q) :=
    p.s.vertex ⟨u,(mem_inter.mp hu).1⟩
  change (p.s.present ∩ sRoles p.pair q).card = (anchorSupport c r).card
  apply Finset.card_bij f
  · intro u hu
    have hr := (mem_filter.mp (mem_inter.mp hu).2).2
    apply mem_inter.mpr
    refine ⟨p.s.mem_scope _,(mem_colorNeighborhood c _ _ _).mpr ⟨?_,?_⟩⟩
    · intro he
      have hv := p.s.vertex.injective (he.trans p.root_image.symm)
      exact hr.1 (congrArg Subtype.val hv)
    · have hm := p.s.map_color ⟨0,p.root_present⟩ ⟨u,(mem_inter.mp hu).1⟩
        (fun h => hr.1 (congrArg Subtype.val h).symm)
      rw [p.root_image,hr.2,hpal] at hm
      exact hm
  · intro u hu v hv h
    exact congrArg Subtype.val (p.s.vertex.injective h)
  · intro v hv
    obtain ⟨u,hu⟩ := p.s.covers v (mem_inter.mp hv).1
    have hc := (mem_colorNeighborhood c _ _ _).mp (mem_inter.mp hv).2
    have une : u.val ≠ 0 := by
      intro he
      have heu : u = ⟨0,p.root_present⟩ := Subtype.ext he
      exact hc.1 (hu.symm.trans ((congrArg p.s.vertex heu).trans p.root_image))
    have hm := p.s.map_color ⟨0,p.root_present⟩ u
      (fun h => une (congrArg Subtype.val h).symm)
    rw [p.root_image,hu] at hm
    have hcol : PricingG.Completion72.referenceColor (representativeS p.pair) 0 u.val = q := by
      apply paletteS.injective
      apply Subtype.ext
      exact hm.symm.trans (hc.2.trans hpal.symm)
    refine ⟨u.val,mem_inter.mpr ⟨u.property,mem_filter.mpr ⟨mem_univ _,une,hcol⟩⟩,?_⟩
    exact hu

set_option maxRecDepth 100000 in
 theorem outside_anchor_roles : ∀ (k : Fin 6) (o : Fin 16),
    o ≠ 0 → (∀ j, o ≠ generators j) → o ∈ sRoles k 1 ∨ o ∈ sRoles k 2 := by decide

/-- The exact exhaustive S-domain alternatives are the three seed strata:
all sixteen points, one missing D role, or one missing B role. -/
theorem pair_three_domains (c : Host) (p : PhysicalXSPair c)
    (hhigh : 15 ≤ colorDegree c (palette 2) 33) :
    p.s.present = univ ∨
    (∃ o ∈ sRoles p.pair 2, p.s.present = univ.erase o) ∨
    (∃ o ∈ sRoles p.pair 1, p.s.present = univ.erase o) := by
  rcases reference_scope_omission p.s hhigh with hall | ⟨o,ho⟩
  · exact Or.inl hall
  · have hx := pair_omission_excludes_anchor p o ho
    rcases outside_anchor_roles p.pair o hx.1 hx.2 with hb | hd
    · exact Or.inr (Or.inr ⟨o,hb,ho⟩)
    · exact Or.inr (Or.inl ⟨o,hd,ho⟩)

#print axioms pair_three_domains
#print axioms pair_support_card
#print axioms reference_scope_omission
end PricingC
