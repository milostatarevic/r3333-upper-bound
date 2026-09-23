import PricingC.PhysicalFrames

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore

/-- One exact retained reference matrix, realized injectively on every
present point of the actual physical neighborhood. -/
structure ReferenceScope (c : Host) (owner : Vertex) (omitted : FourColor)
    (palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}) (state : Fin 72) where
  present : Finset (Fin 16)
  vertex : present ↪ Vertex
  mem_scope : ∀ i, vertex i ∈ colorNeighborhood c omitted owner
  covers : ∀ v ∈ colorNeighborhood c omitted owner, ∃ i, vertex i = v
  map_color : ∀ i j : present, i ≠ j → c (vertex i) (vertex j) =
    (palette (PricingG.Completion72.referenceColor state i.val j.val)).val

noncomputable def referenceScope {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (state : Fin 72) (e : Fin 16 ≃ Fin 16)
    (hcolor : ∀ u v, u ≠ v → m.model (e u) (e v) = PricingG.Completion72.referenceColor state u v) :
    ReferenceScope c owner omitted palette state where
  present := univ.filter (fun v => e v ∈ m.present)
  vertex := ⟨fun i => m.vertex ⟨e i.val,(mem_filter.mp i.property).2⟩,by
    intro i j h
    have he := m.vertex.injective h
    exact Subtype.ext (e.injective (congrArg Subtype.val he))⟩
  mem_scope := fun i => m.mem_scope ⟨e i.val,(mem_filter.mp i.property).2⟩
  covers := by
    intro v hv
    obtain ⟨i,hi⟩ := m.covers v hv
    let j : ↥(univ.filter (fun v => e v ∈ m.present)) :=
      ⟨e.symm i.val,by simp only [mem_filter,mem_univ,Equiv.apply_symm_apply,true_and]; exact i.property⟩
    refine ⟨j,?_⟩
    change m.vertex ⟨e (e.symm i.val),_⟩ = v
    simpa only [Equiv.apply_symm_apply] using hi
  map_color := by
    intro i j hij
    have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have he : (⟨e i.val,(mem_filter.mp i.property).2⟩ : m.present) ≠
        ⟨e j.val,(mem_filter.mp j.property).2⟩ := fun h => hv (e.injective (congrArg Subtype.val h))
    change c (m.vertex ⟨e i.val,(mem_filter.mp i.property).2⟩)
      (m.vertex ⟨e j.val,(mem_filter.mp j.property).2⟩) = _
    rw [m.map_color _ _ he,hcolor i.val j.val hv]

 theorem referenceScope_full {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (state : Fin 72) (e : Fin 16 ≃ Fin 16)
    (hcolor) (hfull : m.present = univ) :
    (referenceScope m state e hcolor).present = univ := by
  change univ.filter (fun v => e v ∈ m.present) = univ
  simp only [hfull,mem_univ,filter_true]

 theorem ReferenceScope.card_eq_degree {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}} {state : Fin 72}
    (m : ReferenceScope c owner omitted palette state) :
    m.present.card = colorDegree c omitted owner := by
  classical
  have he : m.present ≃ ↥(colorNeighborhood c omitted owner) :=
    Equiv.ofBijective (fun i => ⟨m.vertex i,m.mem_scope i⟩) ⟨by
      intro i j h
      exact m.vertex.injective (congrArg Subtype.val h),by
      intro v
      obtain ⟨i,hi⟩ := m.covers v.val v.property
      exact ⟨i,Subtype.ext hi⟩⟩
  have hh := Fintype.card_congr he
  simpa only [Fintype.card_coe,colorDegree] using hh

 theorem ReferenceScope.point_not_owner {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}} {state : Fin 72}
    (m : ReferenceScope c owner omitted palette state) (i : m.present) : m.vertex i ≠ owner :=
  ((mem_colorNeighborhood c _ _ _).mp (m.mem_scope i)).1

#print axioms referenceScope
#print axioms ReferenceScope.card_eq_degree
end PricingC
