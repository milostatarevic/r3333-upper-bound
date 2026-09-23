import PricingC.ScopeMasks

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore

noncomputable def CompletedScope.scopeEquiv {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) :
    m.present ≃ ↥(colorNeighborhood c omitted owner) :=
  Equiv.ofBijective (fun i => ⟨m.vertex i,m.mem_scope i⟩) ⟨by
    intro i j h
    exact m.vertex.injective (congrArg Subtype.val h),by
    intro v
    obtain ⟨i,hi⟩ := m.covers v.val v.property
    exact ⟨i,Subtype.ext hi⟩⟩

@[simp] theorem CompletedScope.scopeEquiv_val {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (i : m.present) :
    (m.scopeEquiv i).val = m.vertex i := rfl

@[simp] theorem CompletedScope.scopeEquiv_symm_val {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (v : colorNeighborhood c omitted owner) :
    m.vertex (m.scopeEquiv.symm v) = v.val :=
  congrArg Subtype.val (m.scopeEquiv.apply_symm_apply v)

noncomputable def liftPhysicalAnchor {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ Vertex)
    (ha : ∀ i, a i ∈ colorNeighborhood c omitted owner) : Fin 5 ↪ m.present where
  toFun i := m.scopeEquiv.symm ⟨a i,ha i⟩
  inj' := by
    intro i j h
    have hi := m.scopeEquiv.symm.injective h
    exact a.injective (congrArg Subtype.val hi)

@[simp] theorem liftPhysicalAnchor_val {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ Vertex)
    (ha : ∀ i, a i ∈ colorNeighborhood c omitted owner) (i : Fin 5) :
    m.vertex (liftPhysicalAnchor m a ha i) = a i := by
  exact m.scopeEquiv_symm_val ⟨a i,ha i⟩

noncomputable def finiteFiveOrder (A : Finset Vertex) (hA : A.card = 5) : Fin 5 ≃ A :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hA)).symm

/-- Exact cardinality transport for a physical five-set; no fixed choice of
its labels is being inserted as a mathematical premise. -/
theorem five_filter_card (A : Finset Vertex) (hA : A.card = 5)
    (p : Vertex → Prop) [DecidablePred p] :
    (univ.filter (fun i => p (finiteFiveOrder A hA i).val)).card = (A.filter p).card := by
  classical
  apply Finset.card_bij (fun i _ => (finiteFiveOrder A hA i).val)
  · intro i hi
    exact mem_filter.mpr ⟨(finiteFiveOrder A hA i).property,(mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact (finiteFiveOrder A hA).injective (Subtype.ext h)
  · intro v hv
    let v' : A := ⟨v,(mem_filter.mp hv).1⟩
    refine ⟨(finiteFiveOrder A hA).symm v',?_,?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [Equiv.apply_symm_apply]
      exact (mem_filter.mp hv).2
    · exact congrArg Subtype.val ((finiteFiveOrder A hA).apply_symm_apply v')

#print axioms five_filter_card
end PricingC
