import PricingC.PairTables

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore AnchorTables PairTables

 theorem referenceAnchor_reorder {c : Host} {owner : Vertex} {omitted : FourColor}
    {palette : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted palette) (a : Fin 5 ↪ m.present) (pi : Fin 5 ≃ Fin 5) :
    referenceAnchor m (pi.toEmbedding.trans a) = referenceAnchor m a := by
  ext z
  simp only [referenceAnchor,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨pi i,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨pi.symm i,by simp⟩

 theorem anchorAction_injective (a : Fin 10) : Function.Injective (anchorActionFn a) := by
  intro j k h
  apply generators_injective
  apply (action a).injective
  rw [action_anchor,action_anchor,h]

/-- Two completed actual scopes sharing the same colored five-anchor reduce
under one simultaneous dihedral action. Both vertex maps retain every shared
anchor point; S's actual root center is retained at reference zero. -/
theorem paired_scopes_six_orbits
    {c : Host} {ox os : Vertex} {qx qs : FourColor}
    {px : Fin 3 ≃ {q : FourColor // q ≠ qx}}
    {ps : Fin 3 ≃ {q : FourColor // q ≠ qs}}
    (mx : CompletedScope c ox qx px) (ms : CompletedScope c os qs ps)
    (ax : Fin 5 ↪ mx.present) (as : Fin 5 ↪ ms.present)
    (hagree : ∀ j, mx.vertex (ax j) = ms.vertex (as j))
    (hindx : R4333.IsColorIndependentSet mx.model 0 (referenceAnchor mx ax))
    (rs : Fin 16) (hrs : referenceAnchor ms as = R4333.colorNeighborhood ms.model 0 rs)
    (hpal : ∀ j k : Fin 5, j ≠ k → (px (cycleColor j k)).val = (ps (cycleColor j k)).val) :
    ∃ (k : Fin 6) (ex es : Fin 16 ≃ Fin 16) (order : Fin 5 ↪ Fin 5),
      es 0 = rs ∧
      (∀ j, ex (generators j) = (ax (order j)).val ∧ es (generators j) = (as (order j)).val) ∧
      (∀ u v, u ≠ v → mx.model (ex u) (ex v) = PricingG.Completion72.referenceColor (representativeX k) u v) ∧
      (∀ u v, u ≠ v → ms.model (es u) (es v) = PricingG.Completion72.referenceColor (representativeS k) u v) := by
  classical
  obtain ⟨pi,hcycx⟩ := completed_anchor_cycle mx ax hindx
  let bx := pi.toEmbedding.trans ax
  let bs := pi.toEmbedding.trans as
  have hix : R4333.IsColorIndependentSet mx.model 0 (referenceAnchor mx bx) := by
    simpa only [bx,referenceAnchor_reorder] using hindx
  have hcs : ∀ j k, j ≠ k → c (ms.vertex (bs j)) (ms.vertex (bs k)) = (ps (cycleColor j k)).val := by
    intro j k hjk
    change c (ms.vertex (as (pi j))) (ms.vertex (as (pi k))) = _
    rw [←hagree _,←hagree _,hcycx j k hjk,hpal j k hjk]
  have hrs' : referenceAnchor ms bs = R4333.colorNeighborhood ms.model 0 rs := by
    simpa only [bs,referenceAnchor_reorder] using hrs
  obtain ⟨ix,ex,hex,hxc⟩ := completed_anchor_to_six mx bx hix hcycx
  obtain ⟨is,es,hes0,hes,hsc⟩ := centered_anchor_to_six ms bs rs hrs' hcs
  let act := action (pairAction ix is)
  let order : Fin 5 ↪ Fin 5 := ⟨fun j => pi (anchorActionFn (pairAction ix is) j),
    pi.injective.comp (anchorAction_injective _)⟩
  refine ⟨pairRepresentative ix is,act.trans ex,act.trans es,order,?_,?_,?_,?_⟩
  · change es (act 0) = rs
    rw [action_root,hes0]
  · intro j
    constructor
    · change ex (act (generators j)) = _
      rw [action_anchor,hex]
      rfl
    · change es (act (generators j)) = _
      rw [action_anchor,hes]
      rfl
  · intro u v huv
    change mx.model (ex (act u)) (ex (act v)) = _
    rw [hxc _ _ (act.injective.ne huv)]
    exact (pair_cover ix is u v huv).1
  · intro u v huv
    change ms.model (es (act u)) (es (act v)) = _
    rw [hsc _ _ (act.injective.ne huv)]
    exact (pair_cover ix is u v huv).2

#print axioms paired_scopes_six_orbits
end PricingC
