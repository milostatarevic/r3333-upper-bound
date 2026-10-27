import UniformK61.BalancedEncodingGeometry

set_option autoImplicit false
set_option maxRecDepth 20000
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedVisible UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

noncomputable def anchorSub {c : Host} {o : Owner} (hn : Normalized c o.left o.right)
    (s : Scope) (a : Fin 5) : visible c s := ⟨anchorVertex o s a,anchor_mem_visible hn s a⟩

structure ChartedEmbedding (c : Host) (o : Owner) (s : Scope)
    (hn : Normalized c o.left o.right) where
  state : Fin 6
  position : visible c s ↪ Fin 16
  anchors : ∀ a, position (anchorSub hn s a)=anchorPosition a
  colors : ∀ u v : visible c s, u≠v →
    c u.val v.val=palette (foreign (scopeColor s) (stateColor state (position u) (position v)))

theorem actual_chart {c : Host} {o : Owner} (hn : Normalized c o.left o.right)
    (hvis : Conditions c) (s : Scope) : Nonempty (ChartedEmbedding c o s hn) := by
  classical
  obtain ⟨t,e,he⟩ := visible_embeds hvis s
  have hanchor : ∀ a b : Fin 5, a≠b →
      R4333.k16Template t (e (anchorSub hn s a)) (e (anchorSub hn s b)) = BalancedAnchor.reference a b := by
    intro a b hab
    have hs : anchorSub hn s a ≠ anchorSub hn s b := by
      intro h; exact hab (anchor_injective o s (congrArg Subtype.val h))
    exact foreign_injective _ (palette_injective ((he _ _ hs).symm.trans (anchor_edge hn s a b hab)))
  obtain ⟨k,hkind,hk⟩ := BalancedAnchor.anchor_covered t (fun a => e (anchorSub hn s a)) hanchor
  let pos : visible c s ↪ Fin 16 := e.trans (BalancedAnchor.chartPerm k).symm.toEmbedding
  refine ⟨⟨BalancedAnchor.chartState k,pos,?_,?_⟩⟩
  · intro a
    change (BalancedAnchor.chartPerm k).symm (e (anchorSub hn s a)) = _
    rw [←hk a,Equiv.symm_apply_apply]
  · intro u v huv
    have hh := BalancedAnchor.chart_color k (pos u) (pos v)
    change R4333.k16Template (BalancedAnchor.chartKind k)
      ((BalancedAnchor.chartPerm k) ((BalancedAnchor.chartPerm k).symm (e u)))
      ((BalancedAnchor.chartPerm k) ((BalancedAnchor.chartPerm k).symm (e v))) = _ at hh
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply,hkind] at hh
    exact (he u v huv).trans (congrArg (fun q => palette (foreign (scopeColor s) q)) hh)

noncomputable def otherSub {c : Host} (s : Scope) (m : Fin 16)
    (h : c (ownVertex s (center s)) (otherVertex s m)=palette (scopeColor s)) : visible c s :=
  ⟨otherVertex s m,(other_mem_visible s m).mpr h⟩

theorem chart_other_nonanchor {c : Host} {o : Owner} {s : Scope} {hn : Normalized c o.left o.right}
    (ch : ChartedEmbedding c o s hn) (m : Fin 16)
    (h : c (ownVertex s (center s)) (otherVertex s m)=palette (scopeColor s)) :
    5 ≤ (ch.position (otherSub s m h)).val := by
  by_contra hb
  have hb' : (ch.position (otherSub s m h)).val < 5 := by omega
  let a : Fin 5 := ⟨(ch.position (otherSub s m h)).val,hb'⟩
  have he : ch.position (otherSub s m h)=ch.position (anchorSub hn s a) := by
    rw [ch.anchors]; exact Fin.ext rfl
  have hv := congrArg Subtype.val (ch.position.injective he)
  exact own_other_ne s _ _ hv.symm

theorem chart_local_witness {c : Host} {o : Owner} {s : Scope} {hn : Normalized c o.left o.right}
    (ch : ChartedEmbedding c o s hn) : Nonempty (LocalWitness c o s) := by
  classical
  let active : Fin 16 → Prop := fun m => c (ownVertex s (center s)) (otherVertex s m)=palette (scopeColor s)
  let role : Fin 16 → Option (Fin 11) := fun m =>
    if h : active m then some ⟨(ch.position (otherSub s m h)).val-5,by
      have hp := (ch.position (otherSub s m h)).isLt; omega⟩ else none
  have role_correct (m : Fin 16) (t : Fin 11) (hr : role m=some t) :
      ∃ h : active m, ch.position (otherSub s m h)=memberPosition t := by
    by_cases hm : active m
    · refine ⟨hm,?_⟩
      simp only [role,dif_pos hm] at hr
      have he := Option.some.inj hr
      have hlo := chart_other_nonanchor ch m hm
      have hv := congrArg Fin.val he
      apply Fin.ext
      simp only [memberPosition,Fin.val_mk] at *
      omega
    · simp [role,hm] at hr
  refine ⟨⟨ch.state,role,?_,?_,?_,?_⟩⟩
  · intro m
    by_cases hm : active m <;> simp [role,hm,active] at *
  · intro a b t ha hb
    obtain ⟨haa,hea⟩ := role_correct a t ha
    obtain ⟨hbb,heb⟩ := role_correct b t hb
    exact other_injective s (congrArg Subtype.val (ch.position.injective (hea.trans heb.symm)))
  · intro m t hr a
    obtain ⟨hm,he⟩ := role_correct m t hr
    have hne : anchorSub hn s a ≠ otherSub s m hm := by
      intro h; exact own_other_ne s _ _ (congrArg Subtype.val h)
    have hh := ch.colors (anchorSub hn s a) (otherSub s m hm) hne
    rw [ch.anchors,he] at hh
    exact hh
  · intro a b t u hab ha hb
    obtain ⟨haa,hea⟩ := role_correct a t ha
    obtain ⟨hbb,heb⟩ := role_correct b u hb
    have hne : otherSub s a haa ≠ otherSub s b hbb := by
      intro h; exact hab (other_injective s (congrArg Subtype.val h))
    have hh := ch.colors (otherSub s a haa) (otherSub s b hbb) hne
    rw [hea,heb] at hh
    exact foreign_injective _ (palette_injective (hh.symm.trans (other_template hn s a b hab)))

theorem actual_local_witness {c : Host} {o : Owner} (hn : Normalized c o.left o.right)
    (hvis : Conditions c) (s : Scope) : Nonempty (LocalWitness c o s) := by
  obtain ⟨ch⟩ := actual_chart hn hvis s
  exact chart_local_witness ch

#print axioms actual_local_witness
end UniformK61.BalancedEncoding
