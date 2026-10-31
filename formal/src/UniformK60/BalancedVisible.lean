import UniformK60.BalancedEncodingLocal
import UniformK60.ClassificationFixedPalette
import UniformK61.BalancedAnchorCoverage

/-! Actual opposite critical neighborhoods supply all six-table witnesses.
The neighborhood can have order15 or16. Only its observed physical members
receive roles; unused reference coordinates are never new host vertices. -/
set_option autoImplicit false
set_option maxRecDepth 20000
namespace UniformK60.BalancedEncoding
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK61.BalancedEncodingData

/-- Geometric facts about a pentagon in one actual critical neighborhood. -/
structure ActualGeometry {n : Nat} (c : Host) (g : Geometry n) : Prop where
  critical : 15 ≤ colorDegree c (palette g.scopeColor) g.center
  member_injective : Function.Injective g.member
  anchor_injective : Function.Injective g.anchor
  anchor_mem : ∀ a, g.anchor a ∈ colorNeighborhood c (palette g.scopeColor) g.center
  anchor_colors : ∀ a b, a ≠ b →
    c (g.anchor a) (g.anchor b) = palette (foreign g.scopeColor (UniformK61.BalancedAnchor.reference a b))
  member_colors : ∀ a b, a ≠ b →
    c (g.member a) (g.member b) = palette (foreign g.scopeColor (g.memberColor a b))

def actualNeighborhood {n : Nat} (c : Host) (g : Geometry n) : Finset Vertex :=
  colorNeighborhood c (palette g.scopeColor) g.center

noncomputable def anchorSub {n : Nat} {c : Host} {g : Geometry n}
    (hg : ActualGeometry c g) (a : Fin 5) : actualNeighborhood c g :=
  ⟨g.anchor a,hg.anchor_mem a⟩

structure ChartedEmbedding {n : Nat} (c : Host) (g : Geometry n)
    (hg : ActualGeometry c g) where
  state : Fin 6
  position : actualNeighborhood c g ↪ Fin 16
  anchors : ∀ a, position (anchorSub hg a) = anchorPosition a
  colors : ∀ u v : actualNeighborhood c g, u ≠ v →
    c u.val v.val = palette (foreign g.scopeColor (stateColor state (position u) (position v)))

theorem foreign_injective (q : Color) : Function.Injective (foreign q) := by
  intro a b h
  have he : foreignEquiv q a = foreignEquiv q b := Subtype.ext (congrArg palette h)
  exact (foreignEquiv q).injective he

/-- Classification followed by one complete template chart, with a fixed
physical palette throughout. This constructs, rather than assumes, coverage. -/
theorem actual_chart {n : Nat} {c : Host} {g : Geometry n}
    (hc : NoMonochromaticTriangle c) (hg : ActualGeometry c g) :
    Nonempty (ChartedEmbedding c g hg) := by
  classical
  obtain ⟨t,e,he⟩ := ClassificationFixedPalette.physical_high_embedding c hc
    g.center (palette g.scopeColor) hg.critical (foreignEquiv g.scopeColor)
  have hanchor : ∀ a b : Fin 5, a ≠ b →
      R4333.k16Template t (e (anchorSub hg a)) (e (anchorSub hg b)) = UniformK61.BalancedAnchor.reference a b := by
    intro a b hab
    have hne : anchorSub hg a ≠ anchorSub hg b := by
      intro h
      exact hab (hg.anchor_injective (congrArg Subtype.val h))
    exact foreign_injective _ (palette_injective ((he _ _ hne).symm.trans (hg.anchor_colors a b hab)))
  obtain ⟨k,hkind,hk⟩ := UniformK61.BalancedAnchor.anchor_covered t (fun a => e (anchorSub hg a)) hanchor
  let pos : actualNeighborhood c g ↪ Fin 16 := e.trans (UniformK61.BalancedAnchor.chartPerm k).symm.toEmbedding
  refine ⟨⟨UniformK61.BalancedAnchor.chartState k,pos,?_,?_⟩⟩
  · intro a
    change (UniformK61.BalancedAnchor.chartPerm k).symm (e (anchorSub hg a)) = _
    rw [←hk a,Equiv.symm_apply_apply]
  · intro u v huv
    have hh := UniformK61.BalancedAnchor.chart_color k (pos u) (pos v)
    change R4333.k16Template (UniformK61.BalancedAnchor.chartKind k)
      ((UniformK61.BalancedAnchor.chartPerm k) ((UniformK61.BalancedAnchor.chartPerm k).symm (e u)))
      ((UniformK61.BalancedAnchor.chartPerm k) ((UniformK61.BalancedAnchor.chartPerm k).symm (e v))) = _ at hh
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply,hkind] at hh
    exact (he u v huv).trans (congrArg (fun q => palette (foreign g.scopeColor q)) hh)

noncomputable def memberSub {n : Nat} {c : Host} (g : Geometry n) (m : Fin n)
    (h : c g.center (g.member m) = palette g.scopeColor) : actualNeighborhood c g :=
  ⟨g.member m,(mem_colorNeighborhood _ _ _ _).mpr ⟨(g.center_ne m).symm,h⟩⟩

theorem chart_member_nonanchor {n : Nat} {c : Host} {g : Geometry n} {hg : ActualGeometry c g}
    (ch : ChartedEmbedding c g hg) (m : Fin n)
    (h : c g.center (g.member m) = palette g.scopeColor) :
    5 ≤ (ch.position (memberSub g m h)).val := by
  by_contra hb
  have hb' : (ch.position (memberSub g m h)).val < 5 := by omega
  let a : Fin 5 := ⟨(ch.position (memberSub g m h)).val,hb'⟩
  have he : ch.position (memberSub g m h) = ch.position (anchorSub hg a) := by
    rw [ch.anchors]
    exact Fin.ext rfl
  have hv := congrArg Subtype.val (ch.position.injective he)
  exact g.anchor_ne a m hv.symm

theorem chart_local_witness {n : Nat} {c : Host} {g : Geometry n} {hg : ActualGeometry c g}
    (ch : ChartedEmbedding c g hg) : Nonempty (LocalWitness c g) := by
  classical
  let active : Fin n → Prop := fun m => c g.center (g.member m) = palette g.scopeColor
  let role : Fin n → Option (Fin 11) := fun m =>
    if h : active m then some ⟨(ch.position (memberSub g m h)).val-5,by
      have hp := (ch.position (memberSub g m h)).isLt
      omega⟩ else none
  have role_correct (m : Fin n) (t : Fin 11) (hr : role m = some t) :
      ∃ h : active m, ch.position (memberSub g m h) = memberPosition t := by
    by_cases hm : active m
    · refine ⟨hm,?_⟩
      simp only [role,dif_pos hm] at hr
      have he := Option.some.inj hr
      have hlo := chart_member_nonanchor ch m hm
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
    exact hg.member_injective (congrArg Subtype.val (ch.position.injective (hea.trans heb.symm)))
  · intro m t hr a
    obtain ⟨hm,he⟩ := role_correct m t hr
    have hne : anchorSub hg a ≠ memberSub g m hm := by
      intro h
      exact g.anchor_ne a m (congrArg Subtype.val h)
    have hh := ch.colors (anchorSub hg a) (memberSub g m hm) hne
    rw [ch.anchors,he] at hh
    exact hh
  · intro a b t u hab ha hb
    obtain ⟨haa,hea⟩ := role_correct a t ha
    obtain ⟨hbb,heb⟩ := role_correct b u hb
    have hne : memberSub g a haa ≠ memberSub g b hbb := by
      intro h
      exact hab (hg.member_injective (congrArg Subtype.val h))
    have hh := ch.colors (memberSub g a haa) (memberSub g b hbb) hne
    rw [hea,heb] at hh
    exact foreign_injective _ (palette_injective (hh.symm.trans (hg.member_colors a b hab)))

theorem actual_local_witness {n : Nat} {c : Host} {g : Geometry n}
    (hc : NoMonochromaticTriangle c) (hg : ActualGeometry c g) : Nonempty (LocalWitness c g) := by
  obtain ⟨ch⟩ := actual_chart hc hg
  exact chart_local_witness ch

#print axioms actual_chart
#print axioms actual_local_witness
end UniformK60.BalancedEncoding
