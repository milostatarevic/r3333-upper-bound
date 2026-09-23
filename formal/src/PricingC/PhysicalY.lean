import PricingC.ReferenceScopes
import PricingC.NonstarFour

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
  AnchorTables FourAnchorTables

structure FullReferenceScope (c : Host) (owner : Vertex) (omitted : FourColor)
    (pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}) (state : Fin 72)
    extends ReferenceScope c owner omitted pal state where
  full : present = univ

 def FullReferenceScope.at {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}} {state : Fin 72}
    (s : FullReferenceScope c owner omitted pal state) (i : Fin 16) : Vertex :=
  s.vertex ⟨i,by rw [s.full]; exact mem_univ _⟩

 theorem FullReferenceScope.at_injective {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}} {state : Fin 72}
    (s : FullReferenceScope c owner omitted pal state) : Function.Injective s.at := by
  intro i j h
  exact congrArg Subtype.val (s.vertex.injective h)

noncomputable def liftPhysical {n : Nat} {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted pal) (a : Fin n ↪ Vertex)
    (ha : ∀ i, a i ∈ colorNeighborhood c omitted owner) : Fin n ↪ m.present where
  toFun i := m.scopeEquiv.symm ⟨a i,ha i⟩
  inj' := by
    intro i j h
    exact a.injective (congrArg Subtype.val (m.scopeEquiv.symm.injective h))

 theorem liftPhysical_val {n : Nat} {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted pal) (a : Fin n ↪ Vertex)
    (ha : ∀ i, a i ∈ colorNeighborhood c omitted owner) (j : Fin n) :
    m.vertex (liftPhysical m a ha j) = a j := m.scopeEquiv_symm_val _

noncomputable def fullReferenceFrom {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted pal) (hfull : m.present = univ)
    (state : Fin 72) (e : Fin 16 ≃ Fin 16)
    (hcolor : ∀ u v, u ≠ v → m.model (e u) (e v) = PricingG.Completion72.referenceColor state u v) :
    FullReferenceScope c owner omitted pal state :=
  { referenceScope m state e hcolor with full := referenceScope_full m state e hcolor hfull }

 theorem fullReferenceFrom_at {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}}
    (m : CompletedScope c owner omitted pal) (hfull : m.present = univ)
    (state : Fin 72) (e : Fin 16 ≃ Fin 16)
    (hcolor : ∀ u v, u ≠ v → m.model (e u) (e v) = PricingG.Completion72.referenceColor state u v)
    (v : Fin 16) (z : m.present) (hz : e v = z.val) :
    (fullReferenceFrom m hfull state e hcolor).at v = m.vertex z := by
  apply congrArg m.vertex
  exact Subtype.ext hz

/-- A prescribed physical positive-cycle order on the full B anchor yields
a complete actual Y matrix in the exact six-state branch. -/
theorem physical_Y_five (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (a : Fin 5 ↪ Vertex)
    (hY : ∀ j, a j ∈ colorNeighborhood c (palette 1) 0)
    (hS : ∀ j, a j ∈ colorNeighborhood c (palette 2) 33)
    (hcycle : ∀ j k, j ≠ k → c (a j) (a k) = (paletteY (cycleColor j k)).val) :
    ∃ (i : Fin 6) (y : FullReferenceScope c 0 (palette 1) paletteY (anchoredIndex i)),
      ∀ j, y.at (generators j) = a j := by
  classical
  have hydeg : colorDegree c (palette 1) 0 = 16 := by simpa using normalized_root_degree c hroot 1
  obtain ⟨t,⟨fy⟩⟩ := fixed_palette_k16 c hc 0 (palette 1) hydeg paletteY
  let m := completed_from_k16 c 0 (palette 1) paletteY t fy
  let b := liftPhysical m a hY
  have hb : ∀ j, m.vertex (b j) = a j := liftPhysical_val m a hY
  have hi : R4333.IsColorIndependentSet m.model 0 (referenceAnchor m b) := by
    apply referenceAnchor_independent m b 0
    intro j k hjk
    rw [hb j,hb k,paletteY_zero]
    exact neighborhood_pair_avoids c hc 33 (palette 2) _ _ (hS j) (hS k) (a.injective.ne hjk)
  have hcyc : ∀ j k, j ≠ k → c (m.vertex (b j)) (m.vertex (b k)) = (paletteY (cycleColor j k)).val := by
    intro j k hjk; rw [hb j,hb k]; exact hcycle j k hjk
  obtain ⟨i,e,he,hcolor⟩ := completed_anchor_to_six m b hi hcyc
  refine ⟨i,fullReferenceFrom m rfl _ e hcolor,?_⟩
  intro j
  exact (fullReferenceFrom_at m rfl _ e hcolor _ (b j) (he j)).trans (hb j)

/-- Both exhaustive four-anchor alternatives use the actual full Y scope.
The star branch's fifth reference point is necessarily an actual Y vertex. -/
theorem physical_Y_four (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (a : Fin 4 ↪ Vertex)
    (hY : ∀ j, a j ∈ colorNeighborhood c (palette 1) 0)
    (hS : ∀ j, a j ∈ colorNeighborhood c (palette 2) 33)
    (hpath : ∀ j k, j ≠ k → c (a j) (a k) = (paletteY (pathColor j k)).val) :
    (∃ (i : Fin 6) (y : FullReferenceScope c 0 (palette 1) paletteY (anchoredIndex i)),
      ∀ j, y.at (starRoles j) = a j) ∨
    (∃ (i : Fin 2) (y : FullReferenceScope c 0 (palette 1) paletteY (nonstarIndex i)),
      ∀ j, y.at (planeRoles j) = a j) := by
  classical
  have hydeg : colorDegree c (palette 1) 0 = 16 := by simpa using normalized_root_degree c hroot 1
  obtain ⟨t,⟨fy⟩⟩ := fixed_palette_k16 c hc 0 (palette 1) hydeg paletteY
  let m := completed_from_k16 c 0 (palette 1) paletteY t fy
  let b := liftPhysical m a hY
  let b' : Fin 4 ↪ Fin 16 := b.trans (Function.Embedding.subtype _)
  have hb : ∀ j, m.vertex (b j) = a j := liftPhysical_val m a hY
  have hind : ∀ j k, j ≠ k → m.model (b' j) (b' k) ≠ 0 := by
    intro j k hjk he
    have hm := m.map_color (b j) (b k) (b.injective.ne hjk)
    change c (m.vertex (b j)) (m.vertex (b k)) = (paletteY (m.model (b' j) (b' k))).val at hm
    rw [hb j,hb k,he,paletteY_zero] at hm
    exact neighborhood_pair_avoids c hc 33 (palette 2) _ _ (hS j) (hS k) (a.injective.ne hjk) hm
  have hp : ∀ j k, j ≠ k → m.model (b' j) (b' k) = pathColor j k := by
    intro j k hjk
    have hm := m.map_color (b j) (b k) (b.injective.ne hjk)
    rw [hb j,hb k,hpath j k hjk] at hm
    exact paletteY.injective (Subtype.ext hm.symm)
  by_cases hs : ∃ r, ∀ j, b' j ∈ R4333.colorNeighborhood m.model 0 r
  · obtain ⟨i,e,he,hcolor⟩ := star_four_reference m.model m.good b' hp hs
    refine Or.inl ⟨i,fullReferenceFrom m rfl _ e hcolor,?_⟩
    intro j
    exact (fullReferenceFrom_at m rfl _ e hcolor _ (b j) (he j)).trans (hb j)
  · obtain ⟨i,e,he,hcolor⟩ := nonstar_four_reference m.model m.good b' hind hp hs
    refine Or.inr ⟨i,fullReferenceFrom m rfl _ e hcolor,?_⟩
    intro j
    exact (fullReferenceFrom_at m rfl _ e hcolor _ (b j) (he j)).trans (hb j)

#print axioms physical_Y_five
#print axioms physical_Y_four
end PricingC
