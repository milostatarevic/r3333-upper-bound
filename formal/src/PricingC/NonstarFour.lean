import PricingC.PlaneGeometry
import PricingC.StarFour

namespace PricingC
open R4333 FourAnchorTables PlaneTables

/-- Full ordered nonstar four-anchor coverage. This is an actual matrix
normalization, with one common vertex map and no palette changes. -/
theorem nonstar_four_reference (d : EdgeColoring (Fin 16) (Fin 3))
    (hd : NoMonochromaticTriangle d) (a : Fin 4 ↪ Fin 16)
    (hind : ∀ j k, j ≠ k → d (a j) (a k) ≠ 0)
    (hpath : ∀ j k, j ≠ k → d (a j) (a k) = pathColor j k)
    (hstar : ¬ ∃ r, ∀ j, a j ∈ colorNeighborhood d 0 r) :
    ∃ (i : Fin 2) (e : Fin 16 ≃ Fin 16),
      (∀ j, e (planeRoles j) = a j) ∧
      (∀ u v, u ≠ v → d (e u) (e v) = PricingG.Completion72.referenceColor (nonstarIndex i) u v) := by
  classical
  have hs := k16_colorGraph_isSRG d hd (0 : Fin 3)
  have hcard : Fintype.card ↥(clebschA (colorGraph d 0) 0) = 5 := by
    rw [Fintype.card_coe,card_clebschA _ hs]
  let pts := (Fintype.equivFinOfCardEq hcard).symm
  let e0 := anchoredCoordinates (colorGraph d 0) hs 0 pts
  let b : Fin 4 ↪ Fin 16 := a.trans e0.toEquiv.symm.toEmbedding
  have hb : ∀ j, e0 (b j) = a j := fun j => e0.apply_symm_apply (a j)
  have hbi : ∀ j k, j ≠ k → ¬xorGraph.Adj (b j) (b k) := by
    intro j k hjk h
    have hh := e0.map_rel_iff.mpr h
    change e0 (b j) ≠ e0 (b k) ∧ d (e0 (b j)) (e0 (b k)) = 0 at hh
    rw [hb j,hb k] at hh
    exact hind j k hjk hh.2
  have hquad : QuadIndependent (b 0) (b 1) (b 2) (b 3) := by
    exact ⟨b.injective.ne (by decide),b.injective.ne (by decide),b.injective.ne (by decide),
      b.injective.ne (by decide),b.injective.ne (by decide),b.injective.ne (by decide),
      hbi 0 1 (by decide),hbi 0 2 (by decide),hbi 0 3 (by decide),
      hbi 1 2 (by decide),hbi 1 3 (by decide),hbi 2 3 (by decide)⟩
  have hn : QuadNonstar (b 0) (b 1) (b 2) (b 3) := by
    intro r ⟨h0,h1,h2,h3⟩
    apply hstar
    refine ⟨e0 r,?_⟩
    intro j
    have hj : xorGraph.Adj r (b j) := by fin_cases j <;> assumption
    have hh := e0.map_rel_iff.mpr hj
    change e0 r ≠ e0 (b j) ∧ d (e0 r) (e0 (b j)) = 0 at hh
    rw [hb j] at hh
    exact (mem_colorNeighborhood d 0 (e0 r) (a j)).mpr ⟨Ne.symm hh.1,hh.2⟩
  obtain ⟨p,hp,h0,h3,h5,h6⟩ := nonstar_quad_coordinates (b 0) (b 1) (b 2) (b 3) hquad hn
  let e := p.trans e0.toEquiv
  have he : ∀ j, e (planeRoles j) = a j := by
    intro j
    change e0 (p (planeRoles j)) = a j
    fin_cases j
    · exact (congrArg e0 h0).trans (hb 0)
    · exact (congrArg e0 h3).trans (hb 1)
    · exact (congrArg e0 h5).trans (hb 2)
    · exact (congrArg e0 h6).trans (hb 3)
  let d' := relabelVertices d e
  have hd' : NoMonochromaticTriangle d' := noMono_relabelVertices d e hd
  have hz : ∀ u v, u ≠ v → (d' u v = 0 ↔ PricingG.Completion72.xorClebsch u v = true) := by
    intro u v huv
    have hm : (colorGraph d 0).Adj (e0 (p u)) (e0 (p v)) ↔ xorGraph.Adj u v :=
      e0.map_rel_iff.trans (hp u v)
    rw [xor_graph_binding] at hm
    change (e u ≠ e v ∧ d (e u) (e v) = 0) ↔ _ at hm
    exact ⟨fun hc => (hm.mp ⟨e.injective.ne huv,hc⟩).2,fun hc => (hm.mpr ⟨huv,hc⟩).2⟩
  obtain ⟨i,hi⟩ := PricingG.Completion72.reference_exhaustive d' hd' hz
  have hplane : PathOn i planeRoles := by
    intro j k hjk
    have hinj : Function.Injective planeRoles := by decide
    have hh := hi (planeRoles j) (planeRoles k) (hinj.ne hjk)
    change d (e (planeRoles j)) (e (planeRoles k)) = _ at hh
    rw [he j,he k,hpath j k hjk] at hh
    exact hh.symm
  obtain ⟨i',hi'⟩ := (nonstar_exhaustive i).mp hplane
  refine ⟨i',e,he,?_⟩
  intro u v huv
  rw [hi']
  exact hi u v huv

#print axioms nonstar_four_reference
end PricingC
