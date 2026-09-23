import PricingG.DecompositionColoring
import PricingC.AdjacentAutomorphisms

namespace PricingG
open Finset Ramsey61 PricingC

theorem srg_neighbor_injective (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) : Function.Injective (fun y => K.neighborFinset y) := by
  let e := coordinates K hK
  have hcanon : Function.Injective (fun y => xorGraph.neighborFinset y) := by decide
  intro x y he
  apply e.symm.injective
  apply hcanon
  have hh := congrArg (fun s : Finset (Fin 16) => s.image e.symm) he
  rwa [graphIso_neighbor_image,graphIso_neighbor_image] at hh

theorem RegularOverlapGuard.reverse {c r p q} (h : RegularOverlapGuard c r p q) :
    RegularOverlapGuard c r q p where
  colors_distinct := h.colors_distinct.symm
  first_root_degree := h.second_root_degree
  second_root_degree := h.first_root_degree
  other_root_degrees a haq hap := h.other_root_degrees a hap haq
  eligible_root := h.eligible_root
  first_fibers := h.second_fibers
  second_fibers := h.first_fibers
  first_opposite_high := h.second_opposite_high
  second_opposite_high := h.first_opposite_high

namespace GuardedGraphModel

noncomputable def reverse {c r p q hpq} (m : GuardedGraphModel c r p q hpq) :
    GuardedGraphModel c r q p hpq.symm where
  X := m.Y
  Y := m.X
  f := m.g
  g := m.f
  first_fiber x y := by
    change (m.Y.graph p hpq).Adj (m.g y) x ↔ c (m.Y.map.vertex x) (m.X.map.vertex y) = p
    rw [m.second_fiber,c.color_symm]
  second_fiber x y := by
    change (m.X.graph q hpq.symm).Adj (m.f x) y ↔ c (m.Y.map.vertex x) (m.X.map.vertex y) = q
    rw [m.first_fiber,c.color_symm]

/-- Once the shared graphs coincide, the physical center composition sends
every vertex to a neighbor. -/
theorem identity_graph_adjacent {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q)
    (heq : m.K = m.J) : ∀ y, m.K.Adj y (m.imageRule y) := by
  intro y
  have hNJ : m.J.neighborFinset y = m.K.neighborFinset y := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset]
    rw [←heq]
  rcases m.shared_graph_rooted_dichotomy hc hG y with ⟨a,hpa,ha⟩ | hp
  · rw [hNJ] at ha
    have hay : y = a := srg_neighbor_injective m.K m.K_srg ha
    subst a
    exact hpa.symm
  · rw [hNJ] at hp
    obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (m.K.neighborFinset y).card by
      rw [SimpleGraph.card_neighborFinset_eq_degree,m.K_srg.regular y]; decide)
    have hh := hp.1 x hx
    rw [star_filter_card_zero m.K m.K_srg y x hx] at hh
    omega

/-- The reciprocal neighborhood contains an isolated vertex, so it cannot
be a pentagon. This proves the second center map is an isomorphism as well;
it is not inferred merely from the first map being an isomorphism. -/
theorem reverse_has_zero_defects {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q)
    (heq : m.K = m.J) : defectCount m.reverse.K m.reverse.J = 0 := by
  classical
  have hadj := m.identity_graph_adjacent hc hG heq
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hdeg := (mem_filter.mp hy).2
  let z := m.g (m.f y)
  have hz : z ∈ m.reverse.J.neighborFinset y := by
    apply (m.reverse.J.mem_neighborFinset _ _).mpr
    rw [m.reverse.J_iff]
    exact hadj (m.f y)
  have hisolated : ((m.reverse.J.neighborFinset y).filter fun w => m.reverse.K.Adj z w).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hkw : m.K.Adj (m.f w) (m.f y) := by
      have h := (m.reverse.J_iff y w).mp ((m.reverse.J.mem_neighborFinset _ _).mp (mem_filter.mp hw).1)
      exact h.symm
    have hq := (m.first_fiber (m.f y) w).mp hkw
    have hp := (m.second_fiber (m.f y) w).mp (mem_filter.mp hw).2
    exact hpq (hp.symm.trans hq)
  have hh := hdeg z hz
  rw [hisolated] at hh
  omega

noncomputable def secondCenterIso {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (heq : m.K = m.J) : m.K ≃g (m.Y.graph p hpq) where
  toEquiv := m.g
  map_rel_iff' := by
    intro x y
    rw [←m.J_iff,←heq]

noncomputable def firstCenterIso {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q)
    (heq : m.K = m.J) : (m.Y.graph p hpq) ≃g m.K where
  toEquiv := m.f
  map_rel_iff' := by
    have hr : m.reverse.K = m.reverse.J := zero_defects_graph_eq _ _
      m.reverse.K_srg m.reverse.J_srg
      (GraphRootedDichotomy.unrooted (m.reverse.shared_graph_rooted_dichotomy hc (PricingG.RegularOverlapGuard.reverse hG)))
      (m.reverse_has_zero_defects hc hG heq)
    intro x y
    change (m.reverse.Y.graph q hpq.symm).Adj (m.reverse.g x) (m.reverse.g y) ↔ m.reverse.K.Adj x y
    rw [←m.reverse.J_iff,←hr]

noncomputable def imageAutomorphism {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q)
    (heq : m.K = m.J) : m.K ≃g m.K :=
  (m.secondCenterIso heq).trans (m.firstCenterIso hc hG heq)

/-- The zero-defect physical endpoint has exactly one of the retained25
center permutations in common XOR coordinates. -/
theorem zero_defects_exact25_coordinates {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q)
    (hz : defectCount m.K m.J = 0) (e : xorGraph ≃g m.K) :
    ∃ (i : Fin 25), ∀ v,
      e.symm (m.imageRule (e v)) = AdjacentAutomorphisms.retainedMap i v := by
  have heq : m.K = m.J := zero_defects_graph_eq _ _ m.K_srg m.J_srg
    (GraphRootedDichotomy.unrooted (m.shared_graph_rooted_dichotomy hc hG)) hz
  let a : xorGraph ≃g xorGraph := (e.trans (m.imageAutomorphism hc hG heq)).trans e.symm
  have ha : ∀ v, xorGraph.Adj v (a v) := by
    intro v
    have hh := m.identity_graph_adjacent hc hG heq (e v)
    have hh' := e.symm.map_rel_iff.mpr hh
    change xorGraph.Adj v (e.symm (m.imageRule (e v)))
    rw [show e.symm (e v) = v from e.symm_apply_apply v] at hh'
    exact hh'
  obtain ⟨i,hi⟩ := AdjacentAutomorphisms.adjacent_automorphism_retained a ha
  exact ⟨i,hi⟩

theorem zero_defects_exact25 {c r p q hpq} (m : GuardedGraphModel c r p q hpq)
    (hc : NoMonochromaticTriangle c) (hG : RegularOverlapGuard c r p q)
    (hz : defectCount m.K m.J = 0) :
    ∃ (e : xorGraph ≃g m.K) (i : Fin 25), ∀ v,
      e.symm (m.imageRule (e v)) = AdjacentAutomorphisms.retainedMap i v := by
  obtain ⟨i,hi⟩ := m.zero_defects_exact25_coordinates hc hG hz (coordinates m.K m.K_srg)
  exact ⟨coordinates m.K m.K_srg,i,hi⟩

#print axioms reverse_has_zero_defects
#print axioms firstCenterIso
#print axioms zero_defects_exact25
end GuardedGraphModel
end PricingG
