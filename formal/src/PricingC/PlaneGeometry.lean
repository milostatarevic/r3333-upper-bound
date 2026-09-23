import PricingC.PlaneTables
import PricingC.UnanchoredReference

namespace PricingC
open PlaneTables

 theorem quad_independent_map (e : Fin 16 ≃ Fin 16)
    (he : ∀ u v, xorGraph.Adj (e u) (e v) ↔ xorGraph.Adj u v) (a b c d : Fin 16) :
    QuadIndependent (e a) (e b) (e c) (e d) ↔ QuadIndependent a b c d := by
  simp only [QuadIndependent,ne_eq,e.injective.eq_iff,he]

 theorem quad_nonstar_map (e : Fin 16 ≃ Fin 16)
    (he : ∀ u v, xorGraph.Adj (e u) (e v) ↔ xorGraph.Adj u v) (a b c d : Fin 16) :
    QuadNonstar (e a) (e b) (e c) (e d) ↔ QuadNonstar a b c d := by
  constructor
  · intro h r
    have hh := h (e r)
    simpa only [he] using hh
  · intro h r
    obtain ⟨s,rfl⟩ := e.surjective r
    simpa only [he] using h s

/-- Every ordered nonstar independent four-set admits the exact plane
coordinates, retaining its complete prescribed physical order. -/
theorem nonstar_quad_coordinates (a b c d : Fin 16)
    (hind : QuadIndependent a b c d) (hn : QuadNonstar a b c d) :
    ∃ e : Fin 16 ≃ Fin 16,
      (∀ u v, xorGraph.Adj (e u) (e v) ↔ xorGraph.Adj u v) ∧
      e 0 = a ∧ e 3 = b ∧ e 5 = c ∧ e 6 = d := by
  let t := xorTranslation a
  have ht := xorTranslation_graph a
  have hi' := (quad_independent_map t ht a b c d).mpr hind
  have hn' := (quad_nonstar_map t ht a b c d).mpr hn
  have hz : t a = 0 := xorTranslation_self a
  rw [hz] at hi' hn'
  obtain ⟨h0,h3,h5,h6⟩ := nonstar_zero_coordinates (t b) (t c) (t d) hi' hn'
  let p := planeMap (t b) (t c)
  refine ⟨p.trans t,?_,?_,?_,?_,?_⟩
  · intro u v
    exact (ht (p u) (p v)).trans (planeMap_graph _ _ u v)
  · change t (p 0) = a
    rw [h0]
    exact xorTranslation_zero a
  · change t (p 3) = b
    rw [h3]
    exact t.left_inv b
  · change t (p 5) = c
    rw [h5]
    exact t.left_inv c
  · change t (p 6) = d
    rw [h6]
    exact t.left_inv d

#print axioms nonstar_quad_coordinates
end PricingC
