import PricingG.CanonicalGuard
import PricingC.GRootNormalization

namespace PricingG
open Finset Ramsey61 PricingC PricingC.GIsomorphic

namespace PhysicalBlock

noncomputable def coordinateColoring {c r p} (b : PhysicalBlock c r p)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ p}) (e : Equiv.Perm (Fin 16)) :
    R4333.EdgeColoring (Fin 16) (Fin 3) :=
  R4333.mapEdgeColors (R4333.relabelVertices b.model e) (b.map.colors.trans pal.symm)

theorem coordinateColoring_good {c r p} (b : PhysicalBlock c r p)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ p}) (e : Equiv.Perm (Fin 16)) :
    R4333.NoMonochromaticTriangle (b.coordinateColoring pal e) :=
  R4333.noMono_mapEdgeColors _ _ (R4333.noMono_relabelVertices _ _ b.good)

theorem coordinateColoring_physical {c r p} (b : PhysicalBlock c r p)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ p}) (e : Equiv.Perm (Fin 16))
    (u v : Fin 16) (huv : u ≠ v) :
    c (b.map.vertex (e u)) (b.map.vertex (e v)) =
      (pal (b.coordinateColoring pal e u v)).val := by
  rw [b.map.map_color _ _ (e.injective.ne huv)]
  change _ = (pal (pal.symm (b.map.colors (b.model (e u) (e v))))).val
  rw [Equiv.apply_symm_apply]

theorem coordinateColoring_zero {c r p} (b : PhysicalBlock c r p)
    (q : FourColor) (hqp : q ≠ p)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ p}) (hp : (pal 0).val = q)
    (e : xorGraph ≃g b.graph q hqp) (u v : Fin 16) (huv : u ≠ v) :
    b.coordinateColoring pal e.toEquiv u v = 0 ↔ Completion72.xorClebsch u v = true := by
  have he : b.coordinateColoring pal e.toEquiv u v = 0 ↔
      c (b.map.vertex (e u)) (b.map.vertex (e v)) = q := by
    change b.coordinateColoring pal e.toEquiv u v = 0 ↔
      c (b.map.vertex (e.toEquiv u)) (b.map.vertex (e.toEquiv v)) = q
    rw [b.coordinateColoring_physical pal e.toEquiv u v huv]
    constructor
    · intro h; rw [h]; exact hp
    · intro h; exact pal.injective (Subtype.ext (h.trans hp.symm))
  rw [he]
  have hg : (b.graph q hqp).Adj (e u) (e v) ↔
      c (b.map.vertex (e u)) (b.map.vertex (e v)) = q :=
    ⟨fun h => ((b.graph_iff q hqp (e u) (e v)).mp h).2,
      fun h => (b.graph_iff q hqp (e u) (e v)).mpr ⟨e.injective.ne huv,h⟩⟩
  rw [←hg,e.map_rel_iff]
  exact (show ∀ u v, xorGraph.Adj u v ↔ Completion72.xorClebsch u v = true from by decide) u v

theorem coordinateColoring_exact72 {c r p} (b : PhysicalBlock c r p)
    (q : FourColor) (hqp : q ≠ p)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ p}) (hp : (pal 0).val = q)
    (e : xorGraph ≃g b.graph q hqp) :
    ∃ i : Fin 72, ∀ u v, u ≠ v → c (b.map.vertex (e u)) (b.map.vertex (e v)) =
      (pal (Completion72.referenceColor i u v)).val := by
  obtain ⟨i,hi⟩ := Completion72.reference_exhaustive (b.coordinateColoring pal e.toEquiv)
    (b.coordinateColoring_good pal e.toEquiv) (b.coordinateColoring_zero q hqp pal hp e)
  refine ⟨i,?_⟩
  intro u v huv
  change c (b.map.vertex (e.toEquiv u)) (b.map.vertex (e.toEquiv v)) = _
  rw [b.coordinateColoring_physical pal e.toEquiv u v huv,hi u v huv]

/-- The exact retained U/T root is reached by a whole vertex automorphism.
The supplied physical palette remains fixed throughout. -/
theorem physical_root_normalized {c r p} (b : PhysicalBlock c r p)
    (q : FourColor) (hqp : q ≠ p)
    (pal : Fin 3 ≃ {a : FourColor // a ≠ p}) (hp : (pal 0).val = q) :
    ∃ (e : xorGraph ≃g b.graph q hqp) (kind : Fin 2), ∀ u v, u ≠ v →
      c (b.map.vertex (e u)) (b.map.vertex (e v)) =
        (pal (Completion72.referenceColor (rootRow kind) u v)).val := by
  let e0 := coordinates (b.graph q hqp) (b.graph_srg q hqp)
  obtain ⟨i,hi⟩ := b.coordinateColoring_exact72 q hqp pal hp e0
  refine ⟨(rootAuto i).trans e0,rootKind i,?_⟩
  intro u v huv
  have hh := hi (rootEquiv i u) (rootEquiv i v) ((rootEquiv i).injective.ne huv)
  rw [roots_normalized] at hh
  exact hh

#print axioms coordinateColoring_exact72
#print axioms physical_root_normalized
end PhysicalBlock
end PricingG
