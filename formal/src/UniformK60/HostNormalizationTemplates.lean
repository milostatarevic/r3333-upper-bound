import UniformK60.HostNormalization
import UniformK60.ClassificationFixedPalette

set_option autoImplicit false
namespace UniformK60.HostNormalization
open Ramsey61 Finset UniformK60.Physical UniformK60.ClassificationAdapter

/-- Any complete labeling of an actual neighborhood is an equivalence with it. -/
noncomputable def neighborhoodIndex {n : Nat} (c : Host) (r : Vertex) (q : FourColor)
    (source : Fin n ↪ Vertex)
    (mem : ∀ i, source i ∈ colorNeighborhood c q r)
    (covers : ∀ v ∈ colorNeighborhood c q r, ∃ i, source i = v) :
    Fin n ≃ {v // v ∈ colorNeighborhood c q r} :=
  Equiv.ofBijective (fun i => ⟨source i, mem i⟩)
    ⟨fun _ _ h => source.injective (congrArg Subtype.val h), by
      intro v
      obtain ⟨i, hi⟩ := covers v.val v.property
      exact ⟨i, Subtype.ext hi⟩⟩

/-- Changing coordinates in one complete neighborhood extends by the identity
on its complement to a permutation of all60 actual host vertices. -/
noncomputable def neighborhoodPermutation {n : Nat} {c : Host} {r : Vertex} {q : FourColor}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (source : Fin n ↪ Vertex)
    (mem : ∀ i, source i ∈ colorNeighborhood c q r)
    (covers : ∀ v ∈ colorNeighborhood c q r, ∃ i, source i = v)
    (m : PhysicalNeighborhoodMap c r q t) : Vertex ≃ Vertex :=
  Equiv.Perm.subtypeCongr
    ((neighborhoodIndex c r q source mem covers).symm.trans m.neighborhoodEquiv) (Equiv.refl _)

theorem neighborhoodPermutation_apply {n : Nat} {c : Host} {r : Vertex} {q : FourColor}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (source : Fin n ↪ Vertex)
    (mem : ∀ i, source i ∈ colorNeighborhood c q r)
    (covers : ∀ v ∈ colorNeighborhood c q r, ∃ i, source i = v)
    (m : PhysicalNeighborhoodMap c r q t) (i : Fin n) :
    neighborhoodPermutation source mem covers m (source i) = m.vertex i := by
  unfold neighborhoodPermutation
  rw [Equiv.Perm.subtypeCongr.left_apply _ _ (mem i)]
  change (m.neighborhoodEquiv ((neighborhoodIndex c r q source mem covers).symm
    ⟨source i, mem i⟩)).val = m.vertex i
  have he : (⟨source i, mem i⟩ : {v // v ∈ colorNeighborhood c q r}) =
      neighborhoodIndex c r q source mem covers i := rfl
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem neighborhoodPermutation_outside {n : Nat} {c : Host} {r : Vertex} {q : FourColor}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (source : Fin n ↪ Vertex)
    (mem : ∀ i, source i ∈ colorNeighborhood c q r)
    (covers : ∀ v ∈ colorNeighborhood c q r, ∃ i, source i = v)
    (m : PhysicalNeighborhoodMap c r q t) (v : Vertex)
    (hv : v ∉ colorNeighborhood c q r) :
    neighborhoodPermutation source mem covers m v = v := by
  unfold neighborhoodPermutation
  rw [Equiv.Perm.subtypeCongr.right_apply _ _ hv]
  rfl

theorem neighborhoodPermutation_root {n : Nat} {c : Host} {r : Vertex} {q : FourColor}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (source : Fin n ↪ Vertex)
    (mem : ∀ i, source i ∈ colorNeighborhood c q r)
    (covers : ∀ v ∈ colorNeighborhood c q r, ∃ i, source i = v)
    (m : PhysicalNeighborhoodMap c r q t) :
    neighborhoodPermutation source mem covers m r = r :=
  neighborhoodPermutation_outside source mem covers m r (by simp)

theorem neighborhoodPermutation_spoke {n : Nat} {c : Host} {r : Vertex} {q : FourColor}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)}
    (source : Fin n ↪ Vertex)
    (mem : ∀ i, source i ∈ colorNeighborhood c q r)
    (covers : ∀ v ∈ colorNeighborhood c q r, ∃ i, source i = v)
    (m : PhysicalNeighborhoodMap c r q t) (v : Vertex) :
    c r (neighborhoodPermutation source mem covers m v) = c r v := by
  by_cases hv : v ∈ colorNeighborhood c q r
  · have hnew : neighborhoodPermutation source mem covers m v ∈ colorNeighborhood c q r := by
      unfold neighborhoodPermutation
      rw [Equiv.Perm.subtypeCongr.left_apply _ _ hv]
      exact ((neighborhoodIndex c r q source mem covers).symm.trans m.neighborhoodEquiv
        ⟨v, hv⟩).property
    exact ((mem_colorNeighborhood _ _ _ _).mp hnew).2.trans
      (((mem_colorNeighborhood _ _ _ _).mp hv).2.symm)
  · rw [neighborhoodPermutation_outside source mem covers m v hv]

/-- Two complete template placements in distinct root groups are realized by
one host permutation. Their palettes remain the original physical colors. -/
theorem simultaneous_neighborhood_maps {nx ny : Nat} {c : Host} {r : Vertex}
    {p q : FourColor} (hpq : p ≠ q)
    {tx : R4333.EdgeColoring (Fin nx) (Fin 3)}
    {ty : R4333.EdgeColoring (Fin ny) (Fin 3)}
    (sx : Fin nx ↪ Vertex) (sy : Fin ny ↪ Vertex)
    (hx : ∀ i, sx i ∈ colorNeighborhood c p r)
    (hy : ∀ j, sy j ∈ colorNeighborhood c q r)
    (cx : ∀ v ∈ colorNeighborhood c p r, ∃ i, sx i = v)
    (cy : ∀ v ∈ colorNeighborhood c q r, ∃ j, sy j = v)
    (mx : PhysicalNeighborhoodMap c r p tx)
    (my : PhysicalNeighborhoodMap c r q ty) :
    ∃ e : Vertex ≃ Vertex, e r = r ∧
      (∀ v, c r (e v) = c r v) ∧
      (∀ i, e (sx i) = mx.vertex i) ∧
      (∀ j, e (sy j) = my.vertex j) := by
  let ex := neighborhoodPermutation sx hx cx mx
  let ey := neighborhoodPermutation sy hy cy my
  refine ⟨ex.trans ey, ?_, ?_, ?_, ?_⟩
  · change ey (ex r) = r
    rw [neighborhoodPermutation_root, neighborhoodPermutation_root]
  · intro v
    exact (neighborhoodPermutation_spoke sy hy cy my (ex v)).trans
      (neighborhoodPermutation_spoke sx hx cx mx v)
  · intro i
    change ey (ex (sx i)) = mx.vertex i
    rw [neighborhoodPermutation_apply]
    apply neighborhoodPermutation_outside
    intro h
    have hp := ((mem_colorNeighborhood _ _ _ _).mp (mx.mem_neighborhood i)).2
    have hq := ((mem_colorNeighborhood _ _ _ _).mp h).2
    exact hpq (hp.symm.trans hq)
  · intro j
    change ey (ex (sy j)) = my.vertex j
    have hout : sy j ∉ colorNeighborhood c p r := by
      intro h
      have hp := ((mem_colorNeighborhood _ _ _ _).mp h).2
      have hq := ((mem_colorNeighborhood _ _ _ _).mp (hy j)).2
      exact hpq (hp.symm.trans hq)
    rw [neighborhoodPermutation_outside sx hx cx mx (sy j) hout,
      neighborhoodPermutation_apply]

#print axioms simultaneous_neighborhood_maps
end UniformK60.HostNormalization
