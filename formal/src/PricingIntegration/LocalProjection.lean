import PricingC.AutomorphismRigidity
import PricingC.PhysicalY

namespace PricingIntegration.LocalProjection
open Ramsey61 Ramsey61.CEncodingCore PricingC PricingG.Completion72

theorem reference_zero_iff (i : Fin 72) (u v : Fin 16) (hne : u ≠ v) :
    referenceColor i u v = 0 ↔ xorGraph.Adj u v := by
  rw [xor_graph_binding]
  simp only [referenceColor, hne, if_false, true_and]
  cases hx : xorClebsch u v <;> simp [hx,hne]
  split <;> decide

/-- Any ordered actual independent five-anchor fixes the reference
coordinates of every other observed scope vertex through its exact high
color mask. Therefore the entire physical K10 (or other restriction) is a
projection of one of the retained72rows. Degree15 needs no extra physical
vertex for the absent completion point. -/
theorem physical_scope_projection {n : Nat}
    (c : Host) (hc : NoMonochromaticTriangle c) (owner : Vertex) (omitted : FourColor)
    (hhigh : 15 ≤ colorDegree c omitted owner)
    (pal : Fin 3 ≃ {q : FourColor // q ≠ omitted})
    (phys : Fin n ↪ Vertex) (hmem : ∀ k, phys k ∈ colorNeighborhood c omitted owner)
    (anchor : Fin 5 ↪ Fin n) (role : Fin n → Fin 16)
    (hind : ∀ j k, j ≠ k → c (phys (anchor j)) (phys (anchor k)) ≠ (pal 0).val)
    (hanchor : ∀ j, role (anchor j) = generators j)
    (hout : ∀ k, (∀ j, k ≠ anchor j) → ∀ j, role k ≠ generators j)
    (hmask : ∀ k, (∀ j, k ≠ anchor j) → ∀ j,
      (c (phys (anchor j)) (phys k) = (pal 0).val ↔ xorGraph.Adj (generators j) (role k))) :
    ∃ i : Fin 72, ∀ u v : Fin n, u ≠ v →
      c (phys u) (phys v) = (pal (referenceColor i (role u) (role v))).val := by
  classical
  obtain ⟨m⟩ := high_neighborhood_completion c hc owner omitted hhigh pal
  let point : Fin n ↪ m.present := liftPhysical m phys hmem
  let a : Fin 5 ↪ m.present := anchor.trans point
  have hpoint : ∀ k, m.vertex (point k) = phys k := liftPhysical_val m phys hmem
  have hA : R4333.IsColorIndependentSet m.model 0 (referenceAnchor m a) := by
    apply referenceAnchor_independent m a 0
    intro j k hjk
    change c (m.vertex (point (anchor j))) (m.vertex (point (anchor k))) ≠ _
    rw [hpoint,hpoint]
    exact hind j k hjk
  obtain ⟨r,hr,_⟩ := IndependentFive.good_K16_independent_five_unique_center
    m.model m.good 0 (referenceAnchor m a) (referenceAnchor_card m a) hA
  obtain ⟨i,e,_,he,hecolor⟩ := ordered_anchor_reference m.model m.good r (anchorPointEquiv m a r hr)
  have he' : ∀ j, e (generators j) = (point (anchor j)).val := he
  let coord (k : Fin n) := e.symm (point k).val
  have hcinj : Function.Injective coord := by
    intro u v h
    exact point.injective (Subtype.ext (e.symm.injective h))
  have hca : ∀ j, coord (anchor j) = generators j := by
    intro j
    change e.symm (point (anchor j)).val = generators j
    rw [←he',Equiv.symm_apply_apply]
  have hcolors : ∀ u v, u ≠ v →
      c (phys u) (phys v) = (pal (referenceColor i (coord u) (coord v))).val := by
    intro u v huv
    have hm := m.map_color (point u) (point v) (point.injective.ne huv)
    rw [hpoint,hpoint] at hm
    have hh := hecolor (coord u) (coord v) (hcinj.ne huv)
    simp only [coord,Equiv.apply_symm_apply] at hh
    exact hm.trans (congrArg (fun q => (pal q).val) hh)
  have hcoord : ∀ k, coord k = role k := by
    intro k
    by_cases ha : ∃ j, k = anchor j
    · obtain ⟨j,rfl⟩ := ha
      rw [hca,hanchor]
    · have hka : ∀ j, k ≠ anchor j := by simpa using ha
      have hcoutside : ∀ j, coord k ≠ generators j := by
        intro j h
        exact hka j (hcinj (h.trans (hca j).symm))
      apply outside_anchor_mask_injective (coord k) (role k) hcoutside (hout k hka)
      intro j
      have hcol := hcolors (anchor j) k (hka j).symm
      rw [hca] at hcol
      have hiff : c (phys (anchor j)) (phys k) = (pal 0).val ↔
          referenceColor i (generators j) (coord k) = 0 := by
        rw [hcol]
        exact ⟨fun h => pal.injective (Subtype.ext h),fun h => congrArg (fun q => (pal q).val) h⟩
      rw [xorGraph.adj_comm (coord k),xorGraph.adj_comm (role k)]
      exact (reference_zero_iff i (generators j) (coord k) (hcoutside j).symm).symm.trans
        (hiff.symm.trans (hmask k hka j))
  refine ⟨i,?_⟩
  intro u v huv
  simpa only [hcoord] using hcolors u v huv

#print axioms physical_scope_projection
end PricingIntegration.LocalProjection
