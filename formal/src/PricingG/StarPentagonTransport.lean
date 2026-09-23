import PricingG.LocalStarPentagonCompact

namespace PricingG
open Finset PricingC

/-- A graph isomorphism transports whole neighbor sets, not separately chosen
edge incidences. -/
theorem graphIso_neighbor_image {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {K : SimpleGraph V} {L : SimpleGraph W}
    [DecidableRel K.Adj] [DecidableRel L.Adj] (e : K ≃g L) (x : V) :
    (K.neighborFinset x).image e = L.neighborFinset (e x) := by
  ext y
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact (L.mem_neighborFinset _ _).mpr (e.map_rel_iff.mpr ((K.mem_neighborFinset _ _).mp ha))
  · intro h
    refine mem_image.mpr ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply (K.mem_neighborFinset _ _).mpr
    apply e.map_rel_iff.mp
    simpa only [e.apply_symm_apply] using (L.mem_neighborFinset _ _).mp h

theorem graphIso_filter_card {V W : Type*} [DecidableEq V] [DecidableEq W]
    {K : SimpleGraph V} {L : SimpleGraph W} [DecidableRel K.Adj] [DecidableRel L.Adj]
    (e : K ≃g L) (A : Finset V) (x : V) :
    ((A.image e).filter fun a => L.Adj (e x) a).card =
      (A.filter fun a => K.Adj x a).card := by
  have heq : (A.image e).filter (fun a => L.Adj (e x) a) =
      (A.filter fun a => K.Adj x a).image e := by
    ext y
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp (mem_filter.mp h).1
      exact mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,e.map_rel_iff.mp (mem_filter.mp h).2⟩,rfl⟩
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_image.mpr ⟨a,(mem_filter.mp ha).1,rfl⟩,
        e.map_rel_iff.mpr (mem_filter.mp ha).2⟩
  rw [heq,card_image_of_injective _ e.injective]

/-- Every actual rooted Clebsch five-support obeying the physical masks is
an intrinsic star or an induced pentagon with its exact rooted incidence law. -/
theorem rooted_star_or_pentagon
    (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj] (hK : K.IsSRGWith 16 5 0 2)
    (v : Fin 16) (A : Finset (Fin 16)) (hA : A.card = 5)
    (havoid : Disjoint A (K.neighborFinset v)) (hmasks : RootMaskCondition K v A) :
    (∃ a, K.Adj v a ∧ A = K.neighborFinset a) ∨
      (InducedDegreeTwo K A ∧ RootPentagonLaw K v A) := by
  classical
  have hpoints : Fintype.card ↥(R4333.clebschA K v) = 5 := by
    simpa only [Fintype.card_coe] using R4333.card_clebschA K hK v
  let points : Fin 5 ≃ ↥(R4333.clebschA K v) := (Fintype.equivFinOfCardEq hpoints).symm
  let e := anchoredCoordinates K hK v points
  have he0 : e 0 = v := anchoredCoordinates_root K hK v points
  let A' := A.image e.symm
  have heA : A'.image e = A := by
    simp [A',Finset.image_image]
  have hcA : A'.card = 5 := by rw [card_image_of_injective _ e.symm.injective]; exact hA
  have hsub : A' ⊆ univ \ xorGraph.neighborFinset 0 := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hx
    have hg := e.map_rel_iff.mpr ((xorGraph.mem_neighborFinset _ _).mp hx)
    rw [he0,e.apply_symm_apply] at hg
    exact disjoint_left.mp havoid ha ((K.mem_neighborFinset _ _).mpr hg)
  have hmask' : RootMaskCondition xorGraph 0 A' := by
    intro x hx
    have hex : e x ∈ K.neighborFinset v := by
      apply (K.mem_neighborFinset _ _).mpr
      rw [← he0]
      exact e.map_rel_iff.mpr ((xorGraph.mem_neighborFinset _ _).mp hx)
    have hm := hmasks (e x) hex
    have hc := graphIso_filter_card e A' x
    rw [heA] at hc
    rwa [hc] at hm
  rcases canonical_root_star_or_pentagon A' (mem_powersetCard.mpr ⟨hsub,hcA⟩) hmask' with hs | hp
  · obtain ⟨a,ha,hset⟩ := hs
    left
    refine ⟨e a,?_,?_⟩
    · rw [← he0]
      exact e.map_rel_iff.mpr ha
    · rw [← heA,hset,graphIso_neighbor_image]
  · right
    constructor
    · intro x hx
      have hx' : e.symm x ∈ A' := mem_image.mpr ⟨x,hx,rfl⟩
      have hh := hp.1 (e.symm x) hx'
      have hc := graphIso_filter_card e A' (e.symm x)
      rw [heA,e.apply_symm_apply] at hc
      rwa [hc]
    · intro x
      have hh := hp.2 (e.symm x)
      have hc := graphIso_filter_card e A' (e.symm x)
      rw [heA,e.apply_symm_apply] at hc
      rw [← hc] at hh
      have hxv : e.symm x = 0 ↔ x = v := by
        constructor
        · intro h
          have hh := congrArg e h
          simpa only [e.apply_symm_apply,he0] using hh
        · intro h
          rw [h,← he0,e.symm_apply_apply]
      have hxa : e.symm x ∈ A' ↔ x ∈ A := by simp [A']
      have hxadj : xorGraph.Adj 0 (e.symm x) ↔ K.Adj v x := by
        simpa only [e.apply_symm_apply,he0] using
          (e.map_rel_iff (a := (0 : Fin 16)) (b := e.symm x)).symm
      simpa only [hxv,hxa,hxadj] using hh

#print axioms rooted_star_or_pentagon
end PricingG
