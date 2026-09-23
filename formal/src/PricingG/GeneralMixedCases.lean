import PricingG.RootedRelabel
import PricingG.GuardedGraphModel

namespace PricingG
open Finset PricingC SignDesign

noncomputable def coordinates (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) : xorGraph ≃g K :=
  anchoredCoordinates K hK 0
    (Fintype.equivFinOfCardEq (show Fintype.card ↥(R4333.clebschA K 0) = 5 from
      by simpa only [Fintype.card_coe] using R4333.card_clebschA K hK 0)).symm

def GraphRootedDichotomy (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (ρ : Equiv.Perm (Fin 16)) : Prop :=
  ∀ y, (∃ a, K.Adj (ρ y) a ∧ J.neighborFinset y = K.neighborFinset a) ∨
    (InducedDegreeTwo K (J.neighborFinset y) ∧ RootPentagonLaw K (ρ y) (J.neighborFinset y))

/-- One common coordinate map is used for both graphs; only the independent
reference description of J is encoded by the permutation. -/
noncomputable def normalizedPermutation {K J : SimpleGraph (Fin 16)}
    (eK : xorGraph ≃g K) (eJ : xorGraph ≃g J) : Equiv.Perm (Fin 16) :=
  eK.toEquiv.trans eJ.toEquiv.symm

noncomputable def normalizedJIso {K J : SimpleGraph (Fin 16)}
    (eK : xorGraph ≃g K) (eJ : xorGraph ≃g J) :
    permutedGraph (normalizedPermutation eK eJ) ≃g J where
  toEquiv := eK.toEquiv
  map_rel_iff' := by
    intro a b
    change J.Adj (eK a) (eK b) ↔ xorGraph.Adj (eJ.symm (eK a)) (eJ.symm (eK b))
    exact eJ.symm.map_rel_iff.symm

theorem rootedDichotomy_normalized {K J : SimpleGraph (Fin 16)}
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (eK : xorGraph ≃g K) (eJ : xorGraph ≃g J) (ρ : Equiv.Perm (Fin 16))
    (hd : GraphRootedDichotomy K J ρ) :
    RootedDichotomy (normalizedPermutation eK eJ) (eK.toEquiv.trans (ρ.trans eK.toEquiv.symm)) := by
  intro y
  let σ := normalizedPermutation eK eJ
  have himage : ((permutedGraph σ).neighborFinset y).image eK = J.neighborFinset (eK y) :=
    graphIso_neighbor_image (normalizedJIso eK eJ) y
  have hpull : (J.neighborFinset (eK y)).image eK.symm = (permutedGraph σ).neighborFinset y := by
    rw [← himage,Finset.image_image]
    simp
  rcases hd (eK y) with hs | hp
  · obtain ⟨a,hpa,ha⟩ := hs
    left
    refine ⟨eK.symm a,eK.symm.map_rel_iff.mpr hpa,?_⟩
    rw [← hpull,ha,graphIso_neighbor_image]
  · right
    constructor
    · rw [← hpull]
      exact SignDesign.inducedDegreeTwo_image eK.symm _ hp.1
    · change RootPentagonLaw xorGraph (eK.symm (ρ (eK y))) _
      rw [← hpull]
      exact SignDesign.rootedPentagonLaw_image eK.symm _ _ hp.2

theorem defectCount_normalized {K J : SimpleGraph (Fin 16)}
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (eK : xorGraph ≃g K) (eJ : xorGraph ≃g J) :
    defectCount xorGraph (permutedGraph (normalizedPermutation eK eJ)) = defectCount K J := by
  classical
  let σ := normalizedPermutation eK eJ
  have hdeg (y : Fin 16) : InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset y) ↔
      InducedDegreeTwo K (J.neighborFinset (eK y)) := by
    have himage : ((permutedGraph σ).neighborFinset y).image eK = J.neighborFinset (eK y) :=
      graphIso_neighbor_image (normalizedJIso eK eJ) y
    constructor
    · intro h
      rw [← himage]
      exact SignDesign.inducedDegreeTwo_image eK _ h
    · intro h
      have hp := SignDesign.inducedDegreeTwo_image eK.symm _ h
      rw [← himage,Finset.image_image] at hp
      simpa using hp
  have heq : (univ.filter fun y => InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset y)).image eK =
      univ.filter fun y => InducedDegreeTwo K (J.neighborFinset y) := by
    ext x
    constructor
    · intro h
      obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_univ _,(hdeg y).mp (mem_filter.mp hy).2⟩
    · intro h
      refine mem_image.mpr ⟨eK.symm x,mem_filter.mpr ⟨mem_univ _,?_⟩,eK.apply_symm_apply x⟩
      apply (hdeg (eK.symm x)).mpr
      have hx : eK (eK.symm x) = x := eK.apply_symm_apply x
      exact hx.symm ▸ (mem_filter.mp h).2
  have hc := congrArg Finset.card heq
  rw [card_image_of_injective _ eK.injective] at hc
  exact hc

/-- The three high mixed counts are excluded for arbitrary simultaneously
labeled Clebsch graphs, not only the canonical drawings. -/
theorem high_mixed_counts_excluded (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ) :
    defectCount K J ≠ 10 ∧ defectCount K J ≠ 12 ∧ defectCount K J ≠ 14 := by
  let eK := coordinates K hK
  let eJ := coordinates J hJ
  let σ := normalizedPermutation eK eJ
  let ρ' := eK.toEquiv.trans (ρ.trans eK.toEquiv.symm)
  have hd' : RootedDichotomy σ ρ' := rootedDichotomy_normalized eK eJ ρ hd
  have hc := starSet_add_defects σ
  rw [defectCount_normalized eK eJ] at hc
  refine ⟨?_,?_,?_⟩
  · intro h
    exact no_six_star_rows σ ρ' hd' (by omega)
  · intro h
    exact no_four_star_rows σ ρ' hd' (by omega)
  · intro h
    exact no_two_star_rows σ ρ' hd' (by omega)

theorem GuardedGraphModel.high_mixed_counts_excluded {c r p q hpq}
    (m : GuardedGraphModel c r p q hpq) (hc : Ramsey61.NoMonochromaticTriangle c)
    (hG : Ramsey61.RegularOverlapGuard c r p q) :
    defectCount m.K m.J ≠ 10 ∧ defectCount m.K m.J ≠ 12 ∧ defectCount m.K m.J ≠ 14 :=
  PricingG.high_mixed_counts_excluded m.K m.J m.K_srg m.J_srg m.imageRule
    (m.shared_graph_rooted_dichotomy hc hG)

#print axioms high_mixed_counts_excluded
#print axioms GuardedGraphModel.high_mixed_counts_excluded
end PricingG
