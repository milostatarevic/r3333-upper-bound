import PricingG.StarPentagonTransport

namespace PricingG
open Finset

theorem graphIso_commonNeighbors_card
    {K L : SimpleGraph (Fin 16)} [DecidableRel K.Adj] [DecidableRel L.Adj]
    (e : K ≃g L) (u v : Fin 16) :
    Fintype.card (K.commonNeighbors u v) = Fintype.card (L.commonNeighbors (e u) (e v)) := by
  apply Fintype.card_congr
  exact e.toEquiv.subtypeEquiv (fun x =>
    and_congr (e.map_rel_iff (a := u) (b := x)).symm
      (e.map_rel_iff (a := v) (b := x)).symm)

theorem graphIso_srg
    {K L : SimpleGraph (Fin 16)} [DecidableRel K.Adj] [DecidableRel L.Adj]
    (e : K ≃g L) (hK : K.IsSRGWith 16 5 0 2) : L.IsSRGWith 16 5 0 2 := by
  refine ⟨by decide,?_,?_,?_⟩
  · intro y
    have h := congrArg Finset.card (graphIso_neighbor_image e (e.symm y))
    rw [card_image_of_injective _ e.injective,e.apply_symm_apply,
      SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at h
    rw [← h]
    exact hK.regular _
  · intro u v huv
    have h := graphIso_commonNeighbors_card e (e.symm u) (e.symm v)
    simp only [e.apply_symm_apply] at h
    rw [← h]
    exact hK.of_adj _ _ (e.symm.map_rel_iff.mpr huv)
  · intro u v huv hnot
    have h := graphIso_commonNeighbors_card e (e.symm u) (e.symm v)
    simp only [e.apply_symm_apply] at h
    rw [← h]
    apply hK.of_not_adj (e.symm.injective.ne huv)
    intro he
    apply hnot
    simpa only [e.apply_symm_apply] using e.map_rel_iff.mpr he

#print axioms graphIso_srg
end PricingG
