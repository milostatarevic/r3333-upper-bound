import PricingG.GraphEndpoints
import PricingG.Completion72

namespace PricingG
open Finset Matrix

abbrev GMatrix := Matrix (Fin 16) (Fin 16) ℤ
def allOnes : GMatrix := fun _ _ => 1

theorem regular_adj_ones (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) : K.adjMatrix ℤ * allOnes = (5 : ℤ) • allOnes := by
  ext x y
  rw [K.adjMatrix_mul_apply]
  simp [allOnes,hK.regular x]

theorem regular_ones_adj (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) : allOnes * K.adjMatrix ℤ = (5 : ℤ) • allOnes := by
  ext x y
  rw [K.mul_adjMatrix_apply]
  simp [allOnes,hK.regular y]

theorem allOnes_square : allOnes * allOnes = (16 : ℤ) • allOnes := by decide

theorem srg_matrix_square (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj]
    (hK : K.IsSRGWith 16 5 0 2) :
    K.adjMatrix ℤ * K.adjMatrix ℤ = (3 : ℤ) • (1 : GMatrix) -
      (2 : ℤ) • K.adjMatrix ℤ + (2 : ℤ) • allOnes := by
  have hs : K.adjMatrix ℤ * K.adjMatrix ℤ = (5 : ℤ) • (1 : GMatrix) + (2 : ℤ) • Kᶜ.adjMatrix ℤ := by
    have hh : K.adjMatrix ℤ * K.adjMatrix ℤ = (5 : ℕ) • (1 : GMatrix) + (2 : ℕ) • Kᶜ.adjMatrix ℤ := by
      simpa only [pow_two,zero_smul,add_zero] using hK.matrix_eq (α := ℤ)
    rw [hh]
    ext x y
    simp
  have hc : Kᶜ.adjMatrix ℤ = allOnes - 1 - K.adjMatrix ℤ := by
    ext x y
    by_cases hxy : x = y
    · subst y; simp [SimpleGraph.adjMatrix_apply,allOnes,Matrix.one_apply]
    · by_cases h : K.Adj x y <;> simp [SimpleGraph.adjMatrix_apply,allOnes,Matrix.one_apply,hxy,h,SimpleGraph.compl_adj]
  rw [hs,hc]
  ext x y
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem full_defects_root_law (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) (y : Fin 16) : RootPentagonLaw K y (J.neighborFinset y) := by
  have hpent := full_defects_all_pentagons K J hz y
  rcases hd y with ⟨a,_,ha⟩ | hp
  · obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (J.neighborFinset y).card by
      rw [SimpleGraph.card_neighborFinset_eq_degree,hJ.regular y]; decide)
    have he := hpent x hx
    rw [ha] at hx he
    rw [star_filter_card_zero K hK a x hx] at he
    omega
  · have hh := hp.2
    rwa [full_defects_image_identity K J hK hJ ρ hd hz y] at hh

theorem full_defects_product (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) :
    K.adjMatrix ℤ * J.adjMatrix ℤ = allOnes - 1 + K.adjMatrix ℤ + J.adjMatrix ℤ := by
  have hdj := full_defects_disjoint K J hK hJ hd.unrooted hz
  ext x y
  rw [J.mul_adjMatrix_apply]
  have he : (∑ z ∈ J.neighborFinset y, K.adjMatrix ℤ x z) =
      (((J.neighborFinset y).filter fun z => K.Adj x z).card : ℤ) := by
    simp [SimpleGraph.adjMatrix_apply,← sum_filter]
  rw [he,full_defects_root_law K J hK hJ ρ hd hz y x]
  by_cases hxy : x = y
  · subst y; simp [allOnes,SimpleGraph.adjMatrix_apply]
  · have hdis := hdj x y
    by_cases hk : K.Adj x y <;> by_cases hj : J.Adj x y <;>
      simp_all [allOnes,SimpleGraph.mem_neighborFinset,SimpleGraph.adjMatrix_apply,K.adj_comm,J.adj_comm,Matrix.one_apply]

def thirdGraph (K J : SimpleGraph (Fin 16)) : SimpleGraph (Fin 16) := (K ⊔ J)ᶜ

instance thirdGraphDecidable (K J : SimpleGraph (Fin 16)) [DecidableRel K.Adj] [DecidableRel J.Adj] :
    DecidableRel (thirdGraph K J).Adj := by unfold thirdGraph; infer_instance

theorem thirdGraph_matrix (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (hd : ∀ x y, ¬(K.Adj x y ∧ J.Adj x y)) :
    (thirdGraph K J).adjMatrix ℤ = allOnes - 1 - K.adjMatrix ℤ - J.adjMatrix ℤ := by
  ext x y
  have hdis := hd x y
  by_cases hxy : x = y
  · subst y; simp [SimpleGraph.adjMatrix_apply,allOnes,Matrix.one_apply]
  · by_cases hk : K.Adj x y <;> by_cases hj : J.Adj x y <;>
      simp_all [SimpleGraph.adjMatrix_apply,thirdGraph,SimpleGraph.compl_adj,allOnes,Matrix.one_apply]

theorem full_defects_third_square (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) :
    (thirdGraph K J).adjMatrix ℤ * (thirdGraph K J).adjMatrix ℤ =
      (5 : ℤ) • (1 : GMatrix) + (2 : ℤ) • K.adjMatrix ℤ + (2 : ℤ) • J.adjMatrix ℤ := by
  have hprod := full_defects_product K J hK hJ ρ hd hz
  have hprod' : J.adjMatrix ℤ * K.adjMatrix ℤ = allOnes - 1 + K.adjMatrix ℤ + J.adjMatrix ℤ := by
    have hh := congrArg Matrix.transpose hprod
    simpa only [Matrix.transpose_mul,SimpleGraph.transpose_adjMatrix,Matrix.transpose_add,
      Matrix.transpose_sub,Matrix.transpose_one,show allOnesᵀ = allOnes from rfl] using hh
  rw [thirdGraph_matrix K J (full_defects_disjoint K J hK hJ hd.unrooted hz)]
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    allOnes_square,regular_adj_ones K hK,regular_adj_ones J hJ,
    regular_ones_adj K hK,regular_ones_adj J hJ,srg_matrix_square K hK,
    srg_matrix_square J hJ,hprod,hprod']
  ext x y
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

#print axioms full_defects_third_square
end PricingG
