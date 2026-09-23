import PricingG.ZeroPairGeometry

namespace PricingG.SignDesign
open Finset PricingC

private theorem star_of_four (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (y : Fin 16) (i : Fin 5) (h4 : |evaluation σ y i| = 4) : y ∈ starSet σ := by
  by_contra hnot
  have h := (pentagon_row_data σ ρ hd y hnot).2.1 i
  omega

/-- Once the actual common-center vertex is the shared origin, the s=6
configuration forces seven distinct star rows, contradicting its count. -/
theorem no_six_stars_canonical (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 6) (hσ : σ 0 = 0)
    (hroot : (permutedGraph σ).neighborFinset 0 = xorGraph.neighborFinset 0) : False := by
  have hrall : ∀ i : Fin 5, row 0 i = 1 := by decide
  have hcol (i : Fin 5) : ∑ j, overlap σ j i = 4 := by
    have h := overlap_evaluation σ 0 i
    rw [hσ,root_evaluation,hroot,neighborhood_centroid] at h
    have hr := hrall i
    rw [hr] at h
    norm_num at h
    exact h
  have hnon : ∀ i j, 0 ≤ overlap σ i j := by
    intro i j
    apply nonnegative_of_column_sum (fun i => overlap σ i j) _ (hcol j) i
    have hb := (column_budget σ ρ hd j).1
    have hcast : ((∑ i, (overlap σ i j).natAbs : Nat) : ℤ) ≤ 4 := by exact_mod_cast hb
    simpa only [Nat.cast_sum,Int.natCast_natAbs] using hcast
  have hrow := overlap_row_sums_four σ hcol
  have hzero : ∀ i, ∃ j, overlap σ i j = 0 := by
    intro i
    by_contra hn
    push Not at hn
    have hp : ∀ j, 1 ≤ overlap σ i j := fun j => by have := hnon i j; have := hn j; omega
    have hh := sum_le_sum (s := (univ : Finset (Fin 5))) (fun j _ => hp j)
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at hh
    rw [hrow] at hh
    norm_num at hh
  let T := (starSet σ).image σ
  have hT : T.card = 6 := by rw [card_image_of_injective _ σ.injective,hs]
  have hmem (u : Fin 16) (i : Fin 5)
      (he : |∑ j, row u j * overlap σ j i| = 4) : u ∈ T := by
    have hfour : |evaluation σ (σ.symm u) i| = 4 := by
      simpa only [evaluation,Equiv.apply_symm_apply] using he
    exact mem_image.mpr ⟨σ.symm u,star_of_four σ ρ hd _ i hfour,σ.apply_symm_apply u⟩
  have hbase : baseSix ⊆ T := by
    intro u hu
    rcases (baseSix_membership u).mp hu with rfl | ⟨i,rfl⟩
    · apply hmem 0 0
      rw [root_evaluation,hcol]
      decide
    · obtain ⟨j,hj⟩ := hzero i
      apply hmem (generators i) j
      rw [generator_evaluation,hj,hcol]
      decide
  have hz := energy_six_two_zeros (fun i => overlap σ i 0)
    (column_budget σ ρ hd 0).1 (six_star_column_energy σ ρ hd hs 0)
  obtain ⟨i,j,hij,hijset⟩ := card_eq_two.mp hz
  have hi : overlap σ i 0 = 0 := by
    have hm : i ∈ (univ.filter fun i => overlap σ i 0 = 0) := by rw [hijset]; simp
    exact (mem_filter.mp hm).2
  have hj : overlap σ j 0 = 0 := by
    have hm : j ∈ (univ.filter fun i => overlap σ i 0 = 0) := by rw [hijset]; simp
    exact (mem_filter.mp hm).2
  have hpair : pairVertex i j ∈ T := by
    apply hmem (pairVertex i j) 0
    rw [pair_evaluation _ i j hij,hcol,hi,hj]
    decide
  have hsubset : insert (pairVertex i j) baseSix ⊆ T := insert_subset hpair hbase
  have hbound := card_le_card hsubset
  rw [card_insert_of_notMem (pair_not_base i j hij),baseSix_card,hT] at hbound
  omega

#print axioms no_six_stars_canonical
end PricingG.SignDesign
