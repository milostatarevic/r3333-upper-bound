import PricingG.ColumnBudget

namespace PricingG.SignDesign
open Finset PricingC

private theorem data_two_bound (e f : Nat) (h : (e,f) ∈ permittedColumnData) (hf : f ≤ 2) :
    2*f ≤ e := by
  simp only [permittedColumnData,mem_insert,mem_singleton,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h <;> omega

private theorem data_four_bound (e f : Nat) (h : (e,f) ∈ permittedColumnData) (hf : f ≤ 4) :
    2+f ≤ e := by
  simp only [permittedColumnData,mem_insert,mem_singleton,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h <;> omega

private theorem data_six_bound (e f : Nat) (h : (e,f) ∈ permittedColumnData) (hf : f ≤ 6) :
    e ≤ 6 := by
  simp only [permittedColumnData,mem_insert,mem_singleton,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h <;> omega

private theorem data_energy_six (e f : Nat) (h : (e,f) ∈ permittedColumnData) (he : e = 6) :
    f = 4 := by
  simp only [permittedColumnData,mem_insert,mem_singleton,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h <;> omega

/-- The complete signed-overlap constraints refute fourteen pentagonal rows. -/
theorem no_two_star_rows (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 2) : False := by
  have hnon : (starSet σ).Nonempty := card_pos.mp (by omega)
  have he := total_energy_eq_five_stars σ ρ hd
  have hf := total_fours_at_least_three_stars σ ρ hd
  have hpoint (i : Fin 5) : 2 * fourEvaluations (fun j => overlap σ j i) ≤
      squareNorm (fun j => overlap σ j i) := by
    exact data_two_bound _ _ (column_data_of_star σ ρ hd hnon i)
      (by simpa only [hs] using column_four_le_stars σ ρ hd i)
  have hsum := sum_le_sum (s := (univ : Finset (Fin 5))) (fun i _ => hpoint i)
  rw [← mul_sum] at hsum
  omega

/-- The complete signed-overlap constraints refute twelve pentagonal rows. -/
theorem no_four_star_rows (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 4) : False := by
  have hnon : (starSet σ).Nonempty := card_pos.mp (by omega)
  have he := total_energy_eq_five_stars σ ρ hd
  have hf := total_fours_at_least_three_stars σ ρ hd
  have hpoint (i : Fin 5) : 2 + fourEvaluations (fun j => overlap σ j i) ≤
      squareNorm (fun j => overlap σ j i) := by
    exact data_four_bound _ _ (column_data_of_star σ ρ hd hnon i)
      (by simpa only [hs] using column_four_le_stars σ ρ hd i)
  have hsum := sum_le_sum (s := (univ : Finset (Fin 5))) (fun i _ => hpoint i)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  omega

theorem six_star_column_energy (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 6) : ∀ i, squareNorm (fun j => overlap σ j i) = 6 := by
  have hnon : (starSet σ).Nonempty := card_pos.mp (by omega)
  have hpoint (i : Fin 5) : squareNorm (fun j => overlap σ j i) ≤ 6 := by
    exact data_six_bound _ _ (column_data_of_star σ ρ hd hnon i)
      (by simpa only [hs] using column_four_le_stars σ ρ hd i)
  have heq : (∑ i, squareNorm (fun j => overlap σ j i)) = ∑ _i : Fin 5, 6 := by
    rw [total_energy_eq_five_stars σ ρ hd,hs]
    decide
  intro i
  exact (sum_eq_sum_iff_of_le (fun i _ => hpoint i)).mp heq i (mem_univ i)

theorem six_star_column_fours (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 6) : ∀ i, fourEvaluations (fun j => overlap σ j i) = 4 := by
  intro i
  apply data_energy_six _ _ (column_data_of_star σ ρ hd (card_pos.mp (by omega)) i)
  exact six_star_column_energy σ ρ hd hs i

/-- The s=6 energy equality supplies an actual shared-neighborhood vertex,
which can be used for simultaneous rooting of both sign representations. -/
theorem six_stars_have_common_center (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).card = 6) :
    ∃ y ∈ starSet σ, (permutedGraph σ).neighborFinset y = xorGraph.neighborFinset y := by
  by_contra hn
  push Not at hn
  have hrow (y : Fin 16) : rowFourCount σ y = if y ∈ starSet σ then 3 else 0 := by
    by_cases hy : y ∈ starSet σ
    · obtain ⟨a,ha,he,hp,hfour⟩ := star_row_data σ ρ hd y hy
      have hne : y ≠ a := by intro heq; subst a; exact hn y hy ha
      rw [if_pos hy,hfour,if_neg hne]
    · rw [if_neg hy]
      exact (pentagon_row_data σ ρ hd y hy).2.2
  have htotal : (∑ i, fourEvaluations (fun j => overlap σ j i)) = 20 := by
    simp [six_star_column_fours σ ρ hd hs]
  rw [total_fours_eq_row] at htotal
  simp only [hrow] at htotal
  have hsum : (∑ y : Fin 16, if y ∈ starSet σ then 3 else 0) = 18 := by
    simp [← sum_filter,hs]
  omega

#print axioms no_two_star_rows
#print axioms no_four_star_rows
#print axioms six_stars_have_common_center
end PricingG.SignDesign
