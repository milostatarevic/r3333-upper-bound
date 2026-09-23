import PricingG.SignedDichotomy

namespace PricingG.SignDesign
open Finset Matrix PricingC

private theorem column_abs_sum_even (b : Fin 5 → ℤ)
    (he : ∀ u, Even (∑ i, row u i * b i)) : Even (∑ i, (b i).natAbs) := by
  let s : Fin 5 → Bool := fun i => decide (0 ≤ b i)
  have hterm (i : Fin 5) : (if s i then 1 else -1 : ℤ) * b i = |b i| := by
    by_cases hb : 0 ≤ b i
    · simp [s,hb,abs_of_nonneg hb]
    · simp [s,hb,abs_of_neg (by omega : b i < 0)]
  have hEven : Even (∑ i, |b i|) := by
    obtain ⟨u,hu|hu⟩ := every_sign_up_to_negation s
    · have h := he u
      simpa only [hu,hterm] using h
    · have h := he u
      simpa only [hu,neg_mul,hterm,sum_neg_distrib,even_neg] using h
  have hcast : Even ((∑ i, (b i).natAbs : Nat) : ℤ) := by
    simpa only [Nat.cast_sum,Int.natCast_natAbs] using hEven
  exact_mod_cast hcast

theorem column_budget (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (i : Fin 5) : (∑ j, (overlap σ j i).natAbs ≤ 4) ∧ Even (∑ j, (overlap σ j i).natAbs) := by
  have he (u : Fin 16) : Even (∑ j, row u j * overlap σ j i) ∧
      |∑ j, row u j * overlap σ j i| ≤ 4 := by
    simpa only [evaluation,Equiv.apply_symm_apply] using
      evaluations_even_bounded σ ρ hd (σ.symm u) i
  have hbound := column_l1_bound (fun j => overlap σ j i) (fun u => (he u).2)
  have hcast : ((∑ j, (overlap σ j i).natAbs : Nat) : ℤ) ≤ 4 := by
    simpa only [Nat.cast_sum,Int.natCast_natAbs] using hbound
  exact ⟨by exact_mod_cast hcast,column_abs_sum_even _ (fun u => (he u).1)⟩

theorem column_nonzero_of_star (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).Nonempty) (i : Fin 5) : (fun j => overlap σ j i) ≠ 0 := by
  obtain ⟨y,hy⟩ := hs
  obtain ⟨a,ha,he,hp,hc⟩ := star_row_data σ ρ hd y hy
  intro hz
  have hzero : evaluation σ y i = 0 := by
    unfold evaluation
    simp only [show ∀ j, overlap σ j i = 0 from fun j => congrFun hz j,mul_zero,sum_const_zero]
  exact (hp i).1 hzero

theorem column_data_of_star (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (hs : (starSet σ).Nonempty) (i : Fin 5) :
    columnData (fun j => overlap σ j i) ∈ permittedColumnData :=
  column_data_exhaustive _ (column_budget σ ρ hd i).1 (column_budget σ ρ hd i).2
    (column_nonzero_of_star σ ρ hd hs i)

private theorem equiv_filter_card {V : Type*} [Fintype V] [DecidableEq V]
    (e : Equiv.Perm V) (P : V → Prop) [DecidablePred P] :
    (univ.filter fun x => P (e x)).card = (univ.filter P).card := by
  have heq : (univ.filter fun x => P (e x)).image e = univ.filter P := by
    ext y
    simp only [mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨x,h,rfl⟩; exact h
    · intro h; exact ⟨e.symm y,by simpa using h,e.apply_symm_apply y⟩
  rw [← heq,card_image_of_injective _ e.injective]

theorem column_four_count (σ : Equiv.Perm (Fin 16)) (i : Fin 5) :
    fourEvaluations (fun j => overlap σ j i) =
      (univ.filter fun y => |evaluation σ y i| = 4).card := by
  exact (equiv_filter_card σ (fun u => |∑ j, row u j * overlap σ j i| = 4)).symm

theorem column_four_le_stars (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (i : Fin 5) : fourEvaluations (fun j => overlap σ j i) ≤ (starSet σ).card := by
  rw [column_four_count]
  apply card_le_card
  intro y hy
  by_contra hnot
  have h2 := (pentagon_row_data σ ρ hd y hnot).2.1 i
  have h4 := (mem_filter.mp hy).2
  omega

theorem total_fours_eq_row (σ : Equiv.Perm (Fin 16)) :
    (∑ i, fourEvaluations (fun j => overlap σ j i)) = ∑ y, rowFourCount σ y := by
  simp_rw [column_four_count]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun i y => |evaluation σ y i| = 4)

theorem total_fours_at_least_three_stars (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ) :
    3 * (starSet σ).card ≤ ∑ i, fourEvaluations (fun j => overlap σ j i) := by
  have heq : (∑ i, fourEvaluations (fun j => overlap σ j i)) = ∑ y, rowFourCount σ y := by
    simp_rw [column_four_count]
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun i y => |evaluation σ y i| = 4)
  rw [heq]
  calc
    3 * (starSet σ).card = ∑ y : Fin 16, if y ∈ starSet σ then 3 else 0 := by
      simp [← sum_filter,mul_comm]
    _ ≤ ∑ y, rowFourCount σ y := by
      apply sum_le_sum
      intro y hy
      by_cases hs : y ∈ starSet σ
      · rw [if_pos hs]
        exact star_rows_at_least_three_fours σ ρ hd y hs
      · rw [if_neg hs]
        omega

theorem total_energy_eq_five_stars (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ) :
    (∑ i, squareNorm (fun j => overlap σ j i)) = 5 * (starSet σ).card := by
  have hcast : ((∑ i, squareNorm (fun j => overlap σ j i) : Nat) : ℤ) =
      Matrix.trace ((overlapMatrix σ)ᵀ * overlapMatrix σ) := by
    simp only [squareNorm,Nat.cast_sum,Nat.cast_pow,Int.natCast_natAbs,sq_abs,
      Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,overlapMatrix,Matrix.of_apply]
    simp only [pow_two]
  rw [overlap_frobenius] at hcast
  have hc := common_edges_and_defects xorGraph (permutedGraph σ) xorGraph_srg (permutedGraph_srg σ)
    (fun y => (hd y).imp (fun ⟨a,_,h⟩ => ⟨a,h⟩) And.left)
  rw [permutedGraph_matrix] at hc
  have hs := starSet_add_defects σ
  change ((∑ i, squareNorm (fun j => overlap σ j i) : Nat) : ℤ) =
    Matrix.trace (xorGraph.adjMatrix ℤ * permAdj σ) at hcast
  omega

#print axioms total_energy_eq_five_stars
#print axioms total_fours_at_least_three_stars
#print axioms column_data_of_star
end PricingG.SignDesign
