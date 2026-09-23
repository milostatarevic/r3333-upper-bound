import PricingG.SignEvaluations

namespace PricingG.SignDesign
open Finset Matrix PricingC

/-- Exact local conclusions supplied by the physical shared-graph reduction. -/
def RootedDichotomy (σ ρ : Equiv.Perm (Fin 16)) : Prop := ∀ y,
  (∃ a, xorGraph.Adj (ρ y) a ∧ (permutedGraph σ).neighborFinset y = xorGraph.neighborFinset a) ∨
  (InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset y) ∧
    RootPentagonLaw xorGraph (ρ y) ((permutedGraph σ).neighborFinset y))

def starSet (σ : Equiv.Perm (Fin 16)) : Finset (Fin 16) :=
  univ.filter fun y => ¬InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset y)

def evaluation (σ : Equiv.Perm (Fin 16)) (y : Fin 16) (i : Fin 5) : ℤ :=
  ∑ j, row (σ y) j * overlap σ j i

def rowFourCount (σ : Equiv.Perm (Fin 16)) (y : Fin 16) : Nat :=
  (univ.filter fun i => |evaluation σ y i| = 4).card

theorem starSet_add_defects (σ : Equiv.Perm (Fin 16)) :
    (starSet σ).card + defectCount xorGraph (permutedGraph σ) = 16 := by
  have h := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin 16)))
    (p := fun y => InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset y))
  simpa only [card_univ,Fintype.card_fin,starSet,defectCount,add_comm] using h

theorem star_row_data (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (y : Fin 16) (hy : y ∈ starSet σ) :
    ∃ a, (permutedGraph σ).neighborFinset y = xorGraph.neighborFinset a ∧
      (∀ i, evaluation σ y i = row y i + 3 * row a i) ∧
      (∀ i, evaluation σ y i ≠ 0 ∧ Even (evaluation σ y i) ∧ |evaluation σ y i| ≤ 4) ∧
      rowFourCount σ y = if y = a then 5 else 3 := by
  have hn := (mem_filter.mp hy).2
  obtain ⟨a,hpa,ha⟩ := (hd y).resolve_right (fun h => hn h.1)
  have hnot : ¬xorGraph.Adj y a := by
    intro h
    have hyA : y ∈ xorGraph.neighborFinset a :=
      (xorGraph.mem_neighborFinset _ _).mpr ((xorGraph.adj_comm y a).mp h)
    rw [← ha] at hyA
    exact (permutedGraph σ).notMem_neighborFinset_self y hyA
  have he (i : Fin 5) : evaluation σ y i = row y i + 3 * row a i := by
    rw [evaluation,overlap_evaluation,ha,neighborhood_centroid]
    ring
  have hp := star_row_evaluation_properties y a hnot
  refine ⟨a,ha,he,?_,?_⟩
  · intro i
    rw [he]
    exact hp.1 i
  · simp only [rowFourCount,he]
    exact hp.2

theorem pentagon_row_data (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (y : Fin 16) (hy : y ∉ starSet σ) :
    (∀ i, evaluation σ y i = row y i - row (ρ y) i) ∧
    (∀ i, Even (evaluation σ y i) ∧ |evaluation σ y i| ≤ 2) ∧ rowFourCount σ y = 0 := by
  have hp : InducedDegreeTwo xorGraph ((permutedGraph σ).neighborFinset y) := by
    simpa only [starSet,mem_filter,mem_univ,true_and,not_not] using hy
  have hlaw : RootPentagonLaw xorGraph (ρ y) ((permutedGraph σ).neighborFinset y) := by
    rcases hd y with hs | hs
    · obtain ⟨a,_,ha⟩ := hs
      have hcard : (xorGraph.neighborFinset a).card = 5 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact xorGraph_srg.regular a
      obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (xorGraph.neighborFinset a).card by omega)
      rw [ha] at hp
      have he := hp x hx
      rw [star_filter_card_zero xorGraph xorGraph_srg a x hx] at he
      omega
    · exact hs.2
  have hA : ((permutedGraph σ).neighborFinset y).card = 5 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact (permutedGraph_srg σ).regular y
  have havoid : Disjoint ((permutedGraph σ).neighborFinset y) (xorGraph.neighborFinset (ρ y)) := by
    have he := hlaw (ρ y)
    simp only [if_pos rfl] at he
    apply disjoint_left.mpr
    intro x hx hx'
    have hm : x ∈ ((permutedGraph σ).neighborFinset y).filter fun a => xorGraph.Adj (ρ y) a :=
      mem_filter.mpr ⟨hx,(xorGraph.mem_neighborFinset _ _).mp hx'⟩
    rw [card_eq_zero.mp he] at hm
    exact notMem_empty _ hm
  have he (i : Fin 5) : evaluation σ y i = row y i - row (ρ y) i := by
    rw [evaluation,overlap_evaluation,pentagon_centroid (ρ y) _ hA havoid hlaw]
  have hb (i : Fin 5) : Even (evaluation σ y i) ∧ |evaluation σ y i| ≤ 2 := by
    rw [he]
    exact pentagon_row_evaluation_properties y (ρ y) i
  refine ⟨he,hb,?_⟩
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h4 := (mem_filter.mp hi).2
  have h2 := (hb i).2
  omega

theorem evaluations_even_bounded (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ) :
    ∀ y i, Even (evaluation σ y i) ∧ |evaluation σ y i| ≤ 4 := by
  intro y i
  by_cases hy : y ∈ starSet σ
  · obtain ⟨a,ha,he,hp,hc⟩ := star_row_data σ ρ hd y hy
    exact (hp i).2
  · have h := (pentagon_row_data σ ρ hd y hy).2.1 i
    exact ⟨h.1,by omega⟩

theorem star_rows_at_least_three_fours (σ ρ : Equiv.Perm (Fin 16)) (hd : RootedDichotomy σ ρ)
    (y : Fin 16) (hy : y ∈ starSet σ) : 3 ≤ rowFourCount σ y := by
  obtain ⟨a,ha,he,hp,hc⟩ := star_row_data σ ρ hd y hy
  split_ifs at hc <;> omega

#print axioms evaluations_even_bounded
#print axioms star_rows_at_least_three_fours
end PricingG.SignDesign
