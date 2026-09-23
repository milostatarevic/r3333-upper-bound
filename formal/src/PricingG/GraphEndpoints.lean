import PricingG.GeneralMixedCases

namespace PricingG
open Finset Matrix

theorem trace_common_neighbors (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] :
    Matrix.trace (K.adjMatrix ℤ * J.adjMatrix ℤ) =
      ∑ y, ((K.neighborFinset y ∩ J.neighborFinset y).card : ℤ) := by
  unfold Matrix.trace Matrix.diag
  apply sum_congr rfl
  intro y hy
  rw [K.adjMatrix_mul_apply]
  have hs : (K.neighborFinset y).filter (fun x => J.Adj y x) =
      K.neighborFinset y ∩ J.neighborFinset y := by ext x; simp
  simpa [SimpleGraph.adjMatrix_apply,J.adj_comm,← sum_filter] using congrArg (fun s => (s.card : ℤ)) hs

theorem trace_nonnegative (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] :
    0 ≤ Matrix.trace (K.adjMatrix ℤ * J.adjMatrix ℤ) := by
  rw [trace_common_neighbors]
  positivity

theorem GraphRootedDichotomy.unrooted {K J : SimpleGraph (Fin 16)}
    [DecidableRel K.Adj] [DecidableRel J.Adj] {ρ : Equiv.Perm (Fin 16)}
    (hd : GraphRootedDichotomy K J ρ) (y : Fin 16) :
    (∃ a, J.neighborFinset y = K.neighborFinset a) ∨ InducedDegreeTwo K (J.neighborFinset y) := by
  rcases hd y with ⟨a,_,ha⟩ | hp
  · exact Or.inl ⟨a,ha⟩
  · exact Or.inr hp.1

/-- At the zero-defect endpoint all 80 directed incidences agree. -/
theorem zero_defects_graph_eq (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (hd : ∀ y, (∃ a, J.neighborFinset y = K.neighborFinset a) ∨
      InducedDegreeTwo K (J.neighborFinset y))
    (hz : defectCount K J = 0) : K = J := by
  have hc := common_edges_and_defects K J hK hJ hd
  rw [hz,trace_common_neighbors] at hc
  have hcardK (y : Fin 16) : (K.neighborFinset y).card = 5 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hK.regular y
  have hcardJ (y : Fin 16) : (J.neighborFinset y).card = 5 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hJ.regular y
  have hle (y : Fin 16) : (K.neighborFinset y ∩ J.neighborFinset y).card ≤ 5 := by
    rw [← hcardK y]; exact card_le_card inter_subset_left
  have heq (y : Fin 16) : (K.neighborFinset y ∩ J.neighborFinset y).card = 5 := by
    have hsum : (∑ x : Fin 16, (5 - ((K.neighborFinset x ∩ J.neighborFinset x).card : ℤ))) = 0 := by
      rw [sum_sub_distrib]
      norm_num at hc ⊢
      omega
    have hn (x : Fin 16) (_ : x ∈ (univ : Finset (Fin 16))) :
        (0 : ℤ) ≤ 5 - (K.neighborFinset x ∩ J.neighborFinset x).card := by
      exact sub_nonneg.mpr (by exact_mod_cast hle x)
    have h := (sum_eq_zero_iff_of_nonneg hn).mp hsum y (mem_univ y)
    omega
  have hN (y : Fin 16) : K.neighborFinset y = J.neighborFinset y := by
    have hk : K.neighborFinset y ∩ J.neighborFinset y = K.neighborFinset y :=
      eq_of_subset_of_card_le inter_subset_left (by rw [heq,hcardK])
    have hj : K.neighborFinset y ∩ J.neighborFinset y = J.neighborFinset y :=
      eq_of_subset_of_card_le inter_subset_right (by rw [heq,hcardJ])
    exact hk.symm.trans hj
  ext x y
  simpa only [SimpleGraph.mem_neighborFinset] using Iff.of_eq (congrArg (fun s => y ∈ s) (hN x))

/-- At the full-defect endpoint the two graphs have no edge in common. -/
theorem full_defects_disjoint (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (hd : ∀ y, (∃ a, J.neighborFinset y = K.neighborFinset a) ∨
      InducedDegreeTwo K (J.neighborFinset y))
    (hz : defectCount K J = 16) : ∀ x y, ¬(K.Adj x y ∧ J.Adj x y) := by
  have hc := common_edges_and_defects K J hK hJ hd
  rw [hz,trace_common_neighbors] at hc
  have hsum : (∑ x : Fin 16, ((K.neighborFinset x ∩ J.neighborFinset x).card : ℤ)) = 0 := by
    norm_num at hc; exact hc
  have hzero (x : Fin 16) : (K.neighborFinset x ∩ J.neighborFinset x).card = 0 := by
    have h := (sum_eq_zero_iff_of_nonneg (fun y _ => (Nat.cast_nonneg _ :
      (0 : ℤ) ≤ (K.neighborFinset y ∩ J.neighborFinset y).card))).mp hsum x (mem_univ x)
    exact_mod_cast h
  intro x y ⟨hk,hj⟩
  have hm : y ∈ K.neighborFinset x ∩ J.neighborFinset x := mem_inter.mpr
    ⟨(K.mem_neighborFinset _ _).mpr hk,(J.mem_neighborFinset _ _).mpr hj⟩
  rw [card_eq_zero.mp (hzero x)] at hm
  exact notMem_empty _ hm

theorem full_defects_all_pentagons (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj] (hz : defectCount K J = 16) :
    ∀ y, InducedDegreeTwo K (J.neighborFinset y) := by
  classical
  have heq : univ.filter (fun y => InducedDegreeTwo K (J.neighborFinset y)) = univ :=
    eq_of_subset_of_card_le (filter_subset _ _) (by simpa [defectCount] using hz.ge)
  intro y
  have hy : y ∈ univ.filter (fun y => InducedDegreeTwo K (J.neighborFinset y)) := by rw [heq]; exact mem_univ y
  exact (mem_filter.mp hy).2

/-- Disjointness forces the rooted zero of each pentagon to be its own row
label, so the physical center composition is exactly the identity. -/
theorem full_defects_image_identity (K J : SimpleGraph (Fin 16))
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hJ : J.IsSRGWith 16 5 0 2)
    (ρ : Equiv.Perm (Fin 16)) (hd : GraphRootedDichotomy K J ρ)
    (hz : defectCount K J = 16) : ∀ y, ρ y = y := by
  have hdis := full_defects_disjoint K J hK hJ hd.unrooted hz
  have hpent := full_defects_all_pentagons K J hz
  intro y
  have hlaw : RootPentagonLaw K (ρ y) (J.neighborFinset y) := by
    rcases hd y with ⟨a,_,ha⟩ | hp
    · obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (J.neighborFinset y).card by
        rw [SimpleGraph.card_neighborFinset_eq_degree,hJ.regular y]; decide)
      have he := hpent y x hx
      rw [ha] at hx he
      rw [star_filter_card_zero K hK a x hx] at he
      omega
    · exact hp.2
  have hzrow : ((J.neighborFinset y).filter fun z => K.Adj y z).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hdis y z ⟨(mem_filter.mp hz).2,(J.mem_neighborFinset _ _).mp (mem_filter.mp hz).1⟩
  have he := hlaw y
  rw [hzrow] at he
  by_contra hn
  simp only [if_neg (Ne.symm hn)] at he
  split_ifs at he <;> omega

#print axioms zero_defects_graph_eq
#print axioms full_defects_disjoint
#print axioms full_defects_image_identity
end PricingG
