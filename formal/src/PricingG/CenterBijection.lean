import Ramsey61.ClassificationAdapter

namespace PricingG
open Finset Matrix

/-- The Clebsch adjacency operator is nonsingular over the rationals. This
analytic fact converts five-fiber balance into uniqueness of every center. -/
theorem clebsch_adjacency_kernel_trivial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 16 5 0 2)
    (z : V → ℚ) (hz : G.adjMatrix ℚ *ᵥ z = 0) : z = 0 := by
  have hsum : (∑ i, (G.adjMatrix ℚ *ᵥ z) i) = 5 * ∑ i, z i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, G.adjMatrix ℚ i j * z j =
          ∑ j, (∑ i, G.adjMatrix ℚ i j) * z j := by simp only [sum_mul]
      _ = ∑ j, 5 * z j := by
        apply sum_congr rfl
        intro j hj
        congr 1
        have hrow := G.adjMatrix_mulVec_const_apply_of_regular (α := ℚ) (a := 1) (v := j) hG.regular
        simpa [Matrix.mulVec, dotProduct, G.adj_comm] using hrow
      _ = 5 * ∑ j, z j := by rw [mul_sum]
  have hsumz : ∑ i, z i = 0 := by
    rw [hz] at hsum
    simp only [Pi.zero_apply, sum_const_zero] at hsum
    linarith
  have hcomp : Gᶜ.adjMatrix ℚ *ᵥ z = -z := by
    have h := congrArg (fun M : Matrix V V ℚ => M *ᵥ z)
      (G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℚ))
    rw [G.compl_adjMatrix_eq_adjMatrix_compl ℚ] at h
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, hz] at h
    have hj : (Matrix.of (1 : V → V → ℚ)) *ᵥ z = 0 := by
      ext i
      simpa [Matrix.mulVec, dotProduct] using hsumz
    rw [hj] at h
    ext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hi ⊢
    linarith
  have hs := congrArg (fun M : Matrix V V ℚ => M *ᵥ z) (hG.matrix_eq (α := ℚ))
  simp only [pow_two, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    zero_smul, add_zero, hcomp] at hs
  ext i
  have hi := congrFun hs i
  simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply] at hi ⊢
  norm_num at hi
  linarith

/-- Equality of Clebsch neighbor sums determines every rational weight. -/
theorem clebsch_adjacency_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 16 5 0 2) :
    Function.Injective (fun z : V → ℚ => G.adjMatrix ℚ *ᵥ z) := by
  intro z w h
  change G.adjMatrix ℚ *ᵥ z = G.adjMatrix ℚ *ᵥ w at h
  apply sub_eq_zero.mp
  apply clebsch_adjacency_kernel_trivial G hG
  rw [Matrix.mulVec_sub, h, sub_self]

/-- A map into Clebsch centers with five incidences in each opposite column
has every center once. This is the actual multiplicity-elimination step in G. -/
theorem centerMap_bijective_of_balanced_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 16 5 0 2)
    (f : V → V)
    (hbalance : ∀ y, (univ.filter fun x => G.Adj (f x) y).card = 5) :
    Function.Bijective f := by
  let n : V → ℚ := fun y => ((univ.filter fun x => f x = y).card : ℚ)
  have hn : G.adjMatrix ℚ *ᵥ n = G.adjMatrix ℚ *ᵥ (fun _ => 1) := by
    ext y
    change (G.adjMatrix ℚ *ᵥ n) y = (G.adjMatrix ℚ *ᵥ Function.const V 1) y
    rw [G.adjMatrix_mulVec_const_apply_of_regular (α := ℚ) (a := 1) hG.regular]
    rw [G.adjMatrix_mulVec_apply]
    have heq : ∑ v ∈ G.neighborFinset y, (univ.filter fun x => f x = v).card =
        (univ.filter fun x => G.Adj (f x) y).card := by
      let S := univ.filter fun x => G.Adj (f x) y
      have hf : ∀ x ∈ S, f x ∈ G.neighborFinset y := by
        intro x hx
        exact (G.mem_neighborFinset y (f x)).mpr ((G.adj_comm (f x) y).mp (mem_filter.mp hx).2)
      have hh := card_eq_sum_card_fiberwise hf
      have hh' : ∀ v ∈ G.neighborFinset y,
          (S.filter fun x => f x = v) = (univ.filter fun x => f x = v) := by
        intro v hv
        ext x
        simp only [S, mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨h ▸ (G.adj_comm y v).mp ((G.mem_neighborFinset y v).mp hv), h⟩
      rw [hh]
      apply sum_congr rfl
      intro v hv
      rw [hh' v hv]
    rw [hbalance] at heq
    simpa only [n, Nat.cast_sum, Nat.cast_ofNat, mul_one] using congrArg (fun k : Nat => (k : ℚ)) heq
  have hn1 := clebsch_adjacency_injective G hG hn
  have hcard : ∀ y, (univ.filter fun x => f x = y).card = 1 := by
    intro y
    have h := congrFun hn1 y
    change ((univ.filter fun x => f x = y).card : ℚ) = 1 at h
    exact_mod_cast h
  have hinj : Function.Injective f := by
    intro x z hxz
    obtain ⟨a, ha⟩ := card_eq_one.mp (hcard (f x))
    have hx : x ∈ univ.filter fun t => f t = f x := by simp
    have hz : z ∈ univ.filter fun t => f t = f x := by simp [hxz]
    rw [ha] at hx hz
    exact (mem_singleton.mp hx).trans (mem_singleton.mp hz).symm
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

#print axioms clebsch_adjacency_kernel_trivial
#print axioms centerMap_bijective_of_balanced_neighbors
end PricingG
