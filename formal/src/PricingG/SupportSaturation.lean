import PricingG.CenterBijection

namespace PricingG
open Finset

/-- In a Clebsch graph, the exact two-or-five masks force at least five
vertices on the opposite side. This is the double count before saturation. -/
theorem five_le_of_two_or_five_masks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 16 5 0 2)
    (v : V) (A : Finset V)
    (havoid : Disjoint A (G.neighborFinset v))
    (hmasks : ∀ x ∈ G.neighborFinset v,
      (A.filter fun a => G.Adj x a).card = 2 ∨
      (A.filter fun a => G.Adj x a).card = 5) :
    5 ≤ A.card := by
  let Q := G.neighborFinset v
  let full := Q.filter fun x => (A.filter fun a => G.Adj x a).card = 5
  have hQ : Q.card = 5 := by
    simpa [Q, SimpleGraph.card_neighborFinset_eq_degree] using hG.regular v
  have hleft : (∑ x ∈ Q, (A.filter fun a => G.Adj x a).card) = 10 + 3 * full.card := by
    have hterm : ∀ x ∈ Q, (A.filter fun a => G.Adj x a).card =
        2 + if (A.filter fun a => G.Adj x a).card = 5 then 3 else 0 := by
      intro x hx
      rcases hmasks x hx with h | h <;> simp [h]
    calc
      _ = ∑ x ∈ Q, (2 + if (A.filter fun a => G.Adj x a).card = 5 then 3 else 0) :=
        sum_congr rfl hterm
      _ = 10 + 3 * full.card := by
        rw [sum_add_distrib]
        simp [hQ, full, ← sum_filter, Nat.mul_comm]
  have hcommon : ∀ a ∈ A, (Q.filter fun x => G.Adj x a).card = if a = v then 5 else 2 := by
    intro a ha
    by_cases hav : a = v
    · subst a
      have heq : (Q.filter fun x => G.Adj x v) = Q := by
        apply filter_eq_self.mpr
        intro x hx
        exact (G.adj_comm v x).mp ((G.mem_neighborFinset v x).mp hx)
      simp [heq, hQ]
    · have hnot : ¬G.Adj v a := by
        intro h
        exact disjoint_left.mp havoid ha ((G.mem_neighborFinset v a).mpr h)
      have heq : (Q.filter fun x => G.Adj x a) = G.neighborFinset v ∩ G.neighborFinset a := by
        ext x
        simp only [Q, mem_filter, mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_congr_right fun _ => G.adj_comm x a
      rw [heq]
      have hh := hG.of_not_adj (Ne.symm hav) hnot
      have hc : (G.neighborFinset v ∩ G.neighborFinset a).card = 2 := by
        simpa only [SimpleGraph.commonNeighbors, ← Set.toFinset_card,
          Set.toFinset_inter, ← SimpleGraph.neighborFinset_def] using hh
      simp [hav, hc]
  have hright : (∑ a ∈ A, (Q.filter fun x => G.Adj x a).card) =
      2 * A.card + if v ∈ A then 3 else 0 := by
    calc
      _ = ∑ a ∈ A, (2 + if a = v then 3 else 0) := by
        apply sum_congr rfl
        intro a ha
        rw [hcommon a ha]
        split <;> simp_all
      _ = 2 * A.card + if v ∈ A then 3 else 0 := by
        rw [sum_add_distrib]
        simp [sum_ite_eq', Nat.mul_comm]
  have hdouble : (∑ x ∈ Q, (A.filter fun a => G.Adj x a).card) =
      ∑ a ∈ A, (Q.filter fun x => G.Adj x a).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
  rw [hleft, hright] at hdouble
  split_ifs at hdouble <;> omega

/-- Exact row and column saturation for a finite incidence relation. -/
theorem relation_saturates {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → V → Prop) [DecidableRel N]
    (hrow : ∀ x, (univ.filter fun y => N x y).card ≤ 5)
    (hcol : ∀ y, 5 ≤ (univ.filter fun x => N x y).card) :
    (∀ x, (univ.filter fun y => N x y).card = 5) ∧
    (∀ y, (univ.filter fun x => N x y).card = 5) := by
  have hd : (∑ x, (univ.filter fun y => N x y).card) =
      ∑ y, (univ.filter fun x => N x y).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow N
  have hu : (∑ x, (univ.filter fun y => N x y).card) ≤ ∑ _x : V, 5 :=
    sum_le_sum fun x _ => hrow x
  have hl : (∑ _y : V, 5) ≤ ∑ y, (univ.filter fun x => N x y).card :=
    sum_le_sum fun y _ => hcol y
  have heq : (∑ x, (univ.filter fun y => N x y).card) = ∑ _x : V, 5 := by omega
  constructor
  · intro x
    exact (sum_eq_sum_iff_of_le (fun x _ => hrow x)).mp heq x (mem_univ x)
  · intro y
    have heq' : (∑ _y : V, 5) = ∑ y, (univ.filter fun x => N x y).card := by omega
    exact ((sum_eq_sum_iff_of_le (fun y _ => hcol y)).mp heq' y (mem_univ y)).symm

/-- Both actual fiber-center maps are bijections once their disjoint physical
incidences obey the critical two-or-five masks. No injectivity is assumed. -/
theorem centerMaps_bijective {V : Type*} [Fintype V] [DecidableEq V]
    (K L : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel L.Adj]
    (hK : K.IsSRGWith 16 5 0 2) (hL : L.IsSRGWith 16 5 0 2)
    (f g : V → V)
    (hdisjoint : ∀ x y, ¬(K.Adj (f y) x ∧ L.Adj (g x) y))
    (hmaskK : ∀ y x, K.Adj (f y) x →
      (univ.filter fun a => L.Adj (g a) y ∧ K.Adj x a).card = 2 ∨
      (univ.filter fun a => L.Adj (g a) y ∧ K.Adj x a).card = 5)
    (hmaskL : ∀ x y, L.Adj (g x) y →
      (univ.filter fun b => K.Adj (f b) x ∧ L.Adj y b).card = 2 ∨
      (univ.filter fun b => K.Adj (f b) x ∧ L.Adj y b).card = 5) :
    Function.Bijective f ∧ Function.Bijective g := by
  have hgcol : ∀ y, 5 ≤ (univ.filter fun x => L.Adj (g x) y).card := by
    intro y
    apply five_le_of_two_or_five_masks K hK (f y)
    · apply disjoint_left.mpr
      intro x hx hq
      exact hdisjoint x y ⟨(K.mem_neighborFinset _ _).mp hq, (mem_filter.mp hx).2⟩
    · intro x hx
      simpa only [filter_filter] using hmaskK y x ((K.mem_neighborFinset _ _).mp hx)
  have hfcol : ∀ x, 5 ≤ (univ.filter fun y => K.Adj (f y) x).card := by
    intro x
    apply five_le_of_two_or_five_masks L hL (g x)
    · apply disjoint_left.mpr
      intro y hy hq
      exact hdisjoint x y ⟨(mem_filter.mp hy).2, (L.mem_neighborFinset _ _).mp hq⟩
    · intro y hy
      simpa only [filter_filter] using hmaskL x y ((L.mem_neighborFinset _ _).mp hy)
  have hgrow : ∀ x, (univ.filter fun y => L.Adj (g x) y).card ≤ 5 := by
    intro x
    have heq : (univ.filter fun y => L.Adj (g x) y) = L.neighborFinset (g x) := by
      ext y; simp
    rw [heq, SimpleGraph.card_neighborFinset_eq_degree, hL.regular]
  have hfrow : ∀ y, (univ.filter fun x => K.Adj (f y) x).card ≤ 5 := by
    intro y
    have heq : (univ.filter fun x => K.Adj (f y) x) = K.neighborFinset (f y) := by
      ext x; simp
    rw [heq, SimpleGraph.card_neighborFinset_eq_degree, hK.regular]
  exact ⟨centerMap_bijective_of_balanced_neighbors K hK f
      ((relation_saturates (fun y x => K.Adj (f y) x) hfrow hfcol).2),
    centerMap_bijective_of_balanced_neighbors L hL g
      ((relation_saturates (fun x y => L.Adj (g x) y) hgrow hgcol).2)⟩

#print axioms five_le_of_two_or_five_masks
#print axioms centerMaps_bijective
end PricingG
