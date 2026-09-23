import PricingG.OrthogonalTripleBlocks

namespace PricingG
open Finset

def InducedDegreeTwo {V : Type*} [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (S : Finset V) : Prop :=
  ∀ x ∈ S, (S.filter fun y => K.Adj x y).card = 2

/-- The two orthogonal triple blocks cannot have all eight complements
induce pentagons: just their degree-two equations already contradict. -/
theorem no_two_four_blocks_of_degree_two {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (A B : Finset V)
    (hA : A.card = 4) (hB : B.card = 4) (hdis : Disjoint A B)
    (hleft : ∀ a ∈ A, InducedDegreeTwo K (insert a B))
    (hright : ∀ b ∈ B, InducedDegreeTwo K (insert b A)) : False := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < A.card by omega)
  have habsent : a ∉ B := fun hb => disjoint_left.mp hdis ha hb
  have hna : (B.filter fun y => K.Adj a y).card = 2 := by
    have h := hleft a ha a (mem_insert_self _ _)
    simpa [filter_insert, K.loopless.irrefl] using h
  obtain ⟨b,hb⟩ := card_pos.mp (show 0 < (B.filter fun y => K.Adj a y).card by omega)
  have hbB := (mem_filter.mp hb).1
  have hab := (mem_filter.mp hb).2
  have hba : K.Adj b a := (K.adj_comm a b).mp hab
  have hbin : b ∈ insert a B := mem_insert_of_mem hbB
  have hbase : (B.filter fun y => K.Adj b y).card = 1 := by
    have h := hleft a ha b hbin
    rw [filter_insert, if_pos hba, card_insert_of_notMem (fun hm => habsent (mem_filter.mp hm).1)] at h
    omega
  have hball : ∀ a' ∈ A, K.Adj b a' := by
    intro a' ha'
    have h := hleft a' ha' b (mem_insert_of_mem hbB)
    by_contra hnot
    rw [filter_insert, if_neg hnot, hbase] at h
    omega
  have hfull : (A.filter fun y => K.Adj b y) = A := filter_eq_self.mpr hball
  have h := hright b hbB b (mem_insert_self _ _)
  rw [filter_insert, if_neg (K.loopless.irrefl b), hfull, hA] at h
  omega

/-- The weight-three orthogonality configuration required by k=8 is
incompatible with pentagonal complement supports. No enumeration is used. -/
theorem no_eight_orthogonal_pentagon_complements
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (F : Finset (Finset (Fin 8))) (hF : F.card = 8)
    (hsize : ∀ S ∈ F, S.card = 3)
    (hcols : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Even (S ∩ T).card)
    (hrows : ∀ a b, a ≠ b → Even (F.filter fun S => a ∈ S ∧ b ∈ S).card)
    (hcycles : ∀ S ∈ F, InducedDegreeTwo K Sᶜ) : False := by
  obtain ⟨A,hA,hfamily⟩ := orthogonal_eight_triples_two_blocks F hF hsize hcols hrows
  apply no_two_four_blocks_of_degree_two K A Aᶜ hA
    (by simp [card_compl,hA]) disjoint_compl_right
  · intro a ha
    have hm : A.erase a ∈ F := by
      rw [hfamily]
      apply mem_union_left
      exact mem_powersetCard.mpr ⟨erase_subset _ _, by rw [card_erase_of_mem ha,hA]⟩
    simpa only [compl_erase] using hcycles (A.erase a) hm
  · intro b hb
    have hm : Aᶜ.erase b ∈ F := by
      rw [hfamily]
      apply mem_union_right
      exact mem_powersetCard.mpr ⟨erase_subset _ _, by simp [card_erase_of_mem hb,card_compl,hA]⟩
    simpa only [compl_erase,compl_compl] using hcycles (Aᶜ.erase b) hm

#print axioms no_eight_orthogonal_pentagon_complements
end PricingG
