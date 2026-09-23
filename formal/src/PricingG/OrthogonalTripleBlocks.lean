import PricingG.OrthogonalTriples

namespace PricingG
open Finset

/-- A complete four-point triple block cannot intersect any other orthogonal
triple. This is a set-theoretic parity argument, not a finite enumeration. -/
theorem four_triple_block_isolated {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (hsize : ∀ S ∈ F, S.card = 3)
    (hcols : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Even (S ∩ T).card)
    (A : Finset V) (hA : A.card = 4)
    (hblock : ∀ a ∈ A, A.erase a ∈ F)
    (T : Finset V) (hT : T ∈ F) : T ⊆ A ∨ Disjoint T A := by
  by_cases hsub : T ⊆ A
  · exact Or.inl hsub
  right
  apply disjoint_left.mpr
  intro x hxT hxA
  have hy : ∃ y ∈ A, y ∉ T := by
    by_contra h
    push Not at h
    have hc := card_le_card h
    rw [hA, hsize T hT] at hc
    omega
  obtain ⟨y,hyA,hyT⟩ := hy
  have hne (a : V) : T ≠ A.erase a := by
    intro heq
    exact hsub (heq ▸ erase_subset a A)
  have hpx := hcols T hT (A.erase x) (hblock x hxA) (hne x)
  have hpy := hcols T hT (A.erase y) (hblock y hyA) (hne y)
  rw [inter_erase, card_erase_of_mem (mem_inter.mpr ⟨hxT,hxA⟩)] at hpx
  rw [inter_erase, erase_eq_of_notMem (fun h => hyT (mem_inter.mp h).1)] at hpy
  have hpos : 0 < (T ∩ A).card := card_pos.mpr ⟨x,mem_inter.mpr ⟨hxT,hxA⟩⟩
  obtain ⟨m,hm⟩ := hpx
  obtain ⟨n,hn⟩ := hpy
  omega

/-- Every nonempty orthogonal triple family supplies an isolated four-point
block containing all four of its triples. -/
theorem orthogonal_triples_has_block {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hsize : ∀ S ∈ F, S.card = 3)
    (hcols : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Even (S ∩ T).card)
    (hrows : ∀ a b, a ≠ b → Even (F.filter fun S => a ∈ S ∧ b ∈ S).card) :
    ∃ A : Finset V, A.card = 4 ∧ (∀ a ∈ A, A.erase a ∈ F) ∧
      ∀ T ∈ F, T ⊆ A ∨ Disjoint T A := by
  obtain ⟨S,hS⟩ := hne
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl,hT,hU,hV⟩ :=
    orthogonal_triples_contains_four_block F hsize hcols hrows S hS
  let A : Finset V := {a,b,c,d}
  have hA : A.card = 4 := by simp [A,hab,hac,had,hbc,hbd,hcd]
  have hblock : ∀ x ∈ A, A.erase x ∈ F := by
    intro x hx
    simp only [A, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [A,hab,hac,had,hbc,hbd,hcd,eq_comm,erase_insert_of_ne,erase_insert_eq_erase] using hV
    · simpa [A,hab,hac,had,hbc,hbd,hcd,eq_comm,erase_insert_of_ne,erase_insert_eq_erase] using hU
    · simpa [A,hab,hac,had,hbc,hbd,hcd,eq_comm,erase_insert_of_ne,erase_insert_eq_erase] using hT
    · simpa [A,hab,hac,had,hbc,hbd,hcd,eq_comm,erase_insert_of_ne,erase_insert_eq_erase] using hS
  exact ⟨A,hA,hblock,fun T hT => four_triple_block_isolated F hsize hcols A hA hblock T hT⟩

/-- Exact two-four-block classification of an eight-by-eight orthogonal
weight-three incidence matrix, stated as its distinct column supports. -/
theorem orthogonal_eight_triples_two_blocks
    (F : Finset (Finset (Fin 8))) (hF : F.card = 8)
    (hsize : ∀ S ∈ F, S.card = 3)
    (hcols : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Even (S ∩ T).card)
    (hrows : ∀ a b, a ≠ b → Even (F.filter fun S => a ∈ S ∧ b ∈ S).card) :
    ∃ A : Finset (Fin 8), A.card = 4 ∧
      F = A.powersetCard 3 ∪ Aᶜ.powersetCard 3 := by
  obtain ⟨A,hA,hblock,hpartition⟩ := orthogonal_triples_has_block F
    (card_pos.mp (by omega)) hsize hcols hrows
  refine ⟨A,hA,?_⟩
  have hAc : Aᶜ.card = 4 := by simp [card_compl,hA]
  have hsub : F ⊆ A.powersetCard 3 ∪ Aᶜ.powersetCard 3 := by
    intro T hT
    rcases hpartition T hT with h | h
    · exact mem_union_left _ (mem_powersetCard.mpr ⟨h,hsize T hT⟩)
    · apply mem_union_right
      apply mem_powersetCard.mpr
      refine ⟨?_,hsize T hT⟩
      intro x hx
      exact mem_compl.mpr (fun ha => disjoint_left.mp h hx ha)
  have hdis : Disjoint (A.powersetCard 3) (Aᶜ.powersetCard 3) := by
    apply disjoint_left.mpr
    intro T hT hT'
    have h1 := (mem_powersetCard.mp hT).1
    have h2 := (mem_powersetCard.mp hT').1
    have hempty : T = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (mem_compl.mp (h2 hx)) (h1 hx)
    have hc := (mem_powersetCard.mp hT).2
    rw [hempty] at hc
    simp at hc
  apply eq_of_subset_of_card_le hsub
  rw [card_union_of_disjoint hdis, card_powersetCard, card_powersetCard, hA, hAc, hF]
  decide

#print axioms orthogonal_eight_triples_two_blocks
end PricingG
