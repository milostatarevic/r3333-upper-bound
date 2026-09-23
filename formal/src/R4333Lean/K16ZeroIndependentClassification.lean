import R4333Lean.CriticalTemplateDeletion
namespace R4333
def k16ZeroCandidateForbidden : Fin 10 → Fin 10 → Bool := ![
  ![false, false, false, false, false, true, false, true, false, true],
  ![false, false, false, false, true, false, true, false, false, true],
  ![false, false, false, false, true, false, false, true, true, false],
  ![false, false, false, false, false, true, true, false, true, false],
  ![false, true, true, false, false, true, false, false, false, false],
  ![true, false, false, true, true, false, false, false, false, false],
  ![false, true, false, true, false, false, false, true, false, false],
  ![true, false, true, false, false, false, true, false, false, false],
  ![false, false, true, true, false, false, false, false, false, true],
  ![true, true, false, false, false, false, false, false, true, false]
]
def K16ZeroCandidateIndependent (T : Finset (Fin 10)) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, i ≠ j → k16ZeroCandidateForbidden i j = false
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16ZeroCandidateIndependent_cardFour_classification : ∀ T ∈ (Finset.univ : Finset (Fin 10)).powersetCard 4,
  K16ZeroCandidateIndependent T → T = {0,1,2,3} ∨ T = {0,4,6,8} ∨ T = {1,5,7,8} ∨
    T = {2,5,6,9} ∨ T = {3,4,7,9} := by
  intro T hT hgood
  have hcard : T.card = 4 := (Finset.mem_powersetCard.mp hT).2
  have forbid {i j : Fin 10} (hi : i ∈ T) (hij : i ≠ j)
      (hedge : k16ZeroCandidateForbidden i j = true) : j ∉ T := by
    intro hj
    have h := hgood i hi j hj hij
    simp [hedge] at h
  by_cases h0 : (0 : Fin 10) ∈ T <;>
    by_cases h1 : (1 : Fin 10) ∈ T <;>
    by_cases h2 : (2 : Fin 10) ∈ T <;>
    by_cases h3 : (3 : Fin 10) ∈ T
  · left
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        using And.intro h0 (And.intro h1 (And.intro h2 h3))
    · simp [hcard]
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    have hsub : T ⊆ {0, 1, 2} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=3) (j:=8) h3 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    have hsub : T ⊆ {0, 1, 3} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    have hsub : T ⊆ {0, 1, 8} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=2) (j:=4) h2 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=3) (j:=6) h3 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    have hsub : T ⊆ {0, 2, 3} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=2) (j:=4) h2 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    have hsub : T ⊆ {0, 2, 6} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=3) (j:=6) h3 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=3) (j:=8) h3 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    have hsub : T ⊆ {0, 3, 4} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · right; left
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=0) (j:=5) h0 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=0) (j:=7) h0 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=0) (j:=9) h0 (by decide) (by decide)
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      fin_cases x <;> simp_all
    · simp [hcard]
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=3) (j:=5) h3 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=2) (j:=7) h2 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=1) (j:=9) h1 (by decide) (by decide)
    have hsub : T ⊆ {1, 2, 3} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=2) (j:=7) h2 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=1) (j:=9) h1 (by decide) (by decide)
    have hsub : T ⊆ {1, 2, 5} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=3) (j:=5) h3 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=3) (j:=8) h3 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=1) (j:=9) h1 (by decide) (by decide)
    have hsub : T ⊆ {1, 3, 7} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · right; right; left
    have h4 : (4 : Fin 10) ∉ T := forbid (i:=1) (j:=4) h1 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=1) (j:=6) h1 (by decide) (by decide)
    have h9 : (9 : Fin 10) ∉ T := forbid (i:=1) (j:=9) h1 (by decide) (by decide)
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      fin_cases x <;> simp_all
    · simp [hcard]
  · have h4 : (4 : Fin 10) ∉ T := forbid (i:=2) (j:=4) h2 (by decide) (by decide)
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=3) (j:=5) h3 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=3) (j:=6) h3 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=2) (j:=7) h2 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    have hsub : T ⊆ {2, 3, 9} := by
      intro x hx
      fin_cases x <;> simp_all
    have := Finset.card_le_card hsub
    simp [hcard] at this
  · right; right; right; left
    have h4 : (4 : Fin 10) ∉ T := forbid (i:=2) (j:=4) h2 (by decide) (by decide)
    have h7 : (7 : Fin 10) ∉ T := forbid (i:=2) (j:=7) h2 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=2) (j:=8) h2 (by decide) (by decide)
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      fin_cases x <;> simp_all
    · simp [hcard]
  · right; right; right; right
    have h5 : (5 : Fin 10) ∉ T := forbid (i:=3) (j:=5) h3 (by decide) (by decide)
    have h6 : (6 : Fin 10) ∉ T := forbid (i:=3) (j:=6) h3 (by decide) (by decide)
    have h8 : (8 : Fin 10) ∉ T := forbid (i:=3) (j:=8) h3 (by decide) (by decide)
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      fin_cases x <;> simp_all
    · simp [hcard]
  · by_cases h4 : (4 : Fin 10) ∈ T
    · have h5 : (5 : Fin 10) ∉ T := forbid h4 (by decide) (by decide)
      by_cases h6 : (6 : Fin 10) ∈ T
      · have h7 : (7 : Fin 10) ∉ T := forbid h6 (by decide) (by decide)
        by_cases h8 : (8 : Fin 10) ∈ T
        · have h9 : (9 : Fin 10) ∉ T := forbid h8 (by decide) (by decide)
          have hsub : T ⊆ {4, 6, 8} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
        · have hsub : T ⊆ {4, 6, 9} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
      · by_cases h8 : (8 : Fin 10) ∈ T
        · have h9 : (9 : Fin 10) ∉ T := forbid h8 (by decide) (by decide)
          have hsub : T ⊆ {4, 7, 8} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
        · have hsub : T ⊆ {4, 7, 9} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
    · by_cases h6 : (6 : Fin 10) ∈ T
      · have h7 : (7 : Fin 10) ∉ T := forbid h6 (by decide) (by decide)
        by_cases h8 : (8 : Fin 10) ∈ T
        · have h9 : (9 : Fin 10) ∉ T := forbid h8 (by decide) (by decide)
          have hsub : T ⊆ {5, 6, 8} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
        · have hsub : T ⊆ {5, 6, 9} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
      · by_cases h8 : (8 : Fin 10) ∈ T
        · have h9 : (9 : Fin 10) ∉ T := forbid h8 (by decide) (by decide)
          have hsub : T ⊆ {5, 7, 8} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
        · have hsub : T ⊆ {5, 7, 9} := by intro x hx; fin_cases x <;> simp_all
          have := Finset.card_le_card hsub; simp [hcard] at this
end R4333

