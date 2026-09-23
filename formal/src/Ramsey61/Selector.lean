import Ramsey61.Incidence

namespace Ramsey61
open Finset

abbrev Host := EdgeColoring (Fin 61) FourColor
abbrev H (c : Host) := highOwnNeighborCount c
abbrev W (c : Host) := criticalDegreeMass c
abbrev Own (c : Host) := incomingHighOwnSupport c
abbrev Incoming (c : Host) := highOwnNeighborSupport c

def mass4 (a b c d : Nat) : Nat :=
  (if 15 ≤ a then a else 0) + (if 15 ≤ b then b else 0) +
  (if 15 ≤ c then c else 0) + (if 15 ≤ d then d else 0)

theorem sorted_degree_profiles (a b c d : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ 16) (hsum : a + b + c + d = 60) :
    (a = 12 ∧ b = 16 ∧ c = 16 ∧ d = 16) ∨
    (a = 13 ∧ b = 15 ∧ c = 16 ∧ d = 16) ∨
    (a = 14 ∧ b = 14 ∧ c = 16 ∧ d = 16) ∨
    (a = 14 ∧ b = 15 ∧ c = 15 ∧ d = 16) ∨
    (a = 15 ∧ b = 15 ∧ c = 15 ∧ d = 15) := by omega

theorem mass4_cases (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) :
    mass4 a b c d = 48 ∨ mass4 a b c d = 47 ∨ mass4 a b c d = 32 ∨
      mass4 a b c d = 46 ∨ mass4 a b c d = 60 := by
  unfold mass4
  split_ifs <;> omega

theorem W_eq_mass4 (c : Host) (v : Fin 61) :
    W c v = mass4 (colorDegree c (false,false) v) (colorDegree c (false,true) v)
      (colorDegree c (true,false) v) (colorDegree c (true,true) v) := by
  simp [W, criticalDegreeMass, mass4, FourColor, Fintype.sum_prod_type,
    Nat.add_comm, Nat.add_assoc]

theorem W_cases (c : Host) (hc : NoMonochromaticTriangle c) (v : Fin 61) :
    W c v = 48 ∨ W c v = 47 ∨ W c v = 32 ∨ W c v = 46 ∨ W c v = 60 := by
  rw [W_eq_mass4]
  apply mass4_cases
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · simpa using fourColor_degree_sum c v

/-- Exactly the three supplied-root selector consequences; still a hypothesis. -/
def SelectorX (c : Host) : Prop := ∀ v,
  (W c v = 48 → H c v ≤ 47) ∧ (W c v = 47 → H c v ≤ 46) ∧
  (W c v = 46 → H c v ≤ 45)

/-- A physical low-at-root/high-at-neighbor incidence at an eligible C root.
The mass32/degree-pattern equivalence is proved below, not postulated. -/
def CExteriorWitness (c : Host) : Prop := ∃ v u,
  W c v = 32 ∧ 32 ≤ H c v ∧ u ∈ Incoming c v ∧ u ∉ Own c v

theorem witness_edge_semantics (c : Host) (v u : Fin 61) :
    (u ∈ Incoming c v ∧ u ∉ Own c v) ↔
      u ≠ v ∧ colorDegree c (c v u) v < 15 ∧ 15 ≤ colorDegree c (c v u) u := by
  simp only [Incoming, Own, highOwnNeighborSupport, incomingHighOwnSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [c.color_symm u v]
  omega

theorem H_le_sixty (c : Host) (v : Fin 61) : H c v ≤ 60 := by
  have hsub : Incoming c v ⊆ (Finset.univ : Finset (Fin 61)).erase v := by
    intro u hu
    have h := (mem_highOwnNeighborSupport c v u).mp hu
    simp [h.1]
  have h := Finset.card_le_card hsub
  simpa [H, highOwnNeighborCount] using h

theorem W_eq_own_card (c : Host) (v : Fin 61) : W c v = (Own c v).card :=
  (incomingHighOwnSupport_card_eq_criticalDegreeMass c v).symm

theorem no_C_witness_forces_pointwise_le (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (none : ¬ CExteriorWitness c) : ∀ v, H c v ≤ W c v := by
  intro v
  rcases W_cases c hc v with hA | hB | hC | hD | hE
  · have := (selectors v).1 hA; omega
  · have := (selectors v).2.1 hB; omega
  · by_contra hnot
    have hhigh : 32 ≤ H c v := by omega
    have hsub : Incoming c v ⊆ Own c v := by
      intro u hu
      by_contra hn
      exact none ⟨v,u,hC,hhigh,hu,hn⟩
    have hcard := Finset.card_le_card hsub
    rw [← W_eq_own_card] at hcard
    change H c v ≤ W c v at hcard
    omega
  · have := (selectors v).2.2 hD; omega
  · have := H_le_sixty c v; omega

theorem no_C_witness_forces_equality (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (none : ¬ CExteriorWitness c) : ∀ v, H c v = W c v := by
  have hle := no_C_witness_forces_pointwise_le c hc selectors none
  have hsum := total_highOwn_eq_total_criticalDegreeMass c
  intro v
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp hsum v (Finset.mem_univ v)

theorem no_C_witness_forces_CE (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (none : ¬ CExteriorWitness c) :
    ∀ v, (W c v = 32 ∨ W c v = 60) ∧ H c v = W c v := by
  intro v
  have heq := no_C_witness_forces_equality c hc selectors none v
  refine ⟨?_,heq⟩
  rcases W_cases c hc v with hA | hB | hC | hD | hE
  · have := (selectors v).1 hA; omega
  · have := (selectors v).2.1 hB; omega
  · exact Or.inl hC
  · have := (selectors v).2.2 hD; omega
  · exact Or.inr hE

/-- The exact32 mass forces every degree to be14 or16, as required for C. -/
theorem mass32_coordinates (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) (hm : mass4 a b c d = 32) :
    (a = 14 ∨ a = 16) ∧ (b = 14 ∨ b = 16) ∧
    (c = 14 ∨ c = 16) ∧ (d = 14 ∨ d = 16) := by
  unfold mass4 at hm
  split_ifs at hm <;> omega

theorem mass60_coordinates (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) (hm : mass4 a b c d = 60) :
    a = 15 ∧ b = 15 ∧ c = 15 ∧ d = 15 := by
  unfold mass4 at hm
  split_ifs at hm <;> omega

theorem W32_degree_cases (c : Host) (hc : NoMonochromaticTriangle c) (v : Fin 61)
    (hm : W c v = 32) : ∀ q, colorDegree c q v = 14 ∨ colorDegree c q v = 16 := by
  have ht := mass32_coordinates
    (colorDegree c (false,false) v) (colorDegree c (false,true) v)
    (colorDegree c (true,false) v) (colorDegree c (true,true) v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (by simpa using fourColor_degree_sum c v) (by rw [← W_eq_mass4]; exact hm)
  intro q
  rcases q with ⟨q₁,q₂⟩
  cases q₁ <;> cases q₂ <;> tauto

theorem W60_degree_cases (c : Host) (hc : NoMonochromaticTriangle c) (v : Fin 61)
    (hm : W c v = 60) : ∀ q, colorDegree c q v = 15 := by
  have ht := mass60_coordinates
    (colorDegree c (false,false) v) (colorDegree c (false,true) v)
    (colorDegree c (true,false) v) (colorDegree c (true,true) v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (by simpa using fourColor_degree_sum c v) (by rw [← W_eq_mass4]; exact hm)
  intro q
  rcases q with ⟨q₁,q₂⟩
  cases q₁ <;> cases q₂ <;> tauto

/-- The synchronized C/E branch used by the proved incidence entrance.
The final composition is `PricingIntegration.NativeWholeProof.ramsey61`. -/
def SynchronizedCE (c : Host) : Prop :=
  (∀ v, W c v = 32 ∨ W c v = 60) ∧ (∀ v, Incoming c v = Own c v)

theorem no_C_witness_forces_synchronized_CE (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (none : ¬ CExteriorWitness c) : SynchronizedCE c := by
  have hCE := no_C_witness_forces_CE c hc selectors none
  refine ⟨fun v => (hCE v).1, ?_⟩
  intro v
  have hsub : Incoming c v ⊆ Own c v := by
    intro u hu
    rcases (hCE v).1 with hC | hE
    · by_contra hn
      exact none ⟨v,u,hC,by have := (hCE v).2; omega,hu,hn⟩
    · have hne := ((mem_highOwnNeighborSupport c v u).mp hu).1
      have hd := W60_degree_cases c hc v hE (c u v)
      simp [Own, incomingHighOwnSupport, hne, hd]
  apply Finset.eq_of_subset_of_card_le hsub
  rw [← W_eq_own_card]
  change W c v ≤ H c v
  exact (hCE v).2.ge

theorem synchronized_endpoint_highness (c : Host) (sync : SynchronizedCE c)
    (v u : Fin 61) (hne : u ≠ v) :
    (15 ≤ colorDegree c (c v u) v ↔ 15 ≤ colorDegree c (c v u) u) := by
  have hm := (Finset.ext_iff.mp (sync.2 v) u).symm
  simpa [Incoming, Own, highOwnNeighborSupport, incomingHighOwnSupport,
    hne, c.color_symm u v] using hm

/-- The actual color graph has no edge from its low set to its high complement. -/
theorem synchronized_no_color_edge_across_cut (c : Host) (sync : SynchronizedCE c)
    (q : FourColor) (v u : Fin 61) (hne : u ≠ v)
    (hv : colorDegree c q v < 15) (hu : 15 ≤ colorDegree c q u) : c v u ≠ q := by
  intro hedge
  have hsync := synchronized_endpoint_highness c sync v u hne
  rw [hedge] at hsync
  have := hsync.mpr hu
  omega

/-- These arithmetic interfaces identify A, B and D independently of palette order. -/
theorem mass4_ABD_interfaces (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) :
    (mass4 a b c d = 48 ↔ a = 12 ∨ b = 12 ∨ c = 12 ∨ d = 12) ∧
    (mass4 a b c d = 47 ↔ a = 13 ∨ b = 13 ∨ c = 13 ∨ d = 13) ∧
    (mass4 a b c d = 46 ↔
      (a = 14 ∨ b = 14 ∨ c = 14 ∨ d = 14) ∧ (a = 15 ∨ b = 15 ∨ c = 15 ∨ d = 15)) := by
  unfold mass4
  split_ifs <;> omega

end Ramsey61
