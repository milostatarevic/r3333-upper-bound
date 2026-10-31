import UniformK60.Profiles

/-!
The K60 ticket reduction. The four strict bounds are explicit hypotheses;
this file does not assert that their SAT campaigns are complete.
-/

set_option autoImplicit false
namespace UniformK60
open Ramsey61 Finset

/-- The four strict ticket bounds supplied by the marked A/B/D/E covers. -/
def StrictTicketBounds (c : Host) : Prop := ∀ v,
  (W c v = 48 → H c v ≤ 47) ∧ (W c v = 47 → H c v ≤ 46) ∧
  (W c v = 46 → H c v ≤ 45) ∧ (W c v = 45 → H c v ≤ 44)

/-- A ticket entering a noncritical group at an eligible C1 or C2 root. -/
def CExteriorWitness (c : Host) : Prop := ∃ v u,
  (W c v = 32 ∨ W c v = 31) ∧ W c v ≤ H c v ∧
    u ∈ Incoming c v ∧ u ∉ Own c v

theorem witness_edge_semantics (c : Host) (v u : Fin 60) :
    (u ∈ Incoming c v ∧ u ∉ Own c v) ↔
      u ≠ v ∧ colorDegree c (c v u) v < 15 ∧ 15 ≤ colorDegree c (c v u) u := by
  simp only [Incoming, Own, highOwnNeighborSupport, incomingHighOwnSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [c.color_symm u v]
  omega

theorem W_eq_own_card (c : Host) (v : Fin 60) : W c v = (Own c v).card :=
  (incomingHighOwnSupport_card_eq_criticalDegreeMass c v).symm

theorem no_C_witness_forces_pointwise_le (c : Host) (hc : NoMonochromaticTriangle c)
    (bounds : StrictTicketBounds c) (none : ¬ CExteriorWitness c) :
    ∀ v, H c v ≤ W c v := by
  intro v
  have cle (hC : W c v = 32 ∨ W c v = 31) : H c v ≤ W c v := by
    by_contra hnot
    have hhigh : W c v ≤ H c v := by omega
    have hsub : Incoming c v ⊆ Own c v := by
      intro u hu
      by_contra hn
      exact none ⟨v, u, hC, hhigh, hu, hn⟩
    have hcard := Finset.card_le_card hsub
    rw [← W_eq_own_card] at hcard
    change H c v ≤ W c v at hcard
    omega
  rcases W_cases c hc v with hA | hB | hC1 | hD | hC2 | hE
  · have := (bounds v).1 hA; omega
  · have := (bounds v).2.1 hB; omega
  · exact cle (Or.inl hC1)
  · have := (bounds v).2.2.1 hD; omega
  · exact cle (Or.inr hC2)
  · have := (bounds v).2.2.2 hE; omega

/-- Double counting upgrades every weak ticket bound to equality. -/
theorem no_C_witness_forces_equality (c : Host) (hc : NoMonochromaticTriangle c)
    (bounds : StrictTicketBounds c) (none : ¬ CExteriorWitness c) :
    ∀ v, H c v = W c v := by
  have hle := no_C_witness_forces_pointwise_le c hc bounds none
  have hsum := total_highOwn_eq_total_criticalDegreeMass c
  intro v
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp hsum v (Finset.mem_univ v)

theorem no_C_witness_forces_C (c : Host) (hc : NoMonochromaticTriangle c)
    (bounds : StrictTicketBounds c) (none : ¬ CExteriorWitness c) :
    ∀ v, (W c v = 32 ∨ W c v = 31) ∧ H c v = W c v := by
  intro v
  have heq := no_C_witness_forces_equality c hc bounds none v
  refine ⟨?_, heq⟩
  rcases W_cases c hc v with hA | hB | hC1 | hD | hC2 | hE
  · have := (bounds v).1 hA; omega
  · have := (bounds v).2.1 hB; omega
  · exact Or.inl hC1
  · have := (bounds v).2.2.1 hD; omega
  · exact Or.inr hC2
  · have := (bounds v).2.2.2 hE; omega

/-- Perfect balance permits both C profiles, with reciprocal tickets. -/
def Synchronized (c : Host) : Prop :=
  (∀ v, W c v = 32 ∨ W c v = 31) ∧ (∀ v, Incoming c v = Own c v)

theorem no_C_witness_forces_synchronized (c : Host) (hc : NoMonochromaticTriangle c)
    (bounds : StrictTicketBounds c) (none : ¬ CExteriorWitness c) : Synchronized c := by
  have hC := no_C_witness_forces_C c hc bounds none
  refine ⟨fun v => (hC v).1, ?_⟩
  intro v
  have hsub : Incoming c v ⊆ Own c v := by
    intro u hu
    by_contra hn
    exact none ⟨v, u, (hC v).1, (hC v).2.ge, hu, hn⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [← W_eq_own_card]
  change W c v ≤ H c v
  exact (hC v).2.ge

theorem synchronized_endpoint_highness (c : Host) (sync : Synchronized c)
    (v u : Fin 60) (hne : u ≠ v) :
    (15 ≤ colorDegree c (c v u) v ↔ 15 ≤ colorDegree c (c v u) u) := by
  have hm := (Finset.ext_iff.mp (sync.2 v) u).symm
  simpa [Incoming, Own, highOwnNeighborSupport, incomingHighOwnSupport,
    hne, c.color_symm u v] using hm

theorem synchronized_no_color_edge_across_cut (c : Host) (sync : Synchronized c)
    (q : FourColor) (v u : Fin 60) (hne : u ≠ v)
    (hv : colorDegree c q v < 15) (hu : 15 ≤ colorDegree c q u) : c v u ≠ q := by
  intro hedge
  have hsync := synchronized_endpoint_highness c sync v u hne
  rw [hedge] at hsync
  have := hsync.mpr hu
  omega

#print axioms no_C_witness_forces_synchronized
#print axioms synchronized_endpoint_highness
end UniformK60
