import UniformK60.BalancedHostAllFive

set_option autoImplicit false
namespace UniformK60.BalancedHost
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization

/-- Under the common generic caps, the all-C1 alternative gives both
named high degrees16 at every actual vertex. -/
theorem named_all_C1_sixteen (c : Host) (hn : NamedCaps c) (hall : ∀ v,W c v=32) :
    AllOwnSixteen c := by
  intro v q hq
  have hw := (W_eq_mass4 c v).symm.trans (hall v)
  change mass4 (colorDegree c (palette 0) v) (colorDegree c (palette 1) v)
    (colorDegree c (palette 2) v) (colorDegree c (palette 3) v)=32 at hw
  have hpair : colorDegree c (palette 0) v=16 ∧ colorDegree c (palette 1) v=16 := by
    rcases named_caps_vectors c hn v with h | h | h | h
    · obtain ⟨h0,h1,h2,h3⟩ := h
      rw [h0,h1,h2,h3] at hw
      norm_num [mass4] at hw
    · obtain ⟨h0,h1,h2,h3⟩ := h
      rw [h0,h1,h2,h3] at hw
      norm_num [mass4] at hw
    · exact ⟨h.1,h.2.1⟩
    · exact ⟨h.1,h.2.1⟩
  have hq' : q=0 ∨ q=1 := by
    have h : q.val=0 ∨ q.val=1 := by omega
    exact h.elim (fun h=>Or.inl (Fin.ext h)) (fun h=>Or.inr (Fin.ext h))
  rcases hq' with rfl | rfl
  · exact hpair.1
  · exact hpair.2

theorem named_weight_cases (c : Host) (hn : NamedCaps c) (v : Vertex) :
    W c v=31 ∨ W c v=32 := by
  have hw := W_eq_mass4 c v
  change W c v=mass4 (colorDegree c (palette 0) v) (colorDegree c (palette 1) v)
    (colorDegree c (palette 2) v) (colorDegree c (palette 3) v) at hw
  rcases named_caps_vectors c hn v with h | h | h | h <;>
    obtain ⟨h0,h1,h2,h3⟩ := h <;> rw [h0,h1,h2,h3] at hw <;>
    norm_num [mass4] at hw <;> simp [hw]

theorem exists_C2_of_not_all_C1 (c : Host) (hn : NamedCaps c)
    (h : ¬∀ v,W c v=32) : ∃ v,W c v=31 := by
  classical
  obtain ⟨v,hv⟩ := not_forall.mp h
  exact ⟨v,(named_weight_cases c hn v).resolve_right hv⟩

#print axioms named_all_C1_sixteen
#print axioms exists_C2_of_not_all_C1
end UniformK60.BalancedHost
