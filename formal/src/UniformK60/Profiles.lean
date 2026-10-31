import Ramsey61.Incidence

set_option autoImplicit false

namespace UniformK60
open Ramsey61 Finset

/-- A hypothetical four-coloring of the complete graph on 60 vertices. -/
abbrev Host := EdgeColoring (Fin 60) FourColor
abbrev H (c : Host) := highOwnNeighborCount c
abbrev W (c : Host) := criticalDegreeMass c
abbrev Own (c : Host) := incomingHighOwnSupport c
abbrev Incoming (c : Host) := highOwnNeighborSupport c

/-- The number of tickets sent, written in four labeled degree coordinates. -/
def mass4 (a b c d : Nat) : Nat :=
  (if 15 ≤ a then a else 0) + (if 15 ≤ b then b else 0) +
  (if 15 ≤ c then c else 0) + (if 15 ≤ d then d else 0)

/-- The six sorted degree profiles at order 60. -/
theorem sorted_degree_profiles (a b c d : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ 16) (hsum : a + b + c + d = 59) :
    (a = 11 ∧ b = 16 ∧ c = 16 ∧ d = 16) ∨
    (a = 12 ∧ b = 15 ∧ c = 16 ∧ d = 16) ∨
    (a = 13 ∧ b = 14 ∧ c = 16 ∧ d = 16) ∨
    (a = 13 ∧ b = 15 ∧ c = 15 ∧ d = 16) ∨
    (a = 14 ∧ b = 14 ∧ c = 15 ∧ d = 16) ∨
    (a = 14 ∧ b = 15 ∧ c = 15 ∧ d = 15) := by
  omega

/-- The weights of A, B, C1, D, C2 and E, in that order. -/
theorem mass4_profile_weights :
    mass4 11 16 16 16 = 48 ∧ mass4 12 15 16 16 = 47 ∧
    mass4 13 14 16 16 = 32 ∧ mass4 13 15 15 16 = 46 ∧
    mass4 14 14 15 16 = 31 ∧ mass4 14 15 15 15 = 45 := by
  decide

/-- The six weights do not depend on the ordering of the colors. -/
theorem mass4_cases (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 59) :
    mass4 a b c d = 48 ∨ mass4 a b c d = 47 ∨ mass4 a b c d = 32 ∨
      mass4 a b c d = 46 ∨ mass4 a b c d = 31 ∨ mass4 a b c d = 45 := by
  unfold mass4
  split_ifs <;> omega

theorem W_eq_mass4 (c : Host) (v : Fin 60) :
    W c v = mass4 (colorDegree c (false, false) v) (colorDegree c (false, true) v)
      (colorDegree c (true, false) v) (colorDegree c (true, true) v) := by
  simp [W, criticalDegreeMass, mass4, FourColor, Fintype.sum_prod_type,
    Nat.add_comm, Nat.add_assoc]

theorem W_cases (c : Host) (hc : NoMonochromaticTriangle c) (v : Fin 60) :
    W c v = 48 ∨ W c v = 47 ∨ W c v = 32 ∨ W c v = 46 ∨
      W c v = 31 ∨ W c v = 45 := by
  rw [W_eq_mass4]
  apply mass4_cases
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · simpa using fourColor_degree_sum c v

/-- Weight 32 has the coordinate values of C1: 13, 14 and 16. -/
theorem mass32_coordinates (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 59) (hm : mass4 a b c d = 32) :
    (a = 13 ∨ a = 14 ∨ a = 16) ∧ (b = 13 ∨ b = 14 ∨ b = 16) ∧
    (c = 13 ∨ c = 14 ∨ c = 16) ∧ (d = 13 ∨ d = 14 ∨ d = 16) := by
  unfold mass4 at hm
  split_ifs at hm <;> omega

/-- Weight 31 has the coordinate values of C2: 14, 15 and 16. -/
theorem mass31_coordinates (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 59) (hm : mass4 a b c d = 31) :
    (a = 14 ∨ a = 15 ∨ a = 16) ∧ (b = 14 ∨ b = 15 ∨ b = 16) ∧
    (c = 14 ∨ c = 15 ∨ c = 16) ∧ (d = 14 ∨ d = 15 ∨ d = 16) := by
  unfold mass4 at hm
  split_ifs at hm <;> omega

theorem W32_degree_cases (c : Host) (hc : NoMonochromaticTriangle c) (v : Fin 60)
    (hm : W c v = 32) :
    ∀ q, colorDegree c q v = 13 ∨ colorDegree c q v = 14 ∨ colorDegree c q v = 16 := by
  have ht := mass32_coordinates
    (colorDegree c (false, false) v) (colorDegree c (false, true) v)
    (colorDegree c (true, false) v) (colorDegree c (true, true) v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (by simpa using fourColor_degree_sum c v) (by rw [← W_eq_mass4]; exact hm)
  intro q
  rcases q with ⟨q₁, q₂⟩
  cases q₁ <;> cases q₂
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2.1
  · exact ht.2.2.2

theorem W31_degree_cases (c : Host) (hc : NoMonochromaticTriangle c) (v : Fin 60)
    (hm : W c v = 31) :
    ∀ q, colorDegree c q v = 14 ∨ colorDegree c q v = 15 ∨ colorDegree c q v = 16 := by
  have ht := mass31_coordinates
    (colorDegree c (false, false) v) (colorDegree c (false, true) v)
    (colorDegree c (true, false) v) (colorDegree c (true, true) v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (fourColor_colorDegree_le_sixteen c hc _ v) (fourColor_colorDegree_le_sixteen c hc _ v)
    (by simpa using fourColor_degree_sum c v) (by rw [← W_eq_mass4]; exact hm)
  intro q
  rcases q with ⟨q₁, q₂⟩
  cases q₁ <;> cases q₂
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2.1
  · exact ht.2.2.2

/-- The colors along which the vertex sends tickets. -/
def criticalColors (c : Host) (v : Fin 60) : Finset FourColor :=
  Finset.univ.filter fun q => 15 ≤ colorDegree c q v

@[simp] theorem mem_criticalColors (c : Host) (v : Fin 60) (q : FourColor) :
    q ∈ criticalColors c v ↔ 15 ≤ colorDegree c q v := by
  simp [criticalColors]

private def criticalCount4 (a b c d : Nat) : Nat :=
  (if 15 ≤ a then 1 else 0) + (if 15 ≤ b then 1 else 0) +
  (if 15 ≤ c then 1 else 0) + (if 15 ≤ d then 1 else 0)

private theorem criticalCount4_eq_two (a b c d : Nat)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 59)
    (hm : mass4 a b c d = 32 ∨ mass4 a b c d = 31) :
    criticalCount4 a b c d = 2 := by
  unfold mass4 at hm
  unfold criticalCount4
  split_ifs at * <;> omega

private theorem criticalColors_card_eq_count4 (c : Host) (v : Fin 60) :
    (criticalColors c v).card =
      criticalCount4 (colorDegree c (false, false) v) (colorDegree c (false, true) v)
        (colorDegree c (true, false) v) (colorDegree c (true, true) v) := by
  unfold criticalColors
  rw [Finset.card_filter]
  simp only [FourColor, Fintype.sum_prod_type, Fintype.sum_bool, criticalCount4]
  omega

/-- Both surviving profiles have exactly two critical colors. -/
theorem criticalColors_card_two (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 60) (hm : W c v = 32 ∨ W c v = 31) :
    (criticalColors c v).card = 2 := by
  rw [criticalColors_card_eq_count4]
  apply criticalCount4_eq_two
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · exact fourColor_colorDegree_le_sixteen c hc _ v
  · simpa using fourColor_degree_sum c v
  · simpa only [W_eq_mass4] using hm

/-- The surviving branch allows both C1 and C2 vertices. -/
theorem balanced_degree_bounds (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 60) (hm : W c v = 32 ∨ W c v = 31) (q : FourColor) :
    13 ≤ colorDegree c q v ∧ colorDegree c q v ≤ 16 := by
  rcases hm with h32 | h31
  · have h := W32_degree_cases c hc v h32 q
    omega
  · have h := W31_degree_cases c hc v h31 q
    omega

theorem balanced_low_degree_bounds (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 60) (hm : W c v = 32 ∨ W c v = 31) (q : FourColor)
    (hq : q ∉ criticalColors c v) :
    13 ≤ colorDegree c q v ∧ colorDegree c q v ≤ 14 := by
  have h := balanced_degree_bounds c hc v hm q
  have hn : ¬ 15 ≤ colorDegree c q v := by simpa using hq
  omega

theorem balanced_high_degree_bounds (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 60) (hm : W c v = 32 ∨ W c v = 31) (q : FourColor)
    (hq : q ∈ criticalColors c v) :
    15 ≤ colorDegree c q v ∧ colorDegree c q v ≤ 16 := by
  exact ⟨(mem_criticalColors c v q).mp hq,
    (balanced_degree_bounds c hc v hm q).2⟩

theorem W32_high_degree_eq_sixteen (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 60) (hm : W c v = 32) (q : FourColor)
    (hq : q ∈ criticalColors c v) : colorDegree c q v = 16 := by
  have h := W32_degree_cases c hc v hm q
  have hhigh := (mem_criticalColors c v q).mp hq
  omega

theorem W31_low_degree_eq_fourteen (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 60) (hm : W c v = 31) (q : FourColor)
    (hq : q ∉ criticalColors c v) : colorDegree c q v = 14 := by
  have h := W31_degree_cases c hc v hm q
  have hn : ¬ 15 ≤ colorDegree c q v := by simpa using hq
  omega

end UniformK60
