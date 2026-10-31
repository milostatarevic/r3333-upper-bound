import UniformK60.BalancedLocal

set_option autoImplicit false
namespace UniformK60.ClassificationGeometry
open Ramsey61 Finset

/-- Genuine high marks inside one actual root neighborhood. -/
def rootBlockMarks (c : Host) (r : Fin 60) (q : FourColor) : Finset (Fin 60) :=
  colorNeighborhood c q r ∩ Incoming c r

/-- A size-16 root cell omits only 43 of the root's 59 physical neighbors. -/
theorem rootBlockMarks_lower_bound (c : Host) (r : Fin 60) (q : FourColor)
    (hdegree : colorDegree c q r = 16) : H c r ≤ (rootBlockMarks c r q).card + 43 := by
  classical
  have hsub : colorNeighborhood c q r ∪ Incoming c r ⊆
      (univ : Finset (Fin 60)).erase r := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_erase.mpr ⟨((mem_colorNeighborhood c q r v).mp hv).1, mem_univ _⟩
    · exact mem_erase.mpr ⟨((mem_highOwnNeighborSupport c r v).mp hv).1, mem_univ _⟩
  have hcard := card_le_card hsub
  have hidentity := card_union_add_card_inter (colorNeighborhood c q r) (Incoming c r)
  have hblock : (colorNeighborhood c q r).card = 16 := hdegree
  have hincoming : (Incoming c r).card = H c r := rfl
  have houtside : ((univ : Finset (Fin 60)).erase r).card = 59 := by simp
  change _ + (rootBlockMarks c r q).card = _ at hidentity
  omega

theorem rootBlockMarks_card_ge_sub (c : Host) (r : Fin 60) (q : FourColor)
    (hdegree : colorDegree c q r = 16) : H c r - 43 ≤ (rootBlockMarks c r q).card := by
  have := rootBlockMarks_lower_bound c r q hdegree
  omega

theorem rootBlockMarks_high (c : Host) (r : Fin 60) (q : FourColor)
    (x : Fin 60) (hx : x ∈ rootBlockMarks c r q) :
    x ∈ colorNeighborhood c q r ∧ 15 ≤ colorDegree c q x := by
  have hx' := mem_inter.mp hx
  have hcolor := ((mem_colorNeighborhood c q r x).mp hx'.1).2
  have hhigh := ((mem_highOwnNeighborSupport c r x).mp hx'.2).2
  exact ⟨hx'.1, by simpa [hcolor] using hhigh⟩

/-- The actual q-neighbors of x lying in the p-colored root cell. -/
def attachingSupport (c : Host) (r : Fin 60) (q : FourColor) (x : Fin 60)
    (p : FourColor) : Finset (Fin 60) :=
  colorNeighborhood c q x ∩ colorNeighborhood c p r

/-- Removing the root partitions the attaching neighborhood over exactly
the three foreign root colors, with no recoloring or vertex identification. -/
theorem attachingSupport_partition (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (x : Fin 60) (hx : x ∈ colorNeighborhood c q r) :
    colorDegree c q x - 1 =
      ∑ p ∈ (univ : Finset FourColor).erase q, (attachingSupport c r q x p).card := by
  classical
  let S := (colorNeighborhood c q x).erase r
  let K := (univ : Finset FourColor).erase q
  let f (p : FourColor) := S.filter fun y => c r y = p
  have hx' := (mem_colorNeighborhood c q r x).mp hx
  have hr : r ∈ colorNeighborhood c q x :=
    (colorNeighborhood_symm c q r x hx'.1.symm).mp hx
  have hScard : S.card = colorDegree c q x - 1 := by
    have h := card_erase_add_one hr
    change S.card + 1 = colorDegree c q x at h
    omega
  have havoid : ∀ y ∈ S, c r y ≠ q := by
    intro y hy hcolor
    have hy' := mem_erase.mp hy
    have hxy := (mem_colorNeighborhood c q x y).mp hy'.2
    exact hc r x y ⟨hx'.1.symm, hy'.1.symm, hxy.1.symm⟩
      ⟨hx'.2.trans hcolor.symm, hcolor.trans hxy.2.symm⟩
  have hpartition : S.card = ∑ p ∈ K, (f p).card :=
    card_eq_sum_card_fiberwise (fun y hy => mem_erase.mpr ⟨havoid y hy, mem_univ _⟩)
  have hfeq (p : FourColor) : f p = attachingSupport c r q x p := by
    ext y
    simp only [f, S, attachingSupport, mem_filter, mem_erase, mem_inter, mem_colorNeighborhood]
    tauto
  simpa only [hScard, hfeq, K] using hpartition

def FourFivePattern (a b d : Nat) : Prop :=
  (a = 4 ∧ b = 5 ∧ d = 5) ∨ (a = 5 ∧ b = 4 ∧ d = 5) ∨
  (a = 5 ∧ b = 5 ∧ d = 4) ∨ (a = 5 ∧ b = 5 ∧ d = 5)

/-- An ordered enumeration of the actual three foreign colors and the four
possible support-size patterns used by the A/B/D attaching search. -/
def AttachingSupportGeometry (c : Host) (r : Fin 60) (q : FourColor) (x : Fin 60) : Prop :=
  ∃ p₀ p₁ p₂ : FourColor, p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₁ ≠ p₂ ∧
    (univ : Finset FourColor).erase q = {p₀, p₁, p₂} ∧
    FourFivePattern (attachingSupport c r q x p₀).card
      (attachingSupport c r q x p₁).card (attachingSupport c r q x p₂).card

theorem genuine_high_attaching_support_geometry (c : Host)
    (hc : NoMonochromaticTriangle c) (r : Fin 60) (q : FourColor) (x : Fin 60)
    (hx : x ∈ colorNeighborhood c q r) (hhigh : 15 ≤ colorDegree c q x) :
    AttachingSupportGeometry c r q x := by
  classical
  let K := (univ : Finset FourColor).erase q
  have hK : K.card = 3 := by simp [K, FourColor]
  obtain ⟨p₀, p₁, p₂, h01, h02, h12, heq⟩ := card_eq_three.mp hK
  have h0 : p₀ ≠ q := (mem_erase.mp (show p₀ ∈ K by rw [heq]; simp)).1
  have h1 : p₁ ≠ q := (mem_erase.mp (show p₁ ∈ K by rw [heq]; simp)).1
  have h2 : p₂ ≠ q := (mem_erase.mp (show p₂ ∈ K by rw [heq]; simp)).1
  have b0 : (attachingSupport c r q x p₀).card ≤ 5 :=
    BalancedStructure.inter_le_five c hc q p₀ h0.symm x r
  have b1 : (attachingSupport c r q x p₁).card ≤ 5 :=
    BalancedStructure.inter_le_five c hc q p₁ h1.symm x r
  have b2 : (attachingSupport c r q x p₂).card ≤ 5 :=
    BalancedStructure.inter_le_five c hc q p₂ h2.symm x r
  have hsum := attachingSupport_partition c hc r q x hx
  change _ = ∑ p ∈ K, _ at hsum
  rw [heq] at hsum
  simp only [sum_insert, mem_insert, mem_singleton, h01, h02, h12,
    false_or, not_false_eq_true, sum_singleton] at hsum
  have hupper := fourColor_colorDegree_le_sixteen c hc q x
  refine ⟨p₀, p₁, p₂, h01, h02, h12, heq, ?_⟩
  unfold FourFivePattern
  omega

/-- This is the direct extraction boundary for a supplied A/B/D root:
every size-16 root cell has the required number of genuine marks and every
one of those marks has one of the exact 455/545/554/555 physical supports. -/
theorem supplied_root_attaching_geometry (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hdegree : colorDegree c q r = 16) :
    H c r - 43 ≤ (rootBlockMarks c r q).card ∧
      ∀ x ∈ rootBlockMarks c r q,
        15 ≤ colorDegree c q x ∧ AttachingSupportGeometry c r q x := by
  refine ⟨rootBlockMarks_card_ge_sub c r q hdegree, ?_⟩
  intro x hx
  have h := rootBlockMarks_high c r q x hx
  exact ⟨h.2, genuine_high_attaching_support_geometry c hc r q x h.1 h.2⟩

/-- The three supplied-root H cutoffs force respectively five, four or three
genuine marks in every size-16 block. -/
theorem supplied_ABD_mark_counts (c : Host) (r : Fin 60) (q : FourColor)
    (hdegree : colorDegree c q r = 16) :
    (48 ≤ H c r → 5 ≤ (rootBlockMarks c r q).card) ∧
    (47 ≤ H c r → 4 ≤ (rootBlockMarks c r q).card) ∧
    (46 ≤ H c r → 3 ≤ (rootBlockMarks c r q).card) := by
  have := rootBlockMarks_lower_bound c r q hdegree
  omega

theorem supplied_ABD_has_attaching_mark (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hdegree : colorDegree c q r = 16)
    (hselected : 46 ≤ H c r) :
    ∃ x ∈ colorNeighborhood c q r,
      15 ≤ colorDegree c q x ∧ AttachingSupportGeometry c r q x := by
  classical
  have hpositive : 0 < (rootBlockMarks c r q).card := by
    have := (supplied_ABD_mark_counts c r q hdegree).2.2 hselected
    omega
  obtain ⟨x, hx⟩ := card_pos.mp hpositive
  have h := rootBlockMarks_high c r q x hx
  exact ⟨x, h.1, h.2, genuine_high_attaching_support_geometry c hc r q x h.1 h.2⟩


/-- A15-cell omits44 of the root's59 physical neighbors. -/
theorem rootBlockMarks_lower_bound_fifteen (c : Host) (r : Fin 60) (q : FourColor)
    (hdegree : colorDegree c q r = 15) : H c r ≤ (rootBlockMarks c r q).card + 44 := by
  have hsub : colorNeighborhood c q r ∪ Incoming c r ⊆
      (univ : Finset (Fin 60)).erase r := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_erase.mpr ⟨((mem_colorNeighborhood c q r v).mp hv).1, mem_univ _⟩
    · exact mem_erase.mpr ⟨((mem_highOwnNeighborSupport c r v).mp hv).1, mem_univ _⟩
  have hcard := card_le_card hsub
  have hidentity := card_union_add_card_inter (colorNeighborhood c q r) (Incoming c r)
  have hblock : (colorNeighborhood c q r).card = 15 := hdegree
  have hincoming : (Incoming c r).card = H c r := rfl
  have houtside : ((univ : Finset (Fin 60)).erase r).card = 59 := by simp
  change _ + (rootBlockMarks c r q).card = _ at hidentity
  omega

/-- Any E-bound violation supplies a genuine mark in any selected15-cell. -/
theorem supplied_E_has_attaching_mark (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (q : FourColor) (hdegree : colorDegree c q r = 15)
    (hselected : 45 ≤ H c r) :
    ∃ x ∈ colorNeighborhood c q r,
      15 ≤ colorDegree c q x ∧ AttachingSupportGeometry c r q x := by
  have hpositive : 0 < (rootBlockMarks c r q).card := by
    have := rootBlockMarks_lower_bound_fifteen c r q hdegree
    omega
  obtain ⟨x, hx⟩ := card_pos.mp hpositive
  have h := rootBlockMarks_high c r q x hx
  exact ⟨x, h.1, h.2, genuine_high_attaching_support_geometry c hc r q x h.1 h.2⟩

#print axioms genuine_high_attaching_support_geometry
#print axioms supplied_ABD_has_attaching_mark
#print axioms supplied_E_has_attaching_mark
end UniformK60.ClassificationGeometry
