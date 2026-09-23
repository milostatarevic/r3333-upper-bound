import Ramsey61.UniformCases

namespace Ramsey61
open Finset

/-- The two colors left after removing two distinct physical colors. -/
theorem fourColor_two_remaining (p q : FourColor) (hne : p ≠ q) :
    ∃ a b : FourColor, ∀ z : FourColor, z ≠ p → z ≠ q → z = a ∨ z = b := by
  revert hne q p
  decide

/-- Intersecting neighborhoods of two different colors leaves a genuinely
 two-colored set, with the original host vertices and coloring unchanged. -/
theorem different_color_intersection_le_five (c : Host)
    (hc : NoMonochromaticTriangle c) (p q : FourColor) (hne : p ≠ q)
    (r x : Fin 61) :
    (colorNeighborhood c p r ∩ colorNeighborhood c q x).card ≤ 5 := by
  obtain ⟨a, b, hab⟩ := fourColor_two_remaining p q hne
  apply twoColorFinset_card_le_five c hc (p := a) (q := b)
  intro y hy z hz hyz
  exact hab (c y z)
    (neighborhood_avoids_own_color c hc (mem_inter.mp hy).1 (mem_inter.mp hz).1 hyz)
    (neighborhood_avoids_own_color c hc (mem_inter.mp hy).2 (mem_inter.mp hz).2 hyz)

/-- A degree-16 attaching neighborhood meeting the root in its own color
has five vertices in each of the other three root cells. -/
theorem degree_sixteen_cross_intersection (c : Host)
    (hc : NoMonochromaticTriangle c) (q : FourColor) (r x : Fin 61)
    (hx : x ∈ colorNeighborhood c q r) (hd : colorDegree c q x = 16)
    (p : FourColor) (hp : p ≠ q) :
    (colorNeighborhood c q x ∩ colorNeighborhood c p r).card = 5 := by
  classical
  let S := (colorNeighborhood c q x).erase r
  let K := (Finset.univ : Finset FourColor).erase q
  let f (k : FourColor) := S.filter fun y => c r y = k
  have hx' := (mem_colorNeighborhood c q r x).mp hx
  have hr : r ∈ colorNeighborhood c q x := by
    exact (colorNeighborhood_symm c q r x hx'.1.symm).mp hx
  have hScard : S.card = 15 := by
    have h := card_erase_add_one hr
    change S.card + 1 = colorDegree c q x at h
    omega
  have havoid : ∀ y ∈ S, c r y ≠ q := by
    intro y hy hcolor
    have hy' := mem_erase.mp hy
    have hxy := (mem_colorNeighborhood c q x y).mp hy'.2
    exact hc r x y ⟨hx'.1.symm, hy'.1.symm, hxy.1.symm⟩
      ⟨hx'.2.trans hcolor.symm, hcolor.trans hxy.2.symm⟩
  have hpartition : S.card = ∑ k ∈ K, (f k).card := by
    exact card_eq_sum_card_fiberwise (fun y hy =>
      mem_erase.mpr ⟨havoid y hy, mem_univ _⟩)
  have hfeq (k : FourColor) :
      f k = colorNeighborhood c q x ∩ colorNeighborhood c k r := by
    ext y
    simp only [f, S, mem_filter, mem_erase, mem_inter, mem_colorNeighborhood]
    tauto
  have hbound : ∀ k ∈ K, (f k).card ≤ 5 := by
    intro k hk
    rw [hfeq]
    exact different_color_intersection_le_five c hc q k
      (Ne.symm (mem_erase.mp hk).1) x r
  have hKcard : K.card = 3 := by
    simp [K, FourColor]
  have hsum : (∑ k ∈ K, (f k).card) = ∑ _k ∈ K, 5 := by
    rw [← hpartition, hScard]
    simp [hKcard]
  have h := (sum_eq_sum_iff_of_le hbound).mp hsum p (mem_erase.mpr ⟨hp, mem_univ _⟩)
  simpa [hfeq] using h

/-- The precise physical regular-overlap guard used by the finite G argument.
The names p and q denote globally fixed, distinct physical colors. -/
structure RegularOverlapGuard (c : Host) (r : Fin 61) (p q : FourColor) : Prop where
  colors_distinct : p ≠ q
  first_root_degree : colorDegree c p r = 16
  second_root_degree : colorDegree c q r = 16
  other_root_degrees : ∀ a, a ≠ p → a ≠ q → colorDegree c a r = 14
  eligible_root : 32 ≤ H c r
  first_fibers : ∀ x ∈ colorNeighborhood c p r,
    (colorNeighborhood c p x ∩ colorNeighborhood c q r).card = 5
  second_fibers : ∀ y ∈ colorNeighborhood c q r,
    (colorNeighborhood c q y ∩ colorNeighborhood c p r).card = 5
  first_opposite_high : ∀ x ∈ colorNeighborhood c p r, 15 ≤ colorDegree c q x
  second_opposite_high : ∀ y ∈ colorNeighborhood c q r, 15 ≤ colorDegree c p y

/-- A uniform host supplies exactly G, at any chosen root, with the same
vertices and colors. No catalogue, bijection or finite-cover premise is used. -/
theorem uniform_host_has_regular_overlap (c : Host)
    (hc : NoMonochromaticTriangle c) (hu : UniformCommonHighPair c) (r : Fin 61) :
    ∃ p q : FourColor, RegularOverlapGuard c r p q := by
  classical
  obtain ⟨high, hcard, hdegrees⟩ := hu
  obtain ⟨p, q, hpq, heq⟩ := Finset.card_eq_two.mp hcard
  have hp : p ∈ high := by rw [heq]; simp
  have hq : q ∈ high := by rw [heq]; simp
  have hpdeg (x : Fin 61) : colorDegree c p x = 16 := by
    rw [hdegrees]; simp [hp]
  have hqdeg (x : Fin 61) : colorDegree c q x = 16 := by
    rw [hdegrees]; simp [hq]
  have hw : W c r = 32 := by
    unfold W criticalDegreeMass
    simp only [hdegrees]
    have hterm (a : FourColor) :
        (if 15 ≤ (if a ∈ high then 16 else 14) then
          (if a ∈ high then 16 else 14) else 0) = if a ∈ high then 16 else 0 := by
      by_cases ha : a ∈ high <;> simp [ha]
    simp only [hterm]
    simp [hcard]
  have hincoming : Incoming c r = Own c r := by
    ext x
    simp only [Incoming, Own, highOwnNeighborSupport, incomingHighOwnSupport,
      mem_filter, mem_univ, true_and]
    rw [c.color_symm x r, hdegrees x (c r x), hdegrees r (c r x)]
  have hh : H c r = 32 := by
    change (Incoming c r).card = 32
    rw [hincoming, ← W_eq_own_card, hw]
  refine ⟨p, q, hpq, hpdeg r, hqdeg r, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · intro a hap haq
    rw [hdegrees, heq]
    simp [hap, haq]
  · intro x hx
    exact degree_sixteen_cross_intersection c hc p r x hx (hpdeg x) q hpq.symm
  · intro y hy
    exact degree_sixteen_cross_intersection c hc q r y hy (hqdeg y) p hpq
  · intro x hx; rw [hqdeg]; omega
  · intro y hy; rw [hpdeg]; omega

end Ramsey61
