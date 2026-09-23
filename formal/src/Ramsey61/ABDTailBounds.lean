import Ramsey61.ABDExtraction

namespace Ramsey61
open Finset

def criticalTail (c : Host) (r : Fin 61) (q : FourColor) : Finset (Fin 61) :=
  (univ.erase r) \ colorNeighborhood c q r

def tailDegree (c : Host) (r : Fin 61) (q : FourColor) (u : Fin 61) (p : FourColor) : Nat :=
  (colorNeighborhood c p u ∩ criticalTail c r q).card

def lowCellDegree (c : Host) (r : Fin 61) (q : FourColor) (u : Fin 61) (p : FourColor) : Nat :=
  (colorNeighborhood c p u ∩ colorNeighborhood c q r).card

/-- The elementary degree lower bound is independent of any classification. -/
theorem fourColor_colorDegree_ge_twelve (c : Host) (hc : NoMonochromaticTriangle c)
    (u : Fin 61) (q : FourColor) : 12 ≤ colorDegree c q u := by
  classical
  let K := (univ : Finset FourColor).erase q
  have hcard : K.card = 3 := by simp [K, FourColor]
  have hother : (∑ p ∈ K, colorDegree c p u) ≤ 48 := calc
    _ ≤ ∑ _p ∈ K, 16 := sum_le_sum fun p _ => fourColor_colorDegree_le_sixteen c hc p u
    _ = 48 := by simp [hcard]
  have hsum := sum_colorDegree_eq_card_sub_one c u
  have hsplit := (univ : Finset FourColor).sum_erase_add (fun p => colorDegree c p u) (mem_univ q)
  change (∑ p ∈ K, colorDegree c p u) + colorDegree c q u = _ at hsplit
  simp only [Fintype.card_fin] at hsum
  omega

theorem fourColor_two_degrees_ge_twenty_eight (c : Host) (hc : NoMonochromaticTriangle c)
    (u : Fin 61) (q p : FourColor) (hp : p ≠ q) :
    28 ≤ colorDegree c q u + colorDegree c p u := by
  classical
  let K := (univ : Finset FourColor).erase q
  have hmem : p ∈ K := mem_erase.mpr ⟨hp, mem_univ _⟩
  have hcard : (K.erase p).card = 2 := by simp [K, FourColor, hp]
  have hother : (∑ a ∈ K.erase p, colorDegree c a u) ≤ 32 := calc
    _ ≤ ∑ _a ∈ K.erase p, 16 := sum_le_sum fun a _ => fourColor_colorDegree_le_sixteen c hc a u
    _ = 32 := by simp [hcard]
  have hsum := sum_colorDegree_eq_card_sub_one c u
  have hsplit := (univ : Finset FourColor).sum_erase_add (fun a => colorDegree c a u) (mem_univ q)
  have hsplit' := K.sum_erase_add (fun a => colorDegree c a u) hmem
  change (∑ a ∈ K, colorDegree c a u) + colorDegree c q u = _ at hsplit
  simp only [Fintype.card_fin] at hsum
  omega

/-- Exact physical degree accounting over the retained tail, full low cell,
and the restored root. All three sets retain their original host vertices. -/
theorem tail_low_root_partition (c : Host) (r : Fin 61) (q : FourColor)
    (u : Fin 61) (p : FourColor) :
    tailDegree c r q u p + lowCellDegree c r q u p +
      (if r ∈ colorNeighborhood c p u then 1 else 0) = colorDegree c p u := by
  classical
  let N := colorNeighborhood c p u
  let F := colorNeighborhood c q r
  have hroot : r ∉ F := by simp [F, mem_colorNeighborhood]
  have htail : N.erase r \ F = N ∩ criticalTail c r q := by
    ext v
    simp only [criticalTail, mem_sdiff, mem_erase, mem_inter, mem_univ, and_true]
    tauto
  have hlow : N.erase r ∩ F = N ∩ F := by
    ext v
    have hn : v ∈ F → v ≠ r := by intro hv heq; subst v; exact hroot hv
    simp only [mem_inter, mem_erase]
    tauto
  have hsplit := card_sdiff_add_card_inter (N.erase r) F
  rw [htail, hlow] at hsplit
  change tailDegree c r q u p + lowCellDegree c r q u p = (N.erase r).card at hsplit
  change _ + (if r ∈ N then 1 else 0) = N.card
  by_cases hr : r ∈ N
  · have he := card_erase_add_one hr
    rw [if_pos hr]
    omega
  · rw [if_neg hr, add_zero, hsplit, erase_eq_of_notMem hr]

theorem lowCellDegree_le_five (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (p : FourColor) (hp : p ≠ q) :
    lowCellDegree c r q u p ≤ 5 :=
  different_color_intersection_le_five c hc p q hp u r

/-- Each foreign color accounts for at least m-11 of a free vertex's
neighbors inside an actual low cell of size m. -/
theorem free_vertex_lowCellDegree_lower (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (hu : u ∈ colorNeighborhood c q r)
    (p : FourColor) (hp : p ≠ q) :
    colorDegree c q r ≤ lowCellDegree c r q u p + 11 := by
  classical
  let K := (univ : Finset FourColor).erase q
  have hmem : p ∈ K := mem_erase.mpr ⟨hp, mem_univ _⟩
  have hcard : (K.erase p).card = 2 := by simp [K, FourColor, hp]
  have hother : (∑ a ∈ K.erase p, lowCellDegree c r q u a) ≤ 10 := calc
    _ ≤ ∑ _a ∈ K.erase p, 5 := sum_le_sum fun a ha =>
      lowCellDegree_le_five c hc r q u a (mem_erase.mp (mem_erase.mp ha).2).1
    _ = 10 := by simp [hcard]
  have hu' := (mem_colorNeighborhood c q r u).mp hu
  have hr := (colorNeighborhood_symm c q r u hu'.1.symm).mp hu
  have hsum := attachingSupport_partition c hc u q r hr
  have heq (a : FourColor) :
      (attachingSupport c u q r a).card = lowCellDegree c r q u a := by
    simp only [attachingSupport, lowCellDegree, inter_comm]
  simp only [heq] at hsum
  change _ = ∑ a ∈ K, lowCellDegree c r q u a at hsum
  have hsplit := K.sum_erase_add (fun a => lowCellDegree c r q u a) hmem
  omega

theorem free_vertex_own_tail_degree (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (hu : u ∈ colorNeighborhood c q r) :
    tailDegree c r q u q + 1 = colorDegree c q u := by
  have hu' := (mem_colorNeighborhood c q r u).mp hu
  have hr := (colorNeighborhood_symm c q r u hu'.1.symm).mp hu
  have hlow : lowCellDegree c r q u q = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    have h := mem_inter.mp hv
    have hne := ((mem_colorNeighborhood c q u v).mp h.1).1.symm
    exact (neighborhood_avoids_own_color c hc hu h.2 hne)
      ((mem_colorNeighborhood c q u v).mp h.1).2
  have hsplit := tail_low_root_partition c r q u q
  simpa [hr, hlow] using hsplit

theorem free_vertex_foreign_tail_degree (c : Host) (r : Fin 61) (q : FourColor)
    (u : Fin 61) (hu : u ∈ colorNeighborhood c q r) (p : FourColor) (hp : p ≠ q) :
    tailDegree c r q u p + lowCellDegree c r q u p = colorDegree c p u := by
  have hu' := (mem_colorNeighborhood c q r u).mp hu
  have hr : r ∉ colorNeighborhood c p u := by
    intro hr
    have he := ((mem_colorNeighborhood c p u r).mp hr).2
    rw [c.color_symm u r, hu'.2] at he
    exact hp he.symm
  simpa [hr] using tail_low_root_partition c r q u p

/-- Actual free-row intervals and paired lower bounds for the A/B/D tail.
At low-cell sizes12/13/14 the foreign upper bounds are respectively15/14/13. -/
theorem free_vertex_tail_intervals (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (hu : u ∈ colorNeighborhood c q r)
    (p : FourColor) (hp : p ≠ q) :
    11 ≤ tailDegree c r q u q ∧ tailDegree c r q u q ≤ 15 ∧
    7 ≤ tailDegree c r q u p ∧ tailDegree c r q u p + colorDegree c q r ≤ 27 ∧
    22 ≤ tailDegree c r q u q + tailDegree c r q u p := by
  have hzero := free_vertex_own_tail_degree c hc r q u hu
  have hpdegree := free_vertex_foreign_tail_degree c r q u hu p hp
  have hilo := free_vertex_lowCellDegree_lower c hc r q u hu p hp
  have hihi := lowCellDegree_le_five c hc r q u p hp
  have hqlo := fourColor_colorDegree_ge_twelve c hc u q
  have hqhi := fourColor_colorDegree_le_sixteen c hc q u
  have hplo := fourColor_colorDegree_ge_twelve c hc u p
  have hphi := fourColor_colorDegree_le_sixteen c hc p u
  have hpair := fourColor_two_degrees_ge_twenty_eight c hc u q p hp
  omega

/-- The free-vertex proxy is necessary for genuine highness; no converse
assertion about a partial-model proxy is made. -/
theorem genuine_high_free_vertex_proxy (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (hu : u ∈ colorNeighborhood c q r)
    (hhigh : 15 ≤ colorDegree c q u) : 14 ≤ tailDegree c r q u q := by
  have := free_vertex_own_tail_degree c hc r q u hu
  omega

theorem tail_vertex_root_color_ne_low (c : Host) (r : Fin 61) (q : FourColor)
    (u : Fin 61) (hu : u ∈ criticalTail c r q) : c r u ≠ q := by
  have h := mem_sdiff.mp hu
  intro hcolor
  exact h.2 ((mem_colorNeighborhood c q r u).mpr ⟨(mem_erase.mp h.1).1, hcolor⟩)

/-- Critical-tail vertices retain at least six neighbors in any non-low
color, and at least seven when the root spoke has a different color. -/
theorem tail_vertex_nonzero_degree_lower (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (p : FourColor) (hp : p ≠ q) :
    6 ≤ tailDegree c r q u p ∧
      (p ≠ c r u → 7 ≤ tailDegree c r q u p) := by
  have hsplit := tail_low_root_partition c r q u p
  have hlo := fourColor_colorDegree_ge_twelve c hc u p
  have hcell := lowCellDegree_le_five c hc r q u p hp
  constructor
  · split_ifs at hsplit <;> omega
  · intro hcolor
    have hr : r ∉ colorNeighborhood c p u := by
      intro hr
      have he := ((mem_colorNeighborhood c p u r).mp hr).2
      rw [c.color_symm u r] at he
      exact hcolor he.symm
    rw [if_neg hr] at hsplit
    omega

/-- A genuinely high critical-tail endpoint satisfies the own-color
tail-degree proxy9, in its actual root-spoke color. -/
theorem genuine_high_tail_vertex_proxy (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (hu : u ∈ criticalTail c r q)
    (hhigh : u ∈ Incoming c r) : 9 ≤ tailDegree c r q u (c r u) := by
  have hp := tail_vertex_root_color_ne_low c r q u hu
  have hd := ((mem_highOwnNeighborSupport c r u).mp hhigh).2
  have hsplit := tail_low_root_partition c r q u (c r u)
  have hcell := lowCellDegree_le_five c hc r q u (c r u) hp
  split_ifs at hsplit <;> omega

def retainedTailAndSupport (c : Host) (r : Fin 61) (q : FourColor)
    (support : Finset (Fin 61)) : Finset (Fin 61) := criticalTail c r q ∪ support

/-- Only the omitted low-cell vertices can be lost from any root-free
physical set. No independence or zero-free property is assumed. -/
theorem rootless_retention_bound (c : Host) (r : Fin 61) (q : FourColor)
    (support : Finset (Fin 61)) (hsupport : support ⊆ colorNeighborhood c q r)
    (A : Finset (Fin 61)) (hroot : r ∉ A) :
    A.card + support.card ≤
      (A ∩ retainedTailAndSupport c r q support).card + colorDegree c q r := by
  classical
  let F := colorNeighborhood c q r
  let R := retainedTailAndSupport c r q support
  have hsub : A \ R ⊆ F \ support := by
    intro u hu
    have h := mem_sdiff.mp hu
    have hne : u ≠ r := by intro heq; subst u; exact hroot h.1
    have hnot := h.2
    simp only [R, retainedTailAndSupport, mem_union, not_or] at hnot
    have hF : u ∈ F := by
      by_contra hnF
      exact hnot.1 (mem_sdiff.mpr ⟨mem_erase.mpr ⟨hne, mem_univ _⟩, hnF⟩)
    exact mem_sdiff.mpr ⟨hF, hnot.2⟩
  have hcard := card_le_card hsub
  have hsplit := card_sdiff_add_card_inter A R
  have hdeleted := card_sdiff_of_subset hsupport
  have hcontained := card_le_card hsupport
  change (F \ support).card = F.card - support.card at hdeleted
  change support.card ≤ F.card at hcontained
  change A.card + support.card ≤ (A ∩ R).card + F.card
  omega

/-- Exact surviving-high count behind the A/B/D proxy total constraints. -/
theorem genuine_high_retention_count (c : Host) (r : Fin 61) (q : FourColor)
    (support : Finset (Fin 61)) (hsupport : support ⊆ colorNeighborhood c q r) :
    H c r + support.card ≤
      (Incoming c r ∩ retainedTailAndSupport c r q support).card + colorDegree c q r := by
  have hroot : r ∉ Incoming c r := by simp [Incoming, mem_highOwnNeighborSupport]
  exact rootless_retention_bound c r q support hsupport (Incoming c r) hroot

/-- With low cells of size12/13/14, the selected H cutoffs leave respectively
36+k,34+k,32+k genuine high vertices in the retained physical graph. -/
theorem supplied_ABD_surviving_high_counts (c : Host) (r : Fin 61) (q : FourColor)
    (support : Finset (Fin 61)) (hsupport : support ⊆ colorNeighborhood c q r) :
    (colorDegree c q r = 12 → 48 ≤ H c r → 36 + support.card ≤
      (Incoming c r ∩ retainedTailAndSupport c r q support).card) ∧
    (colorDegree c q r = 13 → 47 ≤ H c r → 34 + support.card ≤
      (Incoming c r ∩ retainedTailAndSupport c r q support).card) ∧
    (colorDegree c q r = 14 → 46 ≤ H c r → 32 + support.card ≤
      (Incoming c r ∩ retainedTailAndSupport c r q support).card) := by
  have := genuine_high_retention_count c r q support hsupport
  omega

/-- Retained low-color degree of a critical-tail vertex. In A it is at
least k; in B at least k-1, since only m-k free vertices were removed. -/
theorem tail_vertex_retained_low_degree (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 61) (q : FourColor) (u : Fin 61) (hu : u ∈ criticalTail c r q)
    (support : Finset (Fin 61)) (hsupport : support ⊆ colorNeighborhood c q r) :
    12 + support.card ≤
      (colorNeighborhood c q u ∩ retainedTailAndSupport c r q support).card + colorDegree c q r := by
  have hp := tail_vertex_root_color_ne_low c r q u hu
  have hroot : r ∉ colorNeighborhood c q u := by
    intro hr
    have he := ((mem_colorNeighborhood c q u r).mp hr).2
    rw [c.color_symm u r] at he
    exact hp he
  have hretain := rootless_retention_bound c r q support hsupport (colorNeighborhood c q u) hroot
  have hlo := fourColor_colorDegree_ge_twelve c hc u q
  change colorDegree c q u + support.card ≤ _ at hretain
  omega

end Ramsey61
