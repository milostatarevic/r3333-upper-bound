import Ramsey61.Selector
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Ramsey61
open Finset

/-- A common two-color high pair, with the actual61 host vertices unchanged. -/
def UniformCommonHighPair (c : Host) : Prop := ∃ high : Finset FourColor,
  high.card = 2 ∧ ∀ v q, colorDegree c q v = if q ∈ high then 16 else 14


/-- Vertices low in one fixed physical color in the synchronized C/E branch. -/
def lowColorVertices (c : Host) (q : FourColor) : Finset (Fin 61) :=
  Finset.univ.filter fun v => colorDegree c q v = 14

@[simp] theorem mem_lowColorVertices (c : Host) (q : FourColor) (v : Fin 61) :
    v ∈ lowColorVertices c q ↔ colorDegree c q v = 14 := by
  simp [lowColorVertices]

theorem synchronized_degree_cases (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) (q : FourColor) (v : Fin 61) :
    colorDegree c q v = 14 ∨ colorDegree c q v = 15 ∨ colorDegree c q v = 16 := by
  rcases sync.1 v with hC | hE
  · rcases W32_degree_cases c hc v hC q with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl (W60_degree_cases c hc v hE q))

theorem synchronized_low_neighborhood_closed (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (v : Fin 61) (hv : v ∈ lowColorVertices c q) :
    colorNeighborhood c q v ⊆ lowColorVertices c q := by
  intro u hu
  have hv14 := (mem_lowColorVertices c q v).mp hv
  have hedge := (mem_colorNeighborhood c q v u).mp hu
  have he := synchronized_endpoint_highness c sync v u hedge.1
  rw [hedge.2] at he
  have hnot : ¬15 ≤ colorDegree c q u := by
    intro h; have := he.mpr h; omega
  have hcases := synchronized_degree_cases c hc sync q u
  apply (mem_lowColorVertices c q u).mpr
  omega

theorem synchronized_high_neighborhood_closed (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (v : Fin 61) (hv : v ∈ (lowColorVertices c q)ᶜ) :
    colorNeighborhood c q v ⊆ (lowColorVertices c q)ᶜ := by
  intro u hu
  have hvne : colorDegree c q v ≠ 14 := by simpa using hv
  have hvhigh : 15 ≤ colorDegree c q v := by
    have := synchronized_degree_cases c hc sync q v; omega
  have hedge := (mem_colorNeighborhood c q v u).mp hu
  have he := synchronized_endpoint_highness c sync v u hedge.1
  rw [hedge.2] at he
  have hu15 := he.mp hvhigh
  have hune : colorDegree c q u ≠ 14 := by omega
  simpa using hune

/-- The two color-neighborhoods of an edge of that color are disjoint. -/
theorem colorNeighborhoods_disjoint_of_edge (c : Host)
    (hc : NoMonochromaticTriangle c) (q : FourColor) (v u : Fin 61)
    (hu : u ∈ colorNeighborhood c q v) :
    Disjoint (colorNeighborhood c q v) (colorNeighborhood c q u) := by
  apply Finset.disjoint_left.mpr
  intro x hxv hxu
  have huv := (mem_colorNeighborhood c q v u).mp hu
  have hxv' := (mem_colorNeighborhood c q v x).mp hxv
  have hxu' := (mem_colorNeighborhood c q u x).mp hxu
  exact hc v u x ⟨huv.1.symm, hxv'.1.symm, hxu'.1.symm⟩
    ⟨huv.2.trans hxv'.2.symm, hxv'.2.trans hxu'.2.symm⟩

/-- A nonempty closed triangle-free color graph of minimum degree d has
at least 2d vertices. The set contains actual host vertices throughout. -/
theorem closed_color_set_card_lower (c : Host)
    (hc : NoMonochromaticTriangle c) (q : FourColor)
    (S : Finset (Fin 61)) (d : Nat) (hd : 0 < d) (hne : S.Nonempty)
    (hdegree : ∀ v ∈ S, d ≤ colorDegree c q v)
    (hclosed : ∀ v ∈ S, colorNeighborhood c q v ⊆ S) :
    2 * d ≤ S.card := by
  obtain ⟨v, hv⟩ := hne
  have hdv := hdegree v hv
  have hpos : 0 < (colorNeighborhood c q v).card := by
    change 0 < colorDegree c q v; omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have hus := hclosed v hv hu
  have hdu := hdegree u hus
  have hdis := colorNeighborhoods_disjoint_of_edge c hc q v u hu
  have hsub : colorNeighborhood c q v ∪ colorNeighborhood c q u ⊆ S :=
    Finset.union_subset (hclosed v hv) (hclosed u hus)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hcard
  change colorDegree c q v + colorDegree c q u ≤ S.card at hcard
  omega

theorem synchronized_nonempty_low_card (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hne : (lowColorVertices c q).Nonempty) :
    28 ≤ (lowColorVertices c q).card := by
  apply closed_color_set_card_lower c hc q _ 14 (by decide) hne
  · intro v hv; rw [(mem_lowColorVertices c q v).mp hv]
  · exact fun v hv => synchronized_low_neighborhood_closed c hc sync q v hv

theorem synchronized_nonempty_high_card (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hne : ((lowColorVertices c q)ᶜ).Nonempty) :
    30 ≤ ((lowColorVertices c q)ᶜ).card := by
  apply closed_color_set_card_lower c hc q _ 15 (by decide) hne
  · intro v hv
    have hne14 : colorDegree c q v ≠ 14 := by simpa using hv
    have := synchronized_degree_cases c hc sync q v
    omega
  · exact fun v hv => synchronized_high_neighborhood_closed c hc sync q v hv

/-- This is the exact size interval needed by the dense bipartiteness step. -/
theorem synchronized_proper_low_card (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hlow : (lowColorVertices c q).Nonempty)
    (hhigh : ((lowColorVertices c q)ᶜ).Nonempty) :
    28 ≤ (lowColorVertices c q).card ∧ (lowColorVertices c q).card ≤ 31 := by
  have hl := synchronized_nonempty_low_card c hc sync q hlow
  have hh := synchronized_nonempty_high_card c hc sync q hhigh
  have heq := Finset.card_add_card_compl (lowColorVertices c q)
  simp only [Fintype.card_fin] at heq
  omega

theorem colorGraph_degree_eq (c : Host) (q : FourColor) (v : Fin 61) :
    letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
    (colorGraph c q).degree v = colorDegree c q v := by
  classical
  unfold SimpleGraph.degree colorDegree
  congr 1
  ext u
  simp [SimpleGraph.mem_neighborFinset, colorGraph, ne_comm]

/-- The induced low-color graph really is 14-regular: restricting the
vertex set drops no neighbor and does not change any edge color. -/
theorem synchronized_low_induced_degree (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (v : {v // v ∈ lowColorVertices c q}) :
    letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
    ((colorGraph c q).induce (↑(lowColorVertices c q) : Set (Fin 61))).degree v = 14 := by
  classical
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  have hclosed : (colorGraph c q).neighborSet v ⊆
      (↑(lowColorVertices c q) : Set (Fin 61)) := by
    intro u hu
    exact synchronized_low_neighborhood_closed c hc sync q v v.property
      ((mem_colorNeighborhood c q v u).mpr ⟨hu.1.symm, hu.2⟩)
  have heq := SimpleGraph.degree_induce_of_neighborSet_subset hclosed
  convert heq.trans ((colorGraph_degree_eq c q v).trans
    ((mem_lowColorVertices c q v).mp v.property)) using 1
  congr 1
  exact Subsingleton.elim _ _

theorem synchronized_high_induced_degree (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (v : {v // v ∈ (lowColorVertices c q)ᶜ}) :
    letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
    ((colorGraph c q).induce (↑((lowColorVertices c q)ᶜ) : Set (Fin 61))).degree v =
      colorDegree c q v := by
  classical
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  have hclosed : (colorGraph c q).neighborSet v ⊆
      (↑((lowColorVertices c q)ᶜ) : Set (Fin 61)) := by
    intro u hu
    exact synchronized_high_neighborhood_closed c hc sync q v v.property
      ((mem_colorNeighborhood c q v u).mpr ⟨hu.1.symm, hu.2⟩)
  convert (SimpleGraph.degree_induce_of_neighborSet_subset hclosed).trans
    (colorGraph_degree_eq c q v) using 1
  congr 1
  exact Subsingleton.elim _ _

/-- Both nonempty parts meet the strict integer density inequality used
by the remaining triangle-free bipartiteness argument. -/
theorem synchronized_proper_cut_dense (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hlow : (lowColorVertices c q).Nonempty)
    (hhigh : ((lowColorVertices c q)ᶜ).Nonempty) :
    2 * (lowColorVertices c q).card < 5 * 14 ∧
      2 * ((lowColorVertices c q)ᶜ).card < 5 * 15 := by
  have hbounds := synchronized_proper_low_card c hc sync q hlow hhigh
  have heq := Finset.card_add_card_compl (lowColorVertices c q)
  simp only [Fintype.card_fin] at heq
  omega

/-- A color cannot be 15-regular on the odd host of size 61. -/
theorem not_all_color_degree_fifteen (c : Host) (q : FourColor) :
    ¬ ∀ v, colorDegree c q v = 15 := by
  classical
  intro h
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  have hd : ∀ v, (colorGraph c q).degree v = 15 := by
    intro v; rw [colorGraph_degree_eq]; exact h v
  have hs := (colorGraph c q).sum_degrees_eq_twice_card_edges
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hs
  omega

/-- The all-E alternative is excluded by the handshake identity alone. -/
theorem not_all_E (c : Host) (hc : NoMonochromaticTriangle c) :
    ¬ ∀ v, W c v = 60 := by
  intro he
  exact not_all_color_degree_fifteen c (false, false)
    (fun v => W60_degree_cases c hc v (he v) (false, false))

theorem synchronized_exists_C (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) : ∃ v, W c v = 32 := by
  by_contra h
  push Not at h
  exact not_all_E c hc fun v => (sync.1 v).resolve_left (h v)

theorem C_exists_low_color (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 61) (hv : W c v = 32) : ∃ q, colorDegree c q v = 14 := by
  by_contra h
  push Not at h
  have h16 : ∀ q, colorDegree c q v = 16 := by
    intro q; exact (W32_degree_cases c hc v hv q).resolve_left (h q)
  have hs := fourColor_degree_sum c v
  simp [h16] at hs

theorem C_high_color_card (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 61) (hv : W c v = 32) :
    (Finset.univ.filter fun q : FourColor => colorDegree c q v = 16).card = 2 := by
  have hsum := fourColor_degree_sum c v
  have ha := W32_degree_cases c hc v hv (false, false)
  have hb := W32_degree_cases c hc v hv (false, true)
  have hd := W32_degree_cases c hc v hv (true, false)
  have he := W32_degree_cases c hc v hv (true, true)
  have hbcard := Finset.sum_boole (R := Nat)
    (fun q : FourColor => colorDegree c q v = 16) Finset.univ
  simp only [Nat.cast_id] at hbcard
  rw [← hbcard]
  simp only [FourColor, Fintype.sum_prod_type, Fintype.sum_bool]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hd with hd | hd <;> rcases he with he | he <;>
    simp_all

/-- Once proper low-color cuts have been excluded, the uniform branch
follows without any extra graph or SAT premise. Its conclusion is exactly
the mathematical body of `UniformCommonHighPair`. -/
theorem synchronized_uniform_of_no_proper_low_set (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (noProper : ∀ q, lowColorVertices c q = ∅ ∨ lowColorVertices c q = Finset.univ) :
    ∃ high : Finset FourColor, high.card = 2 ∧
      ∀ v q, colorDegree c q v = if q ∈ high then 16 else 14 := by
  classical
  obtain ⟨r, hr⟩ := synchronized_exists_C c hc sync
  obtain ⟨q₀, hq₀⟩ := C_exists_low_color c hc r hr
  have full : lowColorVertices c q₀ = Finset.univ := by
    rcases noProper q₀ with hempty | hfull
    · have hm := (mem_lowColorVertices c q₀ r).mpr hq₀
      rw [hempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
    · exact hfull
  have allC : ∀ v, W c v = 32 := by
    intro v
    rcases sync.1 v with hC | hE
    · exact hC
    · have hlow : colorDegree c q₀ v = 14 := by
        apply (mem_lowColorVertices c q₀ v).mp
        rw [full]; exact Finset.mem_univ v
      have h15 := W60_degree_cases c hc v hE q₀
      omega
  let high := Finset.univ.filter fun q : FourColor => colorDegree c q r = 16
  refine ⟨high, C_high_color_card c hc r hr, ?_⟩
  intro v q
  by_cases hmem : q ∈ high
  · rw [if_pos hmem]
    have hr16 : colorDegree c q r = 16 := by simpa [high] using hmem
    have empty : lowColorVertices c q = ∅ := by
      rcases noProper q with hempty | hfull
      · exact hempty
      · have hm : r ∈ lowColorVertices c q := by rw [hfull]; exact Finset.mem_univ r
        have hr14 := (mem_lowColorVertices c q r).mp hm
        omega
    have hn14 : colorDegree c q v ≠ 14 := by
      intro h; have hm := (mem_lowColorVertices c q v).mpr h
      rw [empty] at hm; exact Finset.notMem_empty _ hm
    exact (W32_degree_cases c hc v (allC v) q).resolve_left hn14
  · rw [if_neg hmem]
    have hrnot16 : colorDegree c q r ≠ 16 := by simpa [high] using hmem
    have hr14 := (W32_degree_cases c hc r hr q).resolve_right hrnot16
    rcases noProper q with hempty | hfull
    · have hm := (mem_lowColorVertices c q r).mpr hr14
      rw [hempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
    · apply (mem_lowColorVertices c q v).mp
      rw [hfull]; exact Finset.mem_univ v


end Ramsey61
