import UniformK60.BalancedHomogeneous

set_option autoImplicit false
namespace UniformK60.BalancedStructure
open Ramsey61 Finset

/-!
The K60 common-pair argument. A second use of neighborhood homogeneity
replaces the K61 argument that required every critical degree to be16.
All neighborhoods below consist of actual vertices of the same K60.
-/

/-- Across a critical edge, a high color at the endpoint is high at the
root. Otherwise its neighborhood is confined to two root groups, each
with at most five vertices. -/
theorem high_along_critical (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : Synchronized c) (r v : Fin 60) (hne : v ≠ r)
    (hedge : 15 ≤ colorDegree c (c r v) r)
    (j : FourColor) (hvj : 15 ≤ colorDegree c j v) :
    15 ≤ colorDegree c j r := by
  classical
  by_contra nothigh
  let i : FourColor := c r v
  have hri : 15 ≤ colorDegree c i r := hedge
  have hvX : v ∈ colorNeighborhood c i r :=
    (mem_colorNeighborhood c i r v).mpr ⟨hne, rfl⟩
  have hvi : 15 ≤ colorDegree c i v :=
    (synchronized_endpoint_highness c sync r v hne).mp hedge
  have hji : j ≠ i := by
    intro he
    exact nothigh (by simpa only [he] using hri)
  have hi : i ∈ criticalColors c r := (mem_criticalColors c r i).mpr hri
  have hcardr := criticalColors_card_two c hc r (sync.1 r)
  have hcardv := criticalColors_card_two c hc v (sync.1 v)
  have hkerase : ((criticalColors c r).erase i).Nonempty := by
    apply card_pos.mp
    have hcard := card_erase_add_one hi
    omega
  obtain ⟨k, hk⟩ := hkerase
  have hki : k ≠ i := (mem_erase.mp hk).1
  have hkr : 15 ≤ colorDegree c k r :=
    (mem_criticalColors c r k).mp (mem_erase.mp hk).2
  have hkj : k ≠ j := by
    intro he
    exact nothigh (by simpa only [he] using hkr)
  have hpairs : ({i, j} : Finset FourColor) ⊆ criticalColors c v := by
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with hqi | hqj
    · exact (mem_criticalColors c v q).mpr (by simpa only [hqi] using hvi)
    · exact (mem_criticalColors c v q).mpr (by simpa only [hqj] using hvj)
  have hpair : ({i, j} : Finset FourColor) = criticalColors c v := by
    apply eq_of_subset_of_card_le hpairs
    rw [hcardv]
    simp [hji.symm]
  have hvnotk : ¬15 ≤ colorDegree c k v := by
    intro hhigh
    have hmem := (mem_criticalColors c v k).mpr hhigh
    rw [← hpair] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    exact hmem.elim hki hkj

  -- A color-j neighbor inside X lies both in X and in the new critical
  -- neighborhood of v, so homogeneity transports the missing k flag.
  have hinside := (inside_degree_bounds c hc r i j hji v hvX).1
  obtain ⟨x, hx⟩ := card_pos.mp
    (show 0 < (inside c r i j v).card by omega)
  have hxS : x ∈ colorNeighborhood c j v := (mem_inter.mp hx).1
  have hxX : x ∈ colorNeighborhood c i r := (mem_inter.mp hx).2
  have hxnotk : ¬15 ≤ colorDegree c k x := by
    intro hxhigh
    exact hvnotk ((critical_homogeneous c hc sync r i hri v hvX x hxX k).mpr hxhigh)
  have every_notk : ∀ u ∈ colorNeighborhood c j v, ¬15 ≤ colorDegree c k u := by
    intro u hu huhigh
    exact hxnotk ((critical_homogeneous c hc sync v j hvj x hxS u hu k).mpr huhigh)

  have noRoot : r ∉ colorNeighborhood c j v := by
    intro hr
    have he := (mem_colorNeighborhood c j v r).mp hr
    exact hji ((c.color_symm r v).trans he.2).symm
  let K : Finset FourColor := ((univ : Finset FourColor).erase j).erase k
  have hK : K.card = 2 := by simp [K, FourColor, hkj]
  have allowed : ∀ u ∈ colorNeighborhood c j v, c r u ∈ K := by
    intro u hu
    have huS := (mem_colorNeighborhood c j v u).mp hu
    have huroot : u ≠ r := by
      intro he
      subst u
      exact noRoot hu
    have huj : 15 ≤ colorDegree c j u := by
      have hrec := synchronized_endpoint_highness c sync v u huS.1
      rw [huS.2] at hrec
      exact hrec.mp hvj
    have notj : c r u ≠ j := by
      intro he
      have hrec := synchronized_endpoint_highness c sync r u huroot
      rw [he] at hrec
      exact nothigh (hrec.mpr huj)
    have notk : c r u ≠ k := by
      intro he
      have hrec := synchronized_endpoint_highness c sync r u huroot
      rw [he] at hrec
      exact every_notk u hu (hrec.mp hkr)
    exact mem_erase.mpr ⟨notk, mem_erase.mpr ⟨notj, mem_univ _⟩⟩
  have hp := card_eq_sum_card_fiberwise (s := colorNeighborhood c j v)
    (t := K) (f := fun u => c r u) allowed
  have bound : ∀ q ∈ K,
      ((colorNeighborhood c j v).filter (fun u => c r u = q)).card ≤ 5 := by
    intro q hq
    have hqj : q ≠ j := (mem_erase.mp (mem_erase.mp hq).2).1
    have sub : (colorNeighborhood c j v).filter (fun u => c r u = q) ⊆
        colorNeighborhood c j v ∩ colorNeighborhood c q r := by
      intro u hu
      obtain ⟨huN, he⟩ := mem_filter.mp hu
      refine mem_inter.mpr ⟨huN, (mem_colorNeighborhood c q r u).mpr ⟨?_, he⟩⟩
      intro heq
      subst u
      exact noRoot huN
    exact (card_le_card sub).trans (inter_le_five c hc j q hqj.symm v r)
  have hle : colorDegree c j v ≤ 10 := by
    change (colorNeighborhood c j v).card ≤ 10
    rw [hp]
    calc
      _ ≤ ∑ _q ∈ K, 5 := sum_le_sum bound
      _ = 10 := by simp [hK]
  omega

/-- All critical-color flags agree across an actual critical edge. -/
theorem critical_pair_preserved (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : Synchronized c) (r v : Fin 60) (hne : v ≠ r)
    (hedge : 15 ≤ colorDegree c (c r v) r) :
    ∀ j : FourColor, (15 ≤ colorDegree c j r ↔ 15 ≤ colorDegree c j v) := by
  have reverse : 15 ≤ colorDegree c (c v r) v := by
    rw [c.color_symm v r]
    exact (synchronized_endpoint_highness c sync r v hne).mp hedge
  intro j
  exact ⟨high_along_critical c hc sync v r hne.symm reverse j,
    high_along_critical c hc sync r v hne hedge j⟩

/-- Any two vertices share a critical neighbor: each has at least31,
and both sets lie in the same60-vertex host. -/
theorem high_flags_global (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : Synchronized c) :
    ∀ u v : Fin 60, ∀ j : FourColor,
      (15 ≤ colorDegree c j u ↔ 15 ≤ colorDegree c j v) := by
  intro u v j
  have own_lower (x : Fin 60) : 31 ≤ (Own c x).card := by
    rw [← W_eq_own_card]
    rcases sync.1 x with h | h <;> omega
  have hu := own_lower u
  have hv := own_lower v
  have hsum := card_union_add_card_inter (Own c u) (Own c v)
  have hbound : (Own c u ∪ Own c v).card ≤ 60 := by
    simpa using card_le_univ (Own c u ∪ Own c v)
  obtain ⟨w, hw⟩ := card_pos.mp
    (show 0 < (Own c u ∩ Own c v).card by omega)
  obtain ⟨hwu, hwv⟩ := mem_inter.mp hw
  have hwu' : w ≠ u ∧ 15 ≤ colorDegree c (c u w) u := by
    simpa [Own, incomingHighOwnSupport, c.color_symm w u] using hwu
  have hwv' : w ≠ v ∧ 15 ≤ colorDegree c (c v w) v := by
    simpa [Own, incomingHighOwnSupport, c.color_symm w v] using hwv
  exact (critical_pair_preserved c hc sync u w hwu'.1 hwu'.2 j).trans
    (critical_pair_preserved c hc sync v w hwv'.1 hwv'.2 j).symm

/-- A synchronized mixed C1/C2 host has one common two-element critical
pair. This theorem needs no critical-template catalogue or SAT premise. -/
theorem synchronized_common_pair (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : Synchronized c) :
    ∃ high : Finset FourColor, high.card = 2 ∧
      ∀ v : Fin 60, criticalColors c v = high := by
  refine ⟨criticalColors c 0, criticalColors_card_two c hc 0 (sync.1 0), ?_⟩
  intro v
  ext j
  simp only [mem_criticalColors]
  exact high_flags_global c hc sync v 0 j

#print axioms high_along_critical
#print axioms high_flags_global
#print axioms synchronized_common_pair
end UniformK60.BalancedStructure
