import UniformK61.BalancedStructureAllC
set_option autoImplicit false
namespace UniformK61.BalancedStructure
open Ramsey61 Finset

/-- A high color at the endpoint of a critical edge cannot be low at its
other endpoint: its neighborhood would split into three sets of size≤5. -/
theorem high_along_critical (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) (allC : ∀v,W c v=32)
    (r v : Fin 61) (hedge : 15≤colorDegree c (c r v) r)
    (j : FourColor) (hvj : 15≤colorDegree c j v) : 15≤colorDegree c j r := by
  by_contra nothigh
  have hrj : colorDegree c j r=14 := by
    have h := W32_degree_cases c hc r (allC r) j
    omega
  have hvj16 : colorDegree c j v=16 := by
    have h := W32_degree_cases c hc v (allC v) j
    omega
  have noRoot : r∉colorNeighborhood c j v := by
    intro hr
    have hcolor := (c.color_symm r v).trans ((mem_colorNeighborhood _ _ _ _).mp hr).2
    rw [hcolor] at hedge
    omega
  have dis : Disjoint (colorNeighborhood c j v) (colorNeighborhood c j r) := by
    apply disjoint_left.mpr
    intro u huv hur
    have ulo := synchronized_low_neighborhood_closed c hc sync j r
      ((mem_lowColorVertices c j r).mpr hrj) hur
    have uhi := synchronized_high_neighborhood_closed c hc sync j v
      (by simp [hvj16]) huv
    exact (mem_compl.mp uhi) ulo
  let K := (univ : Finset FourColor).erase j
  have hK : K.card=3 := by simp [K,FourColor]
  have allowed : ∀u∈colorNeighborhood c j v,c r u∈K := by
    intro u hu
    apply mem_erase.mpr
    refine ⟨?_,mem_univ _⟩
    intro he
    have hur : u∈colorNeighborhood c j r := (mem_colorNeighborhood _ _ _ _).mpr
      ⟨by intro heq;subst u;exact noRoot hu,he⟩
    exact disjoint_left.mp dis hu hur
  have hp := card_eq_sum_card_fiberwise (s:=colorNeighborhood c j v) (t:=K) (f:=fun u => c r u) allowed
  have bound : ∀k∈K,((colorNeighborhood c j v).filter (fun u => c r u=k)).card≤5 := by
    intro k hk
    have hkj := (mem_erase.mp hk).1
    have sub : (colorNeighborhood c j v).filter (fun u => c r u=k) ⊆
        colorNeighborhood c j v ∩ colorNeighborhood c k r := by
      intro u hu
      obtain ⟨huN,he⟩ := mem_filter.mp hu
      exact mem_inter.mpr ⟨huN,(mem_colorNeighborhood _ _ _ _).mpr
        ⟨by intro heq;subst u;exact noRoot huN,he⟩⟩
    exact (card_le_card sub).trans (inter_le_five c hc j k hkj.symm v r)
  have hs := sum_le_sum bound
  have hle : colorDegree c j v≤15 := by
    change (colorNeighborhood c j v).card≤15
    rw [hp]
    calc
      _ ≤ ∑_k∈K,5 := hs
      _ = 15 := by simp [hK]
  omega

theorem critical_pair_preserved (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) (allC : ∀v,W c v=32)
    (r v : Fin 61) (hne : v≠r) (hedge : 15≤colorDegree c (c r v) r) :
    ∀j : FourColor,(15≤colorDegree c j r ↔ 15≤colorDegree c j v) := by
  have reverse : 15≤colorDegree c (c v r) v := by
    rw [c.color_symm v r]
    exact (synchronized_endpoint_highness c sync r v hne).mp hedge
  intro j
  exact ⟨high_along_critical c hc sync allC v r reverse j,
    high_along_critical c hc sync allC r v hedge j⟩

/-- Any two vertices have a common critical neighbor, since their two
32-element neighbor sets lie in the same61-element host. -/
theorem high_flags_global (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) (allC : ∀v,W c v=32) :
    ∀u v : Fin 61,∀j : FourColor,(15≤colorDegree c j u ↔ 15≤colorDegree c j v) := by
  intro u v j
  have hu : (Own c u).card=32 := (W_eq_own_card c u).symm.trans (allC u)
  have hv : (Own c v).card=32 := (W_eq_own_card c v).symm.trans (allC v)
  have hsum := card_union_add_card_inter (Own c u) (Own c v)
  have hbound : (Own c u ∪ Own c v).card≤61 := by
    simpa using card_le_univ (Own c u ∪ Own c v)
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<(Own c u ∩ Own c v).card by omega)
  obtain ⟨hwu,hwv⟩ := mem_inter.mp hw
  have hwu' : w≠u ∧ 15≤colorDegree c (c u w) u := by
    simpa [Own,incomingHighOwnSupport,c.color_symm w u] using hwu
  have hwv' : w≠v ∧ 15≤colorDegree c (c v w) v := by
    simpa [Own,incomingHighOwnSupport,c.color_symm w v] using hwv
  exact (critical_pair_preserved c hc sync allC u w hwu'.1 hwu'.2 j).trans
    (critical_pair_preserved c hc sync allC v w hwv'.1 hwv'.2 j).symm

/-- Elementary common-high-pair endpoint: reciprocity, internal component
sizes, the parity obstruction, and two-color intersection bounds suffice. -/
theorem synchronized_uniform_complete (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) : UniformCommonHighPair c := by
  have allC := synchronized_all_C c hc sync
  let r : Fin 61 := 0
  let high := univ.filter (fun q : FourColor => colorDegree c q r=16)
  refine ⟨high,C_high_color_card c hc r (allC r),?_⟩
  intro v q
  have he := high_flags_global c hc sync allC r v q
  have hrv := W32_degree_cases c hc r (allC r) q
  have hvv := W32_degree_cases c hc v (allC v) q
  by_cases hq : q∈high
  · rw [if_pos hq]
    have hr16 : colorDegree c q r=16 := (mem_filter.mp hq).2
    have hvhigh := he.mp (by omega)
    omega
  · rw [if_neg hq]
    have hrnot : colorDegree c q r≠16 := by simpa [high] using hq
    have hr14 : colorDegree c q r=14 := hrv.resolve_right hrnot
    have hvnot : ¬15≤colorDegree c q v := by intro h;have := he.mpr h;omega
    omega

#print axioms synchronized_uniform_complete
end UniformK61.BalancedStructure
