import UniformK61.BalancedStructureHomogeneous
set_option autoImplicit false
namespace UniformK61.BalancedStructure
open Ramsey61 Finset

theorem E_of_all_high (c : Host) (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (v : Fin 61) (h : ∀q : FourColor,15≤colorDegree c q v) : W c v=60 := by
  rcases sync.1 v with hC|hE
  · obtain ⟨q,hq⟩ := C_exists_low_color c hc v hC
    have := h q
    omega
  · exact hE

theorem critical_E_homogeneous (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) (r : Fin 61) (i : FourColor) (hi : 15≤colorDegree c i r)
    (v : Fin 61) (hv : v∈colorNeighborhood c i r) (hE : W c v=60) :
    ∀w∈colorNeighborhood c i r,W c w=60 := by
  intro w hw
  apply E_of_all_high c hc sync w
  intro q
  apply (critical_homogeneous c hc sync r i hi v hv w hw q).mp
  rw [W60_degree_cases c hc v hE q]

theorem E_enters_high (c : Host) (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (r v : Fin 61) (hC : W c r=32) (hE : W c v=60) :
    v≠r ∧ colorDegree c (c r v) r=16 := by
  have hne : v≠r := by intro he;subst v;omega
  have he := synchronized_endpoint_highness c sync r v hne
  have hv := W60_degree_cases c hc v hE (c r v)
  have hr := he.mpr (by omega)
  have hd := W32_degree_cases c hc r hC (c r v)
  exact ⟨hne,by omega⟩

/-- An E neighborhood would have15 vertices inside two different-color
intersections of size at most5. Only the elementary critical-cell
connectivity and the two-color K6 bound are used. -/
theorem synchronized_all_C (c : Host) (hc : NoMonochromaticTriangle c)
    (sync : SynchronizedCE c) : ∀v,W c v=32 := by
  obtain ⟨r,hC⟩ := synchronized_exists_C c hc sync
  obtain ⟨q,hq⟩ := C_exists_low_color c hc r hC
  have noE : ∀e,W c e≠60 := by
    intro e hE
    obtain ⟨hne,hi⟩ := E_enters_high c hc sync r e hC hE
    let i := c r e
    change colorDegree c i r=16 at hi
    have hem : e∈colorNeighborhood c i r := (mem_colorNeighborhood _ _ _ _).mpr ⟨hne,rfl⟩
    have hqi : q≠i := by intro he;rw [he] at hq;omega
    have lower := (inside_degree_bounds c hc r i q hqi e hem).1
    obtain ⟨a,ha⟩ := card_pos.mp (show 0<(inside c r i q e).card by omega)
    obtain ⟨haN,haZ⟩ := mem_inter.mp ha
    have haE := critical_E_homogeneous c hc sync r i (by omega) e hem hE a haZ
    have heq := W60_degree_cases c hc e hE q
    have allE : ∀v∈colorNeighborhood c q e,W c v=60 :=
      critical_E_homogeneous c hc sync e q (by omega) a haN haE
    let high := univ.filter (fun j : FourColor => colorDegree c j r=16)
    have hhigh : high.card=2 := C_high_color_card c hc r hC
    have hp := card_eq_sum_card_fiberwise
      (s:=colorNeighborhood c q e) (t:=high) (f:=fun v => c r v) (by
        intro v hv
        exact mem_filter.mpr ⟨mem_univ _,(E_enters_high c hc sync r v hC (allE v hv)).2⟩)
    have bound : ∀j∈high,((colorNeighborhood c q e).filter (fun v => c r v=j)).card≤5 := by
      intro j hj
      have hj16 := (mem_filter.mp hj).2
      have hqj : q≠j := by intro he;rw [he] at hq;omega
      have sub : (colorNeighborhood c q e).filter (fun v => c r v=j) ⊆
          colorNeighborhood c q e ∩ colorNeighborhood c j r := by
        intro v hv
        obtain ⟨hvN,hvj⟩ := mem_filter.mp hv
        exact mem_inter.mpr ⟨hvN,(mem_colorNeighborhood _ _ _ _).mpr
          ⟨(E_enters_high c hc sync r v hC (allE v hvN)).1,hvj⟩⟩
      exact (card_le_card sub).trans (inter_le_five c hc q j hqj e r)
    have hsum := sum_le_sum bound
    have hle : (colorNeighborhood c q e).card≤10 := by
      rw [hp]
      calc
        _ ≤ ∑_j∈high,5 := hsum
        _ = 10 := by simp [hhigh]
    change colorDegree c q e≤10 at hle
    omega
  intro v
  exact (sync.1 v).resolve_right (noE v)

#print axioms synchronized_all_C
end UniformK61.BalancedStructure
