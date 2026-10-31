import UniformK60.Selector

set_option autoImplicit false
namespace UniformK60.BalancedStructure
open Ramsey61 Finset

/-- Neighborhoods of the endpoints of a monochromatic edge are disjoint. -/
theorem colorNeighborhoods_disjoint_of_edge (c : Host)
    (hc : NoMonochromaticTriangle c) (q : FourColor) (v u : Fin 60)
    (hu : u ∈ colorNeighborhood c q v) :
    Disjoint (colorNeighborhood c q v) (colorNeighborhood c q u) := by
  apply Finset.disjoint_left.mpr
  intro x hxv hxu
  have huv := (mem_colorNeighborhood c q v u).mp hu
  have hxv' := (mem_colorNeighborhood c q v x).mp hxv
  have hxu' := (mem_colorNeighborhood c q u x).mp hxu
  exact hc v u x ⟨huv.1.symm, hxv'.1.symm, hxu'.1.symm⟩
    ⟨huv.2.trans hxv'.2.symm, hxv'.2.trans hxu'.2.symm⟩

/-- Removing two distinct colors leaves two colors, independently of any
critical-template classification. -/
theorem two_remaining (p q : FourColor) (hne : p≠q) :
    ∃ a b : FourColor, ∀ z : FourColor, z≠p → z≠q → z=a ∨ z=b := by
  revert hne q p
  decide

theorem inter_le_five (c : Host) (hc : NoMonochromaticTriangle c)
    (p q : FourColor) (hne : p≠q) (r x : Fin 60) :
    (colorNeighborhood c p r ∩ colorNeighborhood c q x).card ≤ 5 := by
  obtain ⟨a,b,hab⟩ := two_remaining p q hne
  apply twoColorFinset_card_le_five c hc (p:=a) (q:=b)
  intro y hy z hz hyz
  exact hab (c y z)
    (neighborhood_avoids_own_color c hc (mem_inter.mp hy).1 (mem_inter.mp hz).1 hyz)
    (neighborhood_avoids_own_color c hc (mem_inter.mp hy).2 (mem_inter.mp hz).2 hyz)

/-- The internal color neighbors in one actual root neighborhood. -/
def inside (c : Host) (r : Fin 60) (i j : FourColor) (v : Fin 60) : Finset (Fin 60) :=
  colorNeighborhood c j v ∩ colorNeighborhood c i r

theorem inside_self_empty (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (i : FourColor) (v : Fin 60) (hv : v∈colorNeighborhood c i r) :
    inside c r i i v=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨huv,hur⟩ := mem_inter.mp hu
  have hu' := (mem_colorNeighborhood _ _ _ _).mp huv
  exact neighborhood_avoids_own_color c hc hv hur hu'.1.symm hu'.2

theorem inside_sum (c : Host) (r : Fin 60) (i : FourColor) (v : Fin 60)
    (hv : v∈colorNeighborhood c i r) :
    (∑ j : FourColor, (inside c r i j v).card)=colorDegree c i r-1 := by
  have hp := card_eq_sum_card_fiberwise
    (s:=(colorNeighborhood c i r).erase v) (t:=univ) (f:=fun w => c v w)
    (fun _ _ => mem_univ _)
  have he (j : FourColor) :
      ((colorNeighborhood c i r).erase v).filter (fun w => c v w=j)=inside c r i j v := by
    ext w
    simp only [mem_filter,mem_erase,inside,mem_inter,mem_colorNeighborhood]
    tauto
  simp_rw [he] at hp
  have hcard := card_erase_add_one hv
  change _+1=colorDegree c i r at hcard
  omega

/-- The internal degree interval n-11 through5 at orders15 and16. -/
theorem inside_degree_bounds (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Fin 60) (i j : FourColor) (hij : j≠i) (v : Fin 60)
    (hv : v∈colorNeighborhood c i r) :
    colorDegree c i r-11 ≤ (inside c r i j v).card ∧ (inside c r i j v).card≤5 := by
  have upper (q : FourColor) (hq : q≠i) : (inside c r i q v).card≤5 :=
    inter_le_five c hc q i hq v r
  have zero : (inside c r i i v).card=0 := by rw [inside_self_empty c hc r i v hv];rfl
  have total := inside_sum c r i v hv
  have a : (inside c r i (false,false) v).card≤5 := by
    by_cases h : (false,false)=i
    · simp [h,zero]
    · exact upper _ h
  have b : (inside c r i (false,true) v).card≤5 := by
    by_cases h : (false,true)=i
    · simp [h,zero]
    · exact upper _ h
  have d : (inside c r i (true,false) v).card≤5 := by
    by_cases h : (true,false)=i
    · simp [h,zero]
    · exact upper _ h
  have e : (inside c r i (true,true) v).card≤5 := by
    by_cases h : (true,true)=i
    · simp [h,zero]
    · exact upper _ h
  refine ⟨?_,upper j hij⟩
  simp only [FourColor,Fintype.sum_prod_type,Fintype.sum_bool] at total
  rcases i with ⟨i0,i1⟩
  rcases j with ⟨j0,j1⟩
  cases i0 <;> cases i1 <;> cases j0 <;> cases j1 <;> simp_all <;> omega

#print axioms inside_degree_bounds
end UniformK60.BalancedStructure
