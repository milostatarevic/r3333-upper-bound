import UniformK60.CEntranceLayout

set_option autoImplicit false
namespace UniformK60.CEntranceMembership
open Ramsey61 Finset UniformK60.Physical
open UniformK60.CEntranceSource UniformK60.CEntranceLayout
open PricingIntegration.PairAdmission CompletionC.NativeMatrices

/-- Exact signed membership is determined by the actual free support and
foreign supports. The untemplated marked cell contributes only exclusions
forced by the root triangle. -/
theorem membership_from_cells {c : Host} (hc : NoMonochromaticTriangle c)
    (mode : Mode) (p : Fin 737)
    (spokes : ∀ v : Vertex,v≠0 → c 0 v=palette (rootColor mode v))
    (free : ∀ v : Vertex,v≠0 → v.val≤lowSize mode →
      (c v 59=palette 3 ↔ v.val≤(pairTable p).shape.free))
    (left : ∀ i : Fin (leftSize mode),c (leftVertex mode i) 59=palette 3 ↔
      i.val∈(retained p).left)
    (right : ∀ i : Fin 16,c (rightVertex mode i) 59=palette 3 ↔
      i.val∈(retained p).right) :
    ∀ v : Vertex,v≠59 → (c v 59=palette 3 ↔ member mode p v=true) := by
  intro v hv
  have hsmall : (pairTable p).shape.free≤5 := by cases (pairTable p).shape <;> decide
  have hlow : 13≤lowSize mode := by fin_cases mode <;> decide
  by_cases hzero : v=0
  · subst v
    have hm := spokes 59 (by decide)
    rw [rootColor_mark] at hm
    simp [member,hm]
  by_cases hfree : v.val≤(pairTable p).shape.free
  · have hcell : v.val≤lowSize mode := by omega
    have hm := (free v hzero hcell).mpr hfree
    simp [member,hzero,hfree,hm]
  by_cases hcell : v.val≤lowSize mode
  · have hm : c v 59≠palette 3 := fun h => hfree ((free v hzero hcell).mp h)
    simp [member,hzero,hfree,hcell,hm]
  by_cases hl : v.val<rightStart mode
  · have hstart : leftStart mode≤v.val := by unfold leftStart;omega
    obtain ⟨i,hi⟩ := left_index ⟨hstart,hl⟩
    have hval : v.val-leftStart mode=i.val := by
      have hi0 := i.isLt
      have hb : leftStart mode+i.val<60 := by
        have hx : rightStart mode≤31 := by fin_cases mode <;> decide
        unfold rightStart at hx
        omega
      have h := congrArg Fin.val hi
      change (leftStart mode+i.val)%60=v.val at h
      rw [Nat.mod_eq_of_lt hb] at h
      omega
    rw [member,if_neg hzero,if_neg hfree,if_neg hcell,if_pos hl]
    rw [decide_eq_true_eq, hval,←hi]
    exact left i
  by_cases hr : v.val<rightStart mode+16
  · obtain ⟨i,hi⟩ := right_index ⟨by omega,hr⟩
    have hval : v.val-rightStart mode=i.val := by
      have hi0 := i.isLt
      have hb : rightStart mode+i.val<60 := by
        have hx : rightStart mode≤31 := by fin_cases mode <;> decide
        omega
      have h := congrArg Fin.val hi
      change (rightStart mode+i.val)%60=v.val at h
      rw [Nat.mod_eq_of_lt hb] at h
      omega
    rw [member,if_neg hzero,if_neg hfree,if_neg hcell,if_neg hl,if_pos hr]
    rw [decide_eq_true_eq,hval,←hi]
    exact right i
  have hm : c v 59≠palette 3 := by
    apply neighborhood_avoids_own_color c hc
    · apply (mem_colorNeighborhood _ _ _ _).mpr
      exact ⟨hzero,by simpa [rootColor,hcell,hl,hr] using spokes v hzero⟩
    · apply (mem_colorNeighborhood _ _ _ _).mpr
      exact ⟨by decide,by simpa only [rootColor_mark] using spokes 59 (by decide)⟩
    · exact hv
  simp [member,hzero,hfree,hcell,hl,hr,hm]

#print axioms membership_from_cells
end UniformK60.CEntranceMembership
