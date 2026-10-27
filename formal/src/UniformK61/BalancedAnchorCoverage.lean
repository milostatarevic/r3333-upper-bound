import UniformK61.BalancedAnchorChecks
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace UniformK61.BalancedAnchor
open UniformK61.BalancedEncodingData

/-- The finite witness is one permutation of the entire critical template. -/
def chartPerm (k : Chart) : Equiv.Perm (Fin 16) where
  toFun := chartOrder k
  invFun := chartInverse k
  left_inv := fun v => (chart_inverse k v).1
  right_inv := fun v => (chart_inverse k v).2

theorem chart_color (k : Chart) (a b : Fin 16) :
  R4333.k16Template (chartKind k) (chartPerm k a) (chartPerm k b)=
    stateColor (chartState k) a b := chart_edges k a b

/-- Every ordered reference-colored anchor in either literal template is
covered by one of the320 complete coordinate witnesses. -/
theorem anchor_covered (t : Bool) (a : Fin 5 → Fin 16)
    (hc : ∀ i j, i≠j → R4333.k16Template t (a i) (a j)=reference i j) :
    ∃ k : Chart, chartKind k=t ∧ ∀ i,chartPerm k (anchorPosition i)=a i := by
  have h01 := (hc 0 1 (by decide)).trans (show reference 0 1=1 from by decide)
  have h02 := (hc 0 2 (by decide)).trans (show reference 0 2=2 from by decide)
  have h12 := (hc 1 2 (by decide)).trans (show reference 1 2=1 from by decide)
  have h03 := (hc 0 3 (by decide)).trans (show reference 0 3=2 from by decide)
  have h13 := (hc 1 3 (by decide)).trans (show reference 1 3=2 from by decide)
  have h23 := (hc 2 3 (by decide)).trans (show reference 2 3=1 from by decide)
  have h04 := (hc 0 4 (by decide)).trans (show reference 0 4=1 from by decide)
  have h14 := (hc 1 4 (by decide)).trans (show reference 1 4=2 from by decide)
  have h24 := (hc 2 4 (by decide)).trans (show reference 2 4=2 from by decide)
  have h34 := (hc 3 4 (by decide)).trans (show reference 3 4=1 from by decide)
  obtain ⟨hk,h0,h1,h2,h3,h4⟩ :=
    anchors_exhaustive t (a 0) (a 1) h01 (a 2) h02 h12 (a 3) h03 h13 h23 (a 4) h04 h14 h24 h34
  refine ⟨chartFor t (a 0) (a 1) (a 2),hk,?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- A vertex distinct from the five anchor images has a genuine one of the
remaining eleven coordinates; no completion of the physical host is assumed. -/
theorem inverse_nonanchor (k : Chart) (v : Fin 16)
    (h : ∀ a : Fin 5,v≠chartPerm k (anchorPosition a)) :
    5 ≤ ((chartPerm k).symm v).val := by
  by_contra hn
  have hl : ((chartPerm k).symm v).val<5 := by omega
  let a : Fin 5 := ⟨((chartPerm k).symm v).val,hl⟩
  have he : anchorPosition a=(chartPerm k).symm v := Fin.ext rfl
  exact h a (by rw [he];exact (chartPerm k).apply_symm_apply v |>.symm)

#print axioms anchor_covered
end UniformK61.BalancedAnchor
