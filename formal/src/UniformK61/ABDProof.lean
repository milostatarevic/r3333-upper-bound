import UniformK61.CommonCover
import UniformK61.UUPhysicalCover
import CompletionC.CommonCaseCount

set_option autoImplicit false
namespace UniformK61.ABDProof
open Ramsey61 Ramsey61.DenseCounter

/-- The complete marked-case boundary for profiles A, B and D. -/
abbrev Case := CommonCover.Case ⊕ (Bool × MarkedUU.Leaf)

def formula : Case → CNF
  | .inl k => CommonCover.formula k
  | .inr (q,k) => MarkedUU.formula q k

def AllNativeUnsat : Prop := ∀ k : Case, ¬∃ w : Valuation, FormulaSat w (formula k)

theorem D_selected_excluded (h : AllNativeUnsat) (c : Host)
    (hc : NoMonochromaticTriangle c) (r : Fin 61)
    (hw : W c r = 46) (hh : 46 ≤ H c r) : False := by
  obtain ⟨σ,good,five,t,b,_,hcases⟩ := CommonCover.actual_D_cover_or_UU c hc r hw hh
  rcases hcases with ⟨hl,hr⟩ | ⟨k,w,hw⟩
  · rcases t with ⟨left,right,q⟩
    change left = false at hl
    change right = false at hr
    subst left
    subst right
    obtain ⟨i,w,hw⟩ := UUPhysicalCover.actual_UU_uniform q b good
    exact h (.inr (q,i)) ⟨w,hw⟩
  · exact h (.inl k) ⟨w,hw⟩

/-- The three strict ticket bounds follow only from the A/B/D formulas. -/
theorem selector (h : AllNativeUnsat) (c : Host) (hc : NoMonochromaticTriangle c) :
    SelectorX c := by
  intro r
  refine ⟨?_,?_,?_⟩
  · intro hw
    by_contra hn
    have hh : 48 ≤ H c r := by omega
    obtain ⟨k,w,hk⟩ := CommonCover.actual_A_cover c hc r hw hh
    exact h (.inl k) ⟨w,hk⟩
  · intro hw
    by_contra hn
    have hh : 47 ≤ H c r := by omega
    obtain ⟨k,w,hk⟩ := CommonCover.actual_B_cover c hc r hw hh
    exact h (.inl k) ⟨w,hk⟩
  · intro hw
    by_contra hn
    have hh : 46 ≤ H c r := by omega
    exact D_selected_excluded h c hc r hw hh

theorem native_case_count : Fintype.card Case = 56374 := by
  simp only [Case,CommonCover.Case,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,MarkedUU.Leaf,
    Fintype.card_fin,CompletionC.CommonCaseCount.native_case_count]

#print axioms selector
#print axioms native_case_count
end UniformK61.ABDProof
