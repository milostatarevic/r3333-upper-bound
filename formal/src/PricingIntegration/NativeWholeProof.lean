import PricingIntegration.NativeCommonCases
import CompletionC.ActualProfileCover
import PricingG.UUQExactNative
import PricingIntegration.CComplete
import PricingIntegration.GComplete

set_option autoImplicit false
namespace PricingIntegration.NativeWholeProof
open Ramsey61 Ramsey61.CConcreteFamily
open PricingABD.ABLayout

/-- The exhaustive native computational boundary: common A/B/mixed-D cases,
the two original679-leaf U/U owners, and the456 C inputs. -/
abbrev Case := NativeCommonCases.Case ⊕ ((Bool × PricingG.UUQExactNative.Leaf) ⊕ Fin 456)

def formula : Case → Ramsey61.CNF
  | .inl k => NativeCommonCases.formula k
  | .inr (.inl (q,k)) => PricingG.UUQExactNative.native q k
  | .inr (.inr i) => concreteFamily i

/-- This premise concerns only the explicitly defined finite CNFs.
All coverage, physical transport, and encoding arguments are proved below. -/
def AllNativeUnsat : Prop := ∀ k : Case, ¬Satisfiable (formula k)

theorem common_exclusions (h : AllNativeUnsat) :
    CompletionC.ActualProfileCover.NativeExclusions := by
  intro l t p hp j v hv
  exact h (.inl ⟨l,t,⟨p,hp⟩,j⟩) ⟨v,hv⟩

theorem UU_exclusions (h : AllNativeUnsat) : PricingG.UUQExactNative.NativeExclusions := by
  intro q i v hv
  exact h (.inr (.inl (q,i))) ⟨v,hv⟩

theorem D_selected_excluded (h : AllNativeUnsat) (c : Host)
    (hc : NoMonochromaticTriangle c) (r : Fin 61)
    (hw : W c r=46) (hh : 46≤H c r) : False := by
  obtain ⟨σ,good,five,t,b,_,hcases⟩ := CompletionC.ActualProfileCover.actual_D_cover_or_UU c hc r hw hh
  rcases hcases with ⟨hl,hr⟩ | ⟨p,hp,j,v,hv⟩
  · rcases t with ⟨left,right,q⟩
    change left=false at hl
    change right=false at hr
    subst left
    subst right
    exact PricingG.UUQExactNative.actual_UU_excluded (UU_exclusions h) q b good
  · exact common_exclusions h _ _ _ hp j v hv

/-- The former A/B/D selector parameter is supplied by the proved exhaustive
physical covers and only their explicit native computational exclusions. -/
theorem selector (h : AllNativeUnsat) (c : Host) (hc : NoMonochromaticTriangle c) :
    SelectorX c := by
  intro r
  refine ⟨?_,?_,?_⟩
  · intro hw
    by_contra hn
    have hh : 48≤H c r := by omega
    exact CompletionC.ActualProfileCover.actual_A_excluded (common_exclusions h) c hc r hw hh
  · intro hw
    by_contra hn
    have hh : 47≤H c r := by omega
    exact CompletionC.ActualProfileCover.actual_B_excluded (common_exclusions h) c hc r hw hh
  · intro hw
    by_contra hn
    have hh : 46≤H c r := by omega
    exact D_selected_excluded h c hc r hw hh

/-- Every four-coloring of K61 contains a monochromatic triangle, provided
the explicitly indexed native finite formulas are unsatisfiable. No
mathematical coverage, classification, transport, or encoding premise remains. -/
theorem ramsey61 (h : AllNativeUnsat) : ∀ c : Host, ¬NoMonochromaticTriangle c := by
  apply ramsey61_conditional concreteFamily
    ⟨selector h,GComplete.guarded_G_exclusion,CComplete.physical_C_to_exact_family⟩
  intro i
  exact h (.inr (.inr i))

#synth Fintype Case
#check ramsey61
#print axioms selector
#print axioms ramsey61
end PricingIntegration.NativeWholeProof
