import CompletionC.NativeFamilyJoin

set_option autoImplicit false
namespace PricingIntegration.NativeCommonCases
open Ramsey61 Ramsey61.DenseCounter PricingABD.ABLayout
open CompletionC.NativeFamilyJoin CompletionC.NativeMatrices

deriving instance Fintype for Profile
deriving instance Fintype for Layout
deriving instance Fintype for Types

instance admittedDecidable (l : Layout) (t : Types) (p : Fin 737) :
    Decidable (Admitted l t p) := by
  unfold Admitted Compatible NativeOwner
  cases l.profile <;> infer_instance

/-- A finite native case has only concrete owner, support-pair, and matrix
indices. Its admissibility is an executable test, not a mathematical premise. -/
abbrev Case := (l : Layout) × (t : Types) ×
  (p : {p : Fin 737 // Admitted l t p}) × Fin (pairTable p.val).count

def formula (k : Case) : DenseCounter.CNF :=
  CompletionC.NativeFamilyJoin.formula k.1 k.2.1 k.2.2.1.val k.2.2.2

def AllUnsat : Prop := ∀ k : Case, ¬∃ v : DenseCounter.Valuation, FormulaSat v (formula k)

theorem concrete_case_exclusion (h : AllUnsat) (l : Layout) (t : Types)
    (p : Fin 737) (hp : Admitted l t p) (j : Fin (pairTable p).count)
    (v : DenseCounter.Valuation)
    (hv : FormulaSat v (CompletionC.NativeFamilyJoin.formula l t p j)) : False :=
  h ⟨l,t,⟨p,hp⟩,j⟩ ⟨v,hv⟩

theorem physical_common_excluded (h : AllUnsat) {c : Host} {l : Layout} {t : Types}
    (b : CompletionC.CommonBlocks.Blocks c l t) (hc : NoMonochromaticTriangle c)
    (ho : NativeOwner l t) : False := by
  obtain ⟨p,hp,j,v,hv⟩ := common_native_cover b hc ho
  exact concrete_case_exclusion h l t p hp j v hv

#synth Fintype Case
#check physical_common_excluded
#print axioms physical_common_excluded
end PricingIntegration.NativeCommonCases
