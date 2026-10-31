import UniformK60.BalancedEncodingSoundness
import UniformK60.BalancedEncodingBraceCache
import UniformK60.BalancedEncodingAllFiveSoundness
import UniformK60.BalancedC1Cover
import UniformK60.BalancedHostBraceCover

/-! The two exact computational balance boundaries close the common-pair
alternative. Neither the host cover nor auxiliary existence is an assumption. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingBalance
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.HostNormalization UniformK60.BalancedHost

theorem named_contradiction
    (hMixed : ∀ k : BalancedEncodingBraces.Case,
      ¬∃ v : Valuation,FormulaSat v (BalancedEncodingBraces.formula k))
    (hFive : ∀ o : BalancedHost.Owner,
      (o=(false,false) ∨ o=(false,true) ∨ o=(true,true)) →
      ¬∃ v : Valuation,FormulaSat v (BalancedEncodingAllFive.formula o))
    (c : Host) (hc : NoMonochromaticTriangle c) (hn : NamedCaps c) : False := by
  classical
  by_cases hall : ∀ v,W c v=32
  · obtain ⟨d,o,hd,hnd,ho,hall'⟩ := BalancedC1Cover.canonical_all_C1 c hc hn hall
    have hs := BalancedEncodingAllFive.normalized_satisfiable hd hnd
      (named_all_C1_sixteen d hnd.caps hall')
    exact hFive o ho hs
  · obtain ⟨r,hr⟩ := exists_C2_of_not_all_C1 c hn hall
    obtain ⟨d,k,hd,hnd,hunits⟩ := BalancedHostBraceCover.actual_C2_case c hc hn r hr
    have hs := BalancedEncodingData.normalized_units_satisfiable hd hnd
      (BalancedEncodingBraces.units k) hunits
    exact hMixed k hs

/-- Final balanced endpoint, with only the explicitly enumerated native
UNSAT obligations supplied by the top-level exact-input theorem. -/
theorem common_pair_contradiction
    (hMixed : ∀ k : BalancedEncodingBraces.Case,
      ¬∃ v : Valuation,FormulaSat v (BalancedEncodingBraces.formula k))
    (hFive : ∀ o : BalancedHost.Owner,
      (o=(false,false) ∨ o=(false,true) ∨ o=(true,true)) →
      ¬∃ v : Valuation,FormulaSat v (BalancedEncodingAllFive.formula o))
    (c : Host) (hc : NoMonochromaticTriangle c) (hp : CommonCriticalPair c) : False := by
  obtain ⟨σ,hd,hn,_⟩ := common_pair_to_named c hc hp
  exact named_contradiction hMixed hFive (relabel c (Equiv.refl _) σ) hd hn

#print axioms common_pair_contradiction
end UniformK60.BalancedEncodingBalance
