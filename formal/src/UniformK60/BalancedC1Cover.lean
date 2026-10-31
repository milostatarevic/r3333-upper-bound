import UniformK60.BalancedC1Exchange

set_option autoImplicit false
namespace UniformK60.BalancedC1Cover
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization UniformK60.BalancedHost

/-- An all-C1 good host has one of the three literal all-five owners.
Both template placements and the TU-to-UT exchange act on the whole K60. -/
theorem canonical_all_C1 (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (hall : ∀ v,W c v=32) :
    ∃ d : Host,∃ t : Owner,NoMonochromaticTriangle d ∧ Normalized true d t ∧
      (t=(false,false) ∨ t=(false,true) ∨ t=(true,true)) ∧
      (∀ v,W d v=32) := by
  obtain ⟨σ,e,_,_,hn',hs⟩ := normalize_named_C1_root c hn 0 (hall 0)
  let d := relabel c e σ
  have hd := relabel_noMono c hc e σ
  obtain ⟨f,o,_,hf⟩ := BalancedC1Normalize.templates d hd hn' hs
  apply BalancedC1Exchange.ordered (relabel_noMono d hd f (Equiv.refl _)) hf
  intro v
  rw [relabel_W,relabel_W]
  exact hall _

#print axioms canonical_all_C1
end UniformK60.BalancedC1Cover
