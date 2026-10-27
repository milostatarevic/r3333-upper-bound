import UniformK61.ABDProof
import UniformK61.CEntranceFinal
import UniformK61.BalancedStructurePair
import UniformK61.BalancedEncodingActual

set_option autoImplicit false
namespace UniformK61.WholeProof
open Ramsey61 Ramsey61.DenseCounter

/-- One exhaustive finite boundary: marked A/B/D cases, direct C entrances,
and the three globally balanced template pairs. -/
abbrev Case := ABDProof.Case ⊕ (CEntrance.Case ⊕ BalancedHost.Owner)

def formula : Case → CNF
  | .inl k => ABDProof.formula k
  | .inr (.inl k) => CEntrance.formula k
  | .inr (.inr o) => BalancedEncoding.formula o

/-- The sole external computational premise, on the exact emitted formulas. -/
def AllNativeUnsat : Prop := ∀ k : Case, ¬∃ w : Valuation, FormulaSat w (formula k)

theorem selector (h : AllNativeUnsat) (c : Host) (hc : NoMonochromaticTriangle c) :
    SelectorX c := ABDProof.selector (fun k => h (.inl k)) c hc

/-- Ticket counting leaves either an actual marked C entrance or a globally
balanced host. Both branches have complete physical K61 covers. -/
theorem ramsey61 (h : AllNativeUnsat) : ∀ c : Host, ¬NoMonochromaticTriangle c := by
  classical
  intro c hc
  by_cases witness : CExteriorWitness c
  · obtain ⟨k,w,hw⟩ := CEntrance.actual_C_cover c hc witness
    exact h (.inr (.inl k)) ⟨w,hw⟩
  · have sync := no_C_witness_forces_synchronized_CE c hc (selector h c hc) witness
    have uniform := BalancedStructure.synchronized_uniform_complete c hc sync
    obtain ⟨o,w,hw⟩ := BalancedEncoding.actual_uniform_cover c hc uniform
    exact h (.inr (.inr o)) ⟨w,hw⟩

theorem native_case_count : Fintype.card Case = 56723 := by
  have owners : Fintype.card BalancedHost.Owner = 3 := by decide
  rw [Fintype.card_sum,ABDProof.native_case_count,Fintype.card_sum,owners]
  norm_num [CEntrance.Case]

#print axioms selector
#print axioms ramsey61
#print axioms native_case_count
end UniformK61.WholeProof
