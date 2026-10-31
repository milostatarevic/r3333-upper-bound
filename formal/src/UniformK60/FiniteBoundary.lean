import UniformK60.ExactInputs
import UniformK60.CEntranceComplete
import UniformK60.BalancedEncodingBalance

/-! Final composition. The sole external premise refers to the explicit
finite CNF catalogue; host coverage and all mathematical reductions are
proved before that boundary is used. -/
set_option autoImplicit false
namespace UniformK60
open Ramsey61

theorem ramsey60_of_exact_unsat (h : ExactInputs.AllUnsat) :
    ∀ c : Host,¬NoMonochromaticTriangle c := by
  apply ramsey60_of_reduction_obligations
  · exact MarkedBounds.strict_ticket_bounds (ExactInputs.abd_excluded h) (ExactInputs.e_excluded h)
  · exact CEntranceComplete.no_exterior_of_all_unsat (ExactInputs.entrance_excluded h)
  · intro c hc hp
    apply BalancedEncodingBalance.common_pair_contradiction ?_ ?_ c hc hp
    · intro k hv
      obtain ⟨v,hv⟩ := hv
      exact ExactInputs.mixed_excluded h k v hv
    · intro o ho hv
      obtain ⟨v,hv⟩ := hv
      exact ExactInputs.all_five_excluded h o ho v hv

#print axioms ramsey60_of_exact_unsat
end UniformK60
