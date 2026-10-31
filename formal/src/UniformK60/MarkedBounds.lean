import UniformK60.CommonCompleteE
import UniformK60.Selector

/-! The four strict ticket inequalities follow from the exact marked
formula families. UNSAT is the explicit computational boundary. -/
set_option autoImplicit false
namespace UniformK60.MarkedBounds
open Ramsey61 UniformK60.Physical

def ABDExcluded : Prop := ∀ k : ABDFormula.Case,¬∃ v : DenseCounter.Valuation,
  DenseCounter.FormulaSat v (ABDFormula.formula k)
def EExcluded : Prop := ∀ k : EFormula.Case,¬∃ v : DenseCounter.Valuation,
  DenseCounter.FormulaSat v (EFormula.formula k)

theorem strict_ticket_bounds (hABD : ABDExcluded) (hE : EExcluded)
    (c : Host) (hc : NoMonochromaticTriangle c) : StrictTicketBounds c := by
  intro r
  refine ⟨?_,?_,?_,?_⟩
  · intro hw
    by_contra hh
    obtain ⟨k,v,hv⟩ := CommonCover.actual_A_cover c hc r hw (by omega)
    exact hABD k ⟨v,hv⟩
  · intro hw
    by_contra hh
    obtain ⟨k,v,hv⟩ := CommonCover.actual_B_cover c hc r hw (by omega)
    exact hABD k ⟨v,hv⟩
  · intro hw
    by_contra hh
    obtain ⟨k,v,hv⟩ := CommonCompleteD.actual_D_cover c hc r hw (by omega)
    exact hABD k ⟨v,hv⟩
  · intro hw
    by_contra hh
    obtain ⟨k,v,hv⟩ := CommonCompleteE.actual_E_cover c hc r hw (by omega)
    exact hE k ⟨v,hv⟩

#print axioms strict_ticket_bounds
end UniformK60.MarkedBounds
