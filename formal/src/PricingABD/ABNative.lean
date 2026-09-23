import PricingABD.ABPrefix
import PricingABD.Schedules.AUUU4Complete
import PricingABD.Schedules.AUUU5Complete
import PricingABD.Schedules.BUUU4Complete
import PricingABD.Schedules.BUUU5Complete
import PricingABD.Schedules.BTUU4Complete
import PricingABD.Schedules.BTUU5Complete

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace PricingABD.ABNative
open Ramsey61 Ramsey61.DenseCounter PricingABD.ABLayout PricingABD.ABGeometry PricingABD.Schedules
open PricingIntegration.NativePrimary

def exactPrefix (l : Layout) (t : Types) : CNF :=
  match l.profile,l.five with
  | .A,false => ABPrefix.exactPrefix AUUU4.program t
  | .A,true => ABPrefix.exactPrefix AUUU5.program t
  | .B,false => if t.left then ABPrefix.exactPrefix BTUU4.program t else ABPrefix.exactPrefix BUUU4.program t
  | .B,true => if t.left then ABPrefix.exactPrefix BTUU5.program t else ABPrefix.exactPrefix BUUU5.program t
  | .D,_ => []

/-- All finite native source, folding, allocation and counter data have been
discharged. The only premises concern the actual host and its physical frame.
Every physical edge atom and highness flag is preserved for the suffix join. -/
theorem actual_native_prefix {c : Host} {l : Layout} (hab : l.profile=.A ∨ l.profile=.B)
    (t : Types) (f : Frame c l) (hc : NoMonochromaticTriangle c) (hg : Geometry t f) :
    ∃w:Valuation,(∀a<primaryLimit l,w a=primary f a) ∧ FormulaSat w (exactPrefix l t) := by
  rcases l with ⟨p,b⟩
  cases p with
  | A =>
    cases b with
    | false =>
      exact ABPrefix.satisfying_extension AUUU4.program AUUU4.types t ⟨Or.inl rfl,Or.inl rfl⟩
        AUUU4Complete.fold_all AUUU4Complete.input_all AUUU4Complete.starts_all f hc hg
    | true =>
      exact ABPrefix.satisfying_extension AUUU5.program AUUU5.types t ⟨Or.inl rfl,Or.inl rfl⟩
        AUUU5Complete.fold_all AUUU5Complete.input_all AUUU5Complete.starts_all f hc hg
  | B =>
    cases b with
    | false =>
      cases ht:t.left with
      | false =>
        simpa only [exactPrefix,ht,Bool.false_eq_true,if_false,BUUU4.layout,BUUU5.layout] using
          ABPrefix.satisfying_extension BUUU4.program BUUU4.types t ⟨Or.inr ht,Or.inl rfl⟩
            BUUU4Complete.fold_all BUUU4Complete.input_all BUUU4Complete.starts_all f hc hg
      | true =>
        simpa only [exactPrefix,ht,if_true,BTUU4.layout,BTUU5.layout] using
          ABPrefix.satisfying_extension BTUU4.program BTUU4.types t ⟨Or.inr ht,Or.inl rfl⟩
            BTUU4Complete.fold_all BTUU4Complete.input_all BTUU4Complete.starts_all f hc hg
    | true =>
      cases ht:t.left with
      | false =>
        simpa only [exactPrefix,ht,Bool.false_eq_true,if_false,BUUU4.layout,BUUU5.layout] using
          ABPrefix.satisfying_extension BUUU5.program BUUU5.types t ⟨Or.inr ht,Or.inl rfl⟩
            BUUU5Complete.fold_all BUUU5Complete.input_all BUUU5Complete.starts_all f hc hg
      | true =>
        simpa only [exactPrefix,ht,if_true,BTUU4.layout,BTUU5.layout] using
          ABPrefix.satisfying_extension BTUU5.program BTUU5.types t ⟨Or.inr ht,Or.inl rfl⟩
            BTUU5Complete.fold_all BTUU5Complete.input_all BTUU5Complete.starts_all f hc hg
  | D => simp at hab

#print axioms actual_native_prefix
end PricingABD.ABNative
