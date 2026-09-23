import PricingIntegration.PairAdmissionHeaders
import PricingIntegration.PairAdmissionComplete
import PricingC.NativePairActionData
set_option autoImplicit false
namespace PricingIntegration.PairAdmission
open Finset
namespace N
abbrev data := PricingC.NativePairActions.tables
end N

def orderSet (code size : Nat) : Finset Nat :=
 (Finset.range size).image (PricingC.NativeBlockActions.digit code)
/-- The admitted pair index is exactly the same native index used by the
whole-block action and matrix orbit witnesses, including original supportorders. -/
def NativeBinding (p : Fin 737) : Prop :=
 let r:=retained p
 PricingC.NativePairActions.leftKinds[p.val]! = r.leftKind ∧
 PricingC.NativePairActions.rightKinds[p.val]! = r.rightKind ∧
 PricingC.NativePairActions.freeSizes[p.val]! = (if r.stage=0 then 4 else 5) ∧
 PricingC.NativePairActions.leftSizes[p.val]! = (if r.stage=1 then 4 else 5) ∧
 PricingC.NativePairActions.rightSizes[p.val]! = (if r.stage=2 then 4 else 5) ∧
 orderSet PricingC.NativePairActions.leftOrders[p.val]! PricingC.NativePairActions.leftSizes[p.val]! = r.left ∧
 orderSet PricingC.NativePairActions.rightOrders[p.val]! PricingC.NativePairActions.rightSizes[p.val]! = r.right
instance (p : Fin 737) : Decidable (NativeBinding p) := inferInstanceAs (Decidable (_ ∧ _))
def bindingIndex (block : Fin 8) (offset : Fin 100) : Fin 737 :=
 ⟨(100*block.val+offset.val)%737,Nat.mod_lt _ (by decide)⟩
end PricingIntegration.PairAdmission
