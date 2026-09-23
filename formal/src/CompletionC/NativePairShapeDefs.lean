import CompletionC.NativeMatrices
import PricingIntegration.PairNativeBindingComplete
namespace CompletionC.NativeMatrices
open PricingC
/-- Exact shape at the retained native pair index, independent of any chosen
600-word matrix. This is a scalar census binding, not another orbit check. -/
def PairShape (p:Fin 737):Prop:=
 (table (NativePairActions.table p)).shape.code=(PricingIntegration.PairAdmission.retained p).stage
instance (p:Fin 737):Decidable (PairShape p):=inferInstanceAs (Decidable (_ = _))
end CompletionC.NativeMatrices
