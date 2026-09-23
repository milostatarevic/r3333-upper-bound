import PricingIntegration.NativeWholeProof
import CompletionC.CommonCaseCount

set_option autoImplicit false
namespace PricingIntegration.NativeWholeProof

/-- The complete explicit native computational boundary has56830 members:
55016 common A/B/mixed-D, two679-leaf U/U owners, and456 C inputs. -/
theorem native_case_count : Fintype.card Case = 56830 := by
  simp only [Case,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
    PricingG.UUQExactNative.Leaf,
    Fintype.card_fin,CompletionC.CommonCaseCount.native_case_count]

#check ramsey61
#print axioms native_case_count
#print axioms ramsey61
end PricingIntegration.NativeWholeProof
