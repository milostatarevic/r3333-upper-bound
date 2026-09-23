import PricingIntegration.NativeCommonCases
set_option autoImplicit false
namespace CompletionC.CommonCaseCount
open PricingABD.ABLayout CompletionC.NativeFamilyJoin CompletionC.NativeMatrices
open PricingIntegration.NativeCommonCases Finset

def layouts:List Layout:=[Profile.A,Profile.B,Profile.D].flatMap fun p=>[⟨p,false⟩,⟨p,true⟩]
def types:List Types:=[false,true].flatMap fun a=>[false,true].flatMap fun b=>[false,true].map fun q=>⟨a,b,q⟩
def rowCount (l:Layout) (t:Types):Nat:=((List.finRange 737).map fun p=>if Admitted l t p then (pairTable p).count else 0).sum
def executableCount:Nat:=(layouts.map fun l=>(types.map fun t=>rowCount l t).sum).sum

end CompletionC.CommonCaseCount
