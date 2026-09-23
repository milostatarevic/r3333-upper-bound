import CompletionC.NativeSuffixSat
import PricingABD.ABNative
import PricingIntegration.DNativePrefixComplete
set_option autoImplicit false
namespace CompletionC.NativePrefix
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingABD.ABLayout PricingABD.ABGeometry
open PricingIntegration.NativePrimaryCore PricingIntegration.NativePrimary
open CompletionC.NativeSuffixSat

def formula (l:Layout) (t:Types):CNF:=
 if l.profile=.D then PricingIntegration.DNativePrefix.base l.five t else PricingABD.ABNative.exactPrefix l t

theorem ab_edge_truth {c:Host} {l:Layout} (f:Frame c l) (w:Valuation)
 (h:∀a<primaryLimit l,w a=primary f a):EdgeTruth w f:=by
 intro u v q huv
 have hb:PricingIntegration.NativePrimaryCore.edgeVar u v q<primaryLimit l:=by
  have he:=(edgeVar_bounds (vertex_bounds l) u v q huv).2
  unfold primaryLimit
  omega
 rw[h _ hb]
 exact primary_edge f u v q huv

/-- Every original A/B/D prefix is satisfied by the same physical edge
valuation, with its own independently allocated auxiliary variables. -/
theorem actual_prefix {c:Host} {l:Layout} (t:Types) (f:Frame c l)
 (hc:NoMonochromaticTriangle c) (hg:Geometry t f):
 ∃w:Valuation,FormulaSat w (formula l t) ∧EdgeTruth w f:=by
 by_cases hd:l.profile=.D
 · rcases l with ⟨profile,five⟩
   cases hd
   obtain ⟨w,hs,he⟩:=PricingIntegration.DNativePrefix.satisfying_extension five f t hg hc
   exact ⟨w,hs,he⟩
 · have hab:l.profile=.A∨l.profile=.B:=by cases h:l.profile <;> simp_all
   obtain ⟨w,hp,hs⟩:=PricingABD.ABNative.actual_native_prefix hab t f hc hg
   refine ⟨w,?_,ab_edge_truth f w hp⟩
   simpa only[formula,if_neg hd] using hs
#print axioms actual_prefix
end CompletionC.NativePrefix
