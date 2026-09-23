import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0080 : LayoutValid (eraseCore (fastBase 0 18 0)) layout0080 := by decide
theorem validLayout0080 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 18) layout0080 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0080
private theorem fastLayout0081 : LayoutValid (eraseCore (fastBase 0 18 0)) layout0081 := by decide
theorem validLayout0081 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 18) layout0081 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0081
private theorem fastLayout0082 : LayoutValid (eraseCore (fastBase 0 18 0)) layout0082 := by decide
theorem validLayout0082 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 18) layout0082 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0082
private theorem fastLayout0083 : LayoutValid (eraseCore (fastBase 0 18 0)) layout0083 := by decide
theorem validLayout0083 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 18) layout0083 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0083
private theorem fastLayout0084 : LayoutValid (eraseCore (fastBase 0 19 0)) layout0084 := by decide
theorem validLayout0084 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 19) layout0084 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0084
private theorem fastLayout0085 : LayoutValid (eraseCore (fastBase 0 19 0)) layout0085 := by decide
theorem validLayout0085 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 19) layout0085 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0085
private theorem fastLayout0086 : LayoutValid (eraseCore (fastBase 0 20 0)) layout0086 := by decide
theorem validLayout0086 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 20) layout0086 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0086
private theorem fastLayout0087 : LayoutValid (eraseCore (fastBase 0 20 0)) layout0087 := by decide
theorem validLayout0087 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 20) layout0087 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0087
end PricingIntegration.RemainingGWitnesses
