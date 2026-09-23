import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0216 : LayoutValid (eraseCore (fastBase 0 54 0)) layout0216 := by decide
theorem validLayout0216 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 54) layout0216 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0216
private theorem fastLayout0217 : LayoutValid (eraseCore (fastBase 0 55 0)) layout0217 := by decide
theorem validLayout0217 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 55) layout0217 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0217
private theorem fastLayout0218 : LayoutValid (eraseCore (fastBase 0 55 0)) layout0218 := by decide
theorem validLayout0218 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 55) layout0218 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0218
private theorem fastLayout0219 : LayoutValid (eraseCore (fastBase 0 55 0)) layout0219 := by decide
theorem validLayout0219 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 55) layout0219 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0219
private theorem fastLayout0220 : LayoutValid (eraseCore (fastBase 0 56 0)) layout0220 := by decide
theorem validLayout0220 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 56) layout0220 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0220
private theorem fastLayout0221 : LayoutValid (eraseCore (fastBase 0 56 0)) layout0221 := by decide
theorem validLayout0221 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 56) layout0221 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0221
private theorem fastLayout0222 : LayoutValid (eraseCore (fastBase 0 56 0)) layout0222 := by decide
theorem validLayout0222 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 56) layout0222 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0222
private theorem fastLayout0223 : LayoutValid (eraseCore (fastBase 0 57 0)) layout0223 := by decide
theorem validLayout0223 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 57) layout0223 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0223
end PricingIntegration.RemainingGWitnesses
