import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0232 : LayoutValid (eraseCore (fastBase 0 59 0)) layout0232 := by decide
theorem validLayout0232 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 59) layout0232 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0232
private theorem fastLayout0233 : LayoutValid (eraseCore (fastBase 0 60 0)) layout0233 := by decide
theorem validLayout0233 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 60) layout0233 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0233
private theorem fastLayout0234 : LayoutValid (eraseCore (fastBase 0 60 0)) layout0234 := by decide
theorem validLayout0234 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 60) layout0234 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0234
private theorem fastLayout0235 : LayoutValid (eraseCore (fastBase 0 60 0)) layout0235 := by decide
theorem validLayout0235 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 60) layout0235 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0235
private theorem fastLayout0236 : LayoutValid (eraseCore (fastBase 0 61 0)) layout0236 := by decide
theorem validLayout0236 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 61) layout0236 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0236
private theorem fastLayout0237 : LayoutValid (eraseCore (fastBase 0 61 0)) layout0237 := by decide
theorem validLayout0237 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 61) layout0237 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0237
private theorem fastLayout0238 : LayoutValid (eraseCore (fastBase 0 62 0)) layout0238 := by decide
theorem validLayout0238 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 62) layout0238 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0238
private theorem fastLayout0239 : LayoutValid (eraseCore (fastBase 0 62 0)) layout0239 := by decide
theorem validLayout0239 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 62) layout0239 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0239
end PricingIntegration.RemainingGWitnesses
