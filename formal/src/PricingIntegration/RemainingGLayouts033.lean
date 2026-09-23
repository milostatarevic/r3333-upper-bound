import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0264 : LayoutValid (eraseCore (fastBase 0 69 0)) layout0264 := by decide
theorem validLayout0264 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 69) layout0264 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0264
private theorem fastLayout0265 : LayoutValid (eraseCore (fastBase 0 70 0)) layout0265 := by decide
theorem validLayout0265 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 70) layout0265 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0265
private theorem fastLayout0266 : LayoutValid (eraseCore (fastBase 0 70 0)) layout0266 := by decide
theorem validLayout0266 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 70) layout0266 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0266
private theorem fastLayout0267 : LayoutValid (eraseCore (fastBase 0 71 0)) layout0267 := by decide
theorem validLayout0267 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 71) layout0267 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0267
private theorem fastLayout0268 : LayoutValid (eraseCore (fastBase 0 71 0)) layout0268 := by decide
theorem validLayout0268 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 71) layout0268 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0268
private theorem fastLayout0269 : LayoutValid (eraseCore (fastBase 0 71 0)) layout0269 := by decide
theorem validLayout0269 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 71) layout0269 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0269
private theorem fastLayout0270 : LayoutValid (eraseCore (fastBase 0 16 0)) layout0270 := by decide
theorem validLayout0270 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 16) layout0270 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0270
private theorem fastLayout0271 : LayoutValid (eraseCore (fastBase 0 19 0)) layout0271 := by decide
theorem validLayout0271 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 19) layout0271 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0271
end PricingIntegration.RemainingGWitnesses
