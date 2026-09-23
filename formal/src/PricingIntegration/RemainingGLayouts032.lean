import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0256 : LayoutValid (eraseCore (fastBase 0 67 0)) layout0256 := by decide
theorem validLayout0256 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 67) layout0256 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0256
private theorem fastLayout0257 : LayoutValid (eraseCore (fastBase 0 67 0)) layout0257 := by decide
theorem validLayout0257 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 67) layout0257 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0257
private theorem fastLayout0258 : LayoutValid (eraseCore (fastBase 0 68 0)) layout0258 := by decide
theorem validLayout0258 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 68) layout0258 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0258
private theorem fastLayout0259 : LayoutValid (eraseCore (fastBase 0 68 0)) layout0259 := by decide
theorem validLayout0259 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 68) layout0259 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0259
private theorem fastLayout0260 : LayoutValid (eraseCore (fastBase 0 69 0)) layout0260 := by decide
theorem validLayout0260 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 69) layout0260 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0260
private theorem fastLayout0261 : LayoutValid (eraseCore (fastBase 0 69 0)) layout0261 := by decide
theorem validLayout0261 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 69) layout0261 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0261
private theorem fastLayout0262 : LayoutValid (eraseCore (fastBase 0 69 0)) layout0262 := by decide
theorem validLayout0262 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 69) layout0262 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0262
private theorem fastLayout0263 : LayoutValid (eraseCore (fastBase 0 69 0)) layout0263 := by decide
theorem validLayout0263 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 69) layout0263 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0263
end PricingIntegration.RemainingGWitnesses
