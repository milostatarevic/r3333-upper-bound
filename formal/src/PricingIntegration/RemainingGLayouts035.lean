import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0280 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0280 := by decide
theorem validLayout0280 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0280 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0280
private theorem fastLayout0281 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0281 := by decide
theorem validLayout0281 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0281 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0281
private theorem fastLayout0282 : LayoutValid (eraseCore (fastBase 0 47 0)) layout0282 := by decide
theorem validLayout0282 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 47) layout0282 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0282
private theorem fastLayout0283 : LayoutValid (eraseCore (fastBase 0 48 0)) layout0283 := by decide
theorem validLayout0283 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 48) layout0283 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0283
private theorem fastLayout0284 : LayoutValid (eraseCore (fastBase 0 49 0)) layout0284 := by decide
theorem validLayout0284 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 49) layout0284 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0284
private theorem fastLayout0285 : LayoutValid (eraseCore (fastBase 0 57 0)) layout0285 := by decide
theorem validLayout0285 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 57) layout0285 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0285
private theorem fastLayout0286 : LayoutValid (eraseCore (fastBase 0 61 0)) layout0286 := by decide
theorem validLayout0286 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 61) layout0286 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0286
private theorem fastLayout0287 : LayoutValid (eraseCore (fastBase 0 68 0)) layout0287 := by decide
theorem validLayout0287 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 68) layout0287 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0287
end PricingIntegration.RemainingGWitnesses
