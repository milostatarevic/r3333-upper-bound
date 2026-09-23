import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0272 : LayoutValid (eraseCore (fastBase 0 21 0)) layout0272 := by decide
theorem validLayout0272 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 21) layout0272 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0272
private theorem fastLayout0273 : LayoutValid (eraseCore (fastBase 0 31 0)) layout0273 := by decide
theorem validLayout0273 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 31) layout0273 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0273
private theorem fastLayout0274 : LayoutValid (eraseCore (fastBase 0 32 0)) layout0274 := by decide
theorem validLayout0274 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 32) layout0274 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0274
private theorem fastLayout0275 : LayoutValid (eraseCore (fastBase 0 35 0)) layout0275 := by decide
theorem validLayout0275 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 35) layout0275 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0275
private theorem fastLayout0276 : LayoutValid (eraseCore (fastBase 0 36 0)) layout0276 := by decide
theorem validLayout0276 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 36) layout0276 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0276
private theorem fastLayout0277 : LayoutValid (eraseCore (fastBase 0 36 0)) layout0277 := by decide
theorem validLayout0277 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 36) layout0277 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0277
private theorem fastLayout0278 : LayoutValid (eraseCore (fastBase 0 38 0)) layout0278 := by decide
theorem validLayout0278 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 38) layout0278 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0278
private theorem fastLayout0279 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0279 := by decide
theorem validLayout0279 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0279 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0279
end PricingIntegration.RemainingGWitnesses
