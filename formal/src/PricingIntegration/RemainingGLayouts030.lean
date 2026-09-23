import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0240 : LayoutValid (eraseCore (fastBase 0 62 0)) layout0240 := by decide
theorem validLayout0240 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 62) layout0240 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0240
private theorem fastLayout0241 : LayoutValid (eraseCore (fastBase 0 63 0)) layout0241 := by decide
theorem validLayout0241 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 63) layout0241 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0241
private theorem fastLayout0242 : LayoutValid (eraseCore (fastBase 0 63 0)) layout0242 := by decide
theorem validLayout0242 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 63) layout0242 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0242
private theorem fastLayout0243 : LayoutValid (eraseCore (fastBase 0 63 0)) layout0243 := by decide
theorem validLayout0243 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 63) layout0243 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0243
private theorem fastLayout0244 : LayoutValid (eraseCore (fastBase 0 63 0)) layout0244 := by decide
theorem validLayout0244 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 63) layout0244 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0244
private theorem fastLayout0245 : LayoutValid (eraseCore (fastBase 0 63 0)) layout0245 := by decide
theorem validLayout0245 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 63) layout0245 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0245
private theorem fastLayout0246 : LayoutValid (eraseCore (fastBase 0 64 0)) layout0246 := by decide
theorem validLayout0246 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 64) layout0246 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0246
private theorem fastLayout0247 : LayoutValid (eraseCore (fastBase 0 64 0)) layout0247 := by decide
theorem validLayout0247 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 64) layout0247 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0247
end PricingIntegration.RemainingGWitnesses
