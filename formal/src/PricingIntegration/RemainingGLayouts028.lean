import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0224 : LayoutValid (eraseCore (fastBase 0 57 0)) layout0224 := by decide
theorem validLayout0224 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 57) layout0224 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0224
private theorem fastLayout0225 : LayoutValid (eraseCore (fastBase 0 58 0)) layout0225 := by decide
theorem validLayout0225 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 58) layout0225 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0225
private theorem fastLayout0226 : LayoutValid (eraseCore (fastBase 0 58 0)) layout0226 := by decide
theorem validLayout0226 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 58) layout0226 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0226
private theorem fastLayout0227 : LayoutValid (eraseCore (fastBase 0 58 0)) layout0227 := by decide
theorem validLayout0227 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 58) layout0227 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0227
private theorem fastLayout0228 : LayoutValid (eraseCore (fastBase 0 58 0)) layout0228 := by decide
theorem validLayout0228 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 58) layout0228 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0228
private theorem fastLayout0229 : LayoutValid (eraseCore (fastBase 0 58 0)) layout0229 := by decide
theorem validLayout0229 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 58) layout0229 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0229
private theorem fastLayout0230 : LayoutValid (eraseCore (fastBase 0 59 0)) layout0230 := by decide
theorem validLayout0230 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 59) layout0230 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0230
private theorem fastLayout0231 : LayoutValid (eraseCore (fastBase 0 59 0)) layout0231 := by decide
theorem validLayout0231 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 59) layout0231 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0231
end PricingIntegration.RemainingGWitnesses
