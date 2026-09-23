import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0208 : LayoutValid (eraseCore (fastBase 0 52 0)) layout0208 := by decide
theorem validLayout0208 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 52) layout0208 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0208
private theorem fastLayout0209 : LayoutValid (eraseCore (fastBase 0 53 0)) layout0209 := by decide
theorem validLayout0209 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 53) layout0209 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0209
private theorem fastLayout0210 : LayoutValid (eraseCore (fastBase 0 53 0)) layout0210 := by decide
theorem validLayout0210 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 53) layout0210 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0210
private theorem fastLayout0211 : LayoutValid (eraseCore (fastBase 0 53 0)) layout0211 := by decide
theorem validLayout0211 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 53) layout0211 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0211
private theorem fastLayout0212 : LayoutValid (eraseCore (fastBase 0 54 0)) layout0212 := by decide
theorem validLayout0212 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 54) layout0212 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0212
private theorem fastLayout0213 : LayoutValid (eraseCore (fastBase 0 54 0)) layout0213 := by decide
theorem validLayout0213 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 54) layout0213 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0213
private theorem fastLayout0214 : LayoutValid (eraseCore (fastBase 0 54 0)) layout0214 := by decide
theorem validLayout0214 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 54) layout0214 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0214
private theorem fastLayout0215 : LayoutValid (eraseCore (fastBase 0 54 0)) layout0215 := by decide
theorem validLayout0215 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 54) layout0215 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0215
end PricingIntegration.RemainingGWitnesses
