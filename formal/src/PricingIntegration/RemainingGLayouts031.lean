import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0248 : LayoutValid (eraseCore (fastBase 0 64 0)) layout0248 := by decide
theorem validLayout0248 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 64) layout0248 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0248
private theorem fastLayout0249 : LayoutValid (eraseCore (fastBase 0 65 0)) layout0249 := by decide
theorem validLayout0249 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 65) layout0249 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0249
private theorem fastLayout0250 : LayoutValid (eraseCore (fastBase 0 65 0)) layout0250 := by decide
theorem validLayout0250 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 65) layout0250 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0250
private theorem fastLayout0251 : LayoutValid (eraseCore (fastBase 0 65 0)) layout0251 := by decide
theorem validLayout0251 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 65) layout0251 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0251
private theorem fastLayout0252 : LayoutValid (eraseCore (fastBase 0 66 0)) layout0252 := by decide
theorem validLayout0252 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 66) layout0252 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0252
private theorem fastLayout0253 : LayoutValid (eraseCore (fastBase 0 66 0)) layout0253 := by decide
theorem validLayout0253 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 66) layout0253 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0253
private theorem fastLayout0254 : LayoutValid (eraseCore (fastBase 0 66 0)) layout0254 := by decide
theorem validLayout0254 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 66) layout0254 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0254
private theorem fastLayout0255 : LayoutValid (eraseCore (fastBase 0 67 0)) layout0255 := by decide
theorem validLayout0255 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 67) layout0255 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0255
end PricingIntegration.RemainingGWitnesses
