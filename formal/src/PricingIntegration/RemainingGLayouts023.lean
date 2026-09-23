import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0184 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0184 := by decide
theorem validLayout0184 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0184 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0184
private theorem fastLayout0185 : LayoutValid (eraseCore (fastBase 0 46 0)) layout0185 := by decide
theorem validLayout0185 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 46) layout0185 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0185
private theorem fastLayout0186 : LayoutValid (eraseCore (fastBase 0 46 0)) layout0186 := by decide
theorem validLayout0186 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 46) layout0186 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0186
private theorem fastLayout0187 : LayoutValid (eraseCore (fastBase 0 46 0)) layout0187 := by decide
theorem validLayout0187 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 46) layout0187 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0187
private theorem fastLayout0188 : LayoutValid (eraseCore (fastBase 0 46 0)) layout0188 := by decide
theorem validLayout0188 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 46) layout0188 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0188
private theorem fastLayout0189 : LayoutValid (eraseCore (fastBase 0 47 0)) layout0189 := by decide
theorem validLayout0189 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 47) layout0189 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0189
private theorem fastLayout0190 : LayoutValid (eraseCore (fastBase 0 47 0)) layout0190 := by decide
theorem validLayout0190 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 47) layout0190 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0190
private theorem fastLayout0191 : LayoutValid (eraseCore (fastBase 0 47 0)) layout0191 := by decide
theorem validLayout0191 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 47) layout0191 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0191
end PricingIntegration.RemainingGWitnesses
