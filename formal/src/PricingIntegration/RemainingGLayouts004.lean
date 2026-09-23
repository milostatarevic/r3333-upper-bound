import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0032 : LayoutValid (eraseCore (fastBase 0 6 0)) layout0032 := by decide
theorem validLayout0032 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 6) layout0032 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0032
private theorem fastLayout0033 : LayoutValid (eraseCore (fastBase 0 6 0)) layout0033 := by decide
theorem validLayout0033 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 6) layout0033 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0033
private theorem fastLayout0034 : LayoutValid (eraseCore (fastBase 0 6 0)) layout0034 := by decide
theorem validLayout0034 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 6) layout0034 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0034
private theorem fastLayout0035 : LayoutValid (eraseCore (fastBase 0 7 0)) layout0035 := by decide
theorem validLayout0035 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 7) layout0035 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0035
private theorem fastLayout0036 : LayoutValid (eraseCore (fastBase 0 7 0)) layout0036 := by decide
theorem validLayout0036 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 7) layout0036 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0036
private theorem fastLayout0037 : LayoutValid (eraseCore (fastBase 0 7 0)) layout0037 := by decide
theorem validLayout0037 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 7) layout0037 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0037
private theorem fastLayout0038 : LayoutValid (eraseCore (fastBase 0 7 0)) layout0038 := by decide
theorem validLayout0038 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 7) layout0038 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0038
private theorem fastLayout0039 : LayoutValid (eraseCore (fastBase 0 7 0)) layout0039 := by decide
theorem validLayout0039 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 7) layout0039 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0039
end PricingIntegration.RemainingGWitnesses
