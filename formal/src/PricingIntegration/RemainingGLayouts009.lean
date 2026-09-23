import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0072 : LayoutValid (eraseCore (fastBase 0 15 0)) layout0072 := by decide
theorem validLayout0072 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 15) layout0072 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0072
private theorem fastLayout0073 : LayoutValid (eraseCore (fastBase 0 15 0)) layout0073 := by decide
theorem validLayout0073 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 15) layout0073 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0073
private theorem fastLayout0074 : LayoutValid (eraseCore (fastBase 0 16 0)) layout0074 := by decide
theorem validLayout0074 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 16) layout0074 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0074
private theorem fastLayout0075 : LayoutValid (eraseCore (fastBase 0 16 0)) layout0075 := by decide
theorem validLayout0075 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 16) layout0075 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0075
private theorem fastLayout0076 : LayoutValid (eraseCore (fastBase 0 16 0)) layout0076 := by decide
theorem validLayout0076 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 16) layout0076 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0076
private theorem fastLayout0077 : LayoutValid (eraseCore (fastBase 0 17 0)) layout0077 := by decide
theorem validLayout0077 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 17) layout0077 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0077
private theorem fastLayout0078 : LayoutValid (eraseCore (fastBase 0 17 0)) layout0078 := by decide
theorem validLayout0078 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 17) layout0078 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0078
private theorem fastLayout0079 : LayoutValid (eraseCore (fastBase 0 17 0)) layout0079 := by decide
theorem validLayout0079 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 17) layout0079 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0079
end PricingIntegration.RemainingGWitnesses
