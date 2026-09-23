import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0120 : LayoutValid (eraseCore (fastBase 0 29 0)) layout0120 := by decide
theorem validLayout0120 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 29) layout0120 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0120
private theorem fastLayout0121 : LayoutValid (eraseCore (fastBase 0 29 0)) layout0121 := by decide
theorem validLayout0121 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 29) layout0121 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0121
private theorem fastLayout0122 : LayoutValid (eraseCore (fastBase 0 29 0)) layout0122 := by decide
theorem validLayout0122 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 29) layout0122 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0122
private theorem fastLayout0123 : LayoutValid (eraseCore (fastBase 0 30 0)) layout0123 := by decide
theorem validLayout0123 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 30) layout0123 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0123
private theorem fastLayout0124 : LayoutValid (eraseCore (fastBase 0 30 0)) layout0124 := by decide
theorem validLayout0124 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 30) layout0124 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0124
private theorem fastLayout0125 : LayoutValid (eraseCore (fastBase 0 30 0)) layout0125 := by decide
theorem validLayout0125 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 30) layout0125 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0125
private theorem fastLayout0126 : LayoutValid (eraseCore (fastBase 0 31 0)) layout0126 := by decide
theorem validLayout0126 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 31) layout0126 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0126
private theorem fastLayout0127 : LayoutValid (eraseCore (fastBase 0 31 0)) layout0127 := by decide
theorem validLayout0127 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 31) layout0127 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0127
end PricingIntegration.RemainingGWitnesses
