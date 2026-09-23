import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0152 : LayoutValid (eraseCore (fastBase 0 39 0)) layout0152 := by decide
theorem validLayout0152 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 39) layout0152 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0152
private theorem fastLayout0153 : LayoutValid (eraseCore (fastBase 0 39 0)) layout0153 := by decide
theorem validLayout0153 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 39) layout0153 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0153
private theorem fastLayout0154 : LayoutValid (eraseCore (fastBase 0 39 0)) layout0154 := by decide
theorem validLayout0154 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 39) layout0154 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0154
private theorem fastLayout0155 : LayoutValid (eraseCore (fastBase 0 39 0)) layout0155 := by decide
theorem validLayout0155 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 39) layout0155 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0155
private theorem fastLayout0156 : LayoutValid (eraseCore (fastBase 0 40 0)) layout0156 := by decide
theorem validLayout0156 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 40) layout0156 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0156
private theorem fastLayout0157 : LayoutValid (eraseCore (fastBase 0 40 0)) layout0157 := by decide
theorem validLayout0157 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 40) layout0157 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0157
private theorem fastLayout0158 : LayoutValid (eraseCore (fastBase 0 40 0)) layout0158 := by decide
theorem validLayout0158 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 40) layout0158 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0158
private theorem fastLayout0159 : LayoutValid (eraseCore (fastBase 0 40 0)) layout0159 := by decide
theorem validLayout0159 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 40) layout0159 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0159
end PricingIntegration.RemainingGWitnesses
