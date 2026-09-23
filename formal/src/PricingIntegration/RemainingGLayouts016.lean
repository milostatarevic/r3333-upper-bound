import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0128 : LayoutValid (eraseCore (fastBase 0 31 0)) layout0128 := by decide
theorem validLayout0128 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 31) layout0128 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0128
private theorem fastLayout0129 : LayoutValid (eraseCore (fastBase 0 32 0)) layout0129 := by decide
theorem validLayout0129 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 32) layout0129 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0129
private theorem fastLayout0130 : LayoutValid (eraseCore (fastBase 0 32 0)) layout0130 := by decide
theorem validLayout0130 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 32) layout0130 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0130
private theorem fastLayout0131 : LayoutValid (eraseCore (fastBase 0 33 0)) layout0131 := by decide
theorem validLayout0131 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 33) layout0131 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0131
private theorem fastLayout0132 : LayoutValid (eraseCore (fastBase 0 33 0)) layout0132 := by decide
theorem validLayout0132 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 33) layout0132 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0132
private theorem fastLayout0133 : LayoutValid (eraseCore (fastBase 0 33 0)) layout0133 := by decide
theorem validLayout0133 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 33) layout0133 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0133
private theorem fastLayout0134 : LayoutValid (eraseCore (fastBase 0 34 0)) layout0134 := by decide
theorem validLayout0134 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 34) layout0134 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0134
private theorem fastLayout0135 : LayoutValid (eraseCore (fastBase 0 34 0)) layout0135 := by decide
theorem validLayout0135 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 34) layout0135 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0135
end PricingIntegration.RemainingGWitnesses
