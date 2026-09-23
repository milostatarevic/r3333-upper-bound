import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0040 : LayoutValid (eraseCore (fastBase 0 7 0)) layout0040 := by decide
theorem validLayout0040 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 7) layout0040 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0040
private theorem fastLayout0041 : LayoutValid (eraseCore (fastBase 0 8 0)) layout0041 := by decide
theorem validLayout0041 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 8) layout0041 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0041
private theorem fastLayout0042 : LayoutValid (eraseCore (fastBase 0 8 0)) layout0042 := by decide
theorem validLayout0042 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 8) layout0042 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0042
private theorem fastLayout0043 : LayoutValid (eraseCore (fastBase 0 8 0)) layout0043 := by decide
theorem validLayout0043 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 8) layout0043 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0043
private theorem fastLayout0044 : LayoutValid (eraseCore (fastBase 0 9 0)) layout0044 := by decide
theorem validLayout0044 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 9) layout0044 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0044
private theorem fastLayout0045 : LayoutValid (eraseCore (fastBase 0 9 0)) layout0045 := by decide
theorem validLayout0045 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 9) layout0045 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0045
private theorem fastLayout0046 : LayoutValid (eraseCore (fastBase 0 9 0)) layout0046 := by decide
theorem validLayout0046 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 9) layout0046 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0046
private theorem fastLayout0047 : LayoutValid (eraseCore (fastBase 0 9 0)) layout0047 := by decide
theorem validLayout0047 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 9) layout0047 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0047
end PricingIntegration.RemainingGWitnesses
