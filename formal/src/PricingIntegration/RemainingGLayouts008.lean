import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0064 : LayoutValid (eraseCore (fastBase 0 13 0)) layout0064 := by decide
theorem validLayout0064 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 13) layout0064 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0064
private theorem fastLayout0065 : LayoutValid (eraseCore (fastBase 0 14 0)) layout0065 := by decide
theorem validLayout0065 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 14) layout0065 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0065
private theorem fastLayout0066 : LayoutValid (eraseCore (fastBase 0 14 0)) layout0066 := by decide
theorem validLayout0066 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 14) layout0066 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0066
private theorem fastLayout0067 : LayoutValid (eraseCore (fastBase 0 14 0)) layout0067 := by decide
theorem validLayout0067 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 14) layout0067 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0067
private theorem fastLayout0068 : LayoutValid (eraseCore (fastBase 0 14 0)) layout0068 := by decide
theorem validLayout0068 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 14) layout0068 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0068
private theorem fastLayout0069 : LayoutValid (eraseCore (fastBase 0 14 0)) layout0069 := by decide
theorem validLayout0069 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 14) layout0069 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0069
private theorem fastLayout0070 : LayoutValid (eraseCore (fastBase 0 15 0)) layout0070 := by decide
theorem validLayout0070 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 15) layout0070 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0070
private theorem fastLayout0071 : LayoutValid (eraseCore (fastBase 0 15 0)) layout0071 := by decide
theorem validLayout0071 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 15) layout0071 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0071
end PricingIntegration.RemainingGWitnesses
