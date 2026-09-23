import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0096 : LayoutValid (eraseCore (fastBase 0 22 0)) layout0096 := by decide
theorem validLayout0096 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 22) layout0096 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0096
private theorem fastLayout0097 : LayoutValid (eraseCore (fastBase 0 23 0)) layout0097 := by decide
theorem validLayout0097 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 23) layout0097 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0097
private theorem fastLayout0098 : LayoutValid (eraseCore (fastBase 0 23 0)) layout0098 := by decide
theorem validLayout0098 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 23) layout0098 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0098
private theorem fastLayout0099 : LayoutValid (eraseCore (fastBase 0 23 0)) layout0099 := by decide
theorem validLayout0099 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 23) layout0099 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0099
private theorem fastLayout0100 : LayoutValid (eraseCore (fastBase 0 24 0)) layout0100 := by decide
theorem validLayout0100 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 24) layout0100 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0100
private theorem fastLayout0101 : LayoutValid (eraseCore (fastBase 0 24 0)) layout0101 := by decide
theorem validLayout0101 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 24) layout0101 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0101
private theorem fastLayout0102 : LayoutValid (eraseCore (fastBase 0 24 0)) layout0102 := by decide
theorem validLayout0102 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 24) layout0102 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0102
private theorem fastLayout0103 : LayoutValid (eraseCore (fastBase 0 25 0)) layout0103 := by decide
theorem validLayout0103 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 25) layout0103 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0103
end PricingIntegration.RemainingGWitnesses
