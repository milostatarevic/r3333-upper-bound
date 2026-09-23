import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0112 : LayoutValid (eraseCore (fastBase 0 27 0)) layout0112 := by decide
theorem validLayout0112 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 27) layout0112 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0112
private theorem fastLayout0113 : LayoutValid (eraseCore (fastBase 0 27 0)) layout0113 := by decide
theorem validLayout0113 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 27) layout0113 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0113
private theorem fastLayout0114 : LayoutValid (eraseCore (fastBase 0 27 0)) layout0114 := by decide
theorem validLayout0114 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 27) layout0114 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0114
private theorem fastLayout0115 : LayoutValid (eraseCore (fastBase 0 28 0)) layout0115 := by decide
theorem validLayout0115 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 28) layout0115 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0115
private theorem fastLayout0116 : LayoutValid (eraseCore (fastBase 0 28 0)) layout0116 := by decide
theorem validLayout0116 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 28) layout0116 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0116
private theorem fastLayout0117 : LayoutValid (eraseCore (fastBase 0 28 0)) layout0117 := by decide
theorem validLayout0117 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 28) layout0117 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0117
private theorem fastLayout0118 : LayoutValid (eraseCore (fastBase 0 29 0)) layout0118 := by decide
theorem validLayout0118 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 29) layout0118 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0118
private theorem fastLayout0119 : LayoutValid (eraseCore (fastBase 0 29 0)) layout0119 := by decide
theorem validLayout0119 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 29) layout0119 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0119
end PricingIntegration.RemainingGWitnesses
