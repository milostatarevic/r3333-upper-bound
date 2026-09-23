import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0136 : LayoutValid (eraseCore (fastBase 0 34 0)) layout0136 := by decide
theorem validLayout0136 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 34) layout0136 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0136
private theorem fastLayout0137 : LayoutValid (eraseCore (fastBase 0 34 0)) layout0137 := by decide
theorem validLayout0137 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 34) layout0137 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0137
private theorem fastLayout0138 : LayoutValid (eraseCore (fastBase 0 35 0)) layout0138 := by decide
theorem validLayout0138 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 35) layout0138 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0138
private theorem fastLayout0139 : LayoutValid (eraseCore (fastBase 0 35 0)) layout0139 := by decide
theorem validLayout0139 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 35) layout0139 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0139
private theorem fastLayout0140 : LayoutValid (eraseCore (fastBase 0 35 0)) layout0140 := by decide
theorem validLayout0140 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 35) layout0140 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0140
private theorem fastLayout0141 : LayoutValid (eraseCore (fastBase 0 36 0)) layout0141 := by decide
theorem validLayout0141 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 36) layout0141 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0141
private theorem fastLayout0142 : LayoutValid (eraseCore (fastBase 0 36 0)) layout0142 := by decide
theorem validLayout0142 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 36) layout0142 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0142
private theorem fastLayout0143 : LayoutValid (eraseCore (fastBase 0 37 0)) layout0143 := by decide
theorem validLayout0143 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 37) layout0143 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0143
end PricingIntegration.RemainingGWitnesses
