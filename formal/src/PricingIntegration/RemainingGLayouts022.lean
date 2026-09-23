import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0176 : LayoutValid (eraseCore (fastBase 0 44 0)) layout0176 := by decide
theorem validLayout0176 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 44) layout0176 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0176
private theorem fastLayout0177 : LayoutValid (eraseCore (fastBase 0 44 0)) layout0177 := by decide
theorem validLayout0177 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 44) layout0177 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0177
private theorem fastLayout0178 : LayoutValid (eraseCore (fastBase 0 44 0)) layout0178 := by decide
theorem validLayout0178 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 44) layout0178 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0178
private theorem fastLayout0179 : LayoutValid (eraseCore (fastBase 0 44 0)) layout0179 := by decide
theorem validLayout0179 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 44) layout0179 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0179
private theorem fastLayout0180 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0180 := by decide
theorem validLayout0180 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0180 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0180
private theorem fastLayout0181 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0181 := by decide
theorem validLayout0181 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0181 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0181
private theorem fastLayout0182 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0182 := by decide
theorem validLayout0182 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0182 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0182
private theorem fastLayout0183 : LayoutValid (eraseCore (fastBase 0 45 0)) layout0183 := by decide
theorem validLayout0183 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 45) layout0183 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0183
end PricingIntegration.RemainingGWitnesses
