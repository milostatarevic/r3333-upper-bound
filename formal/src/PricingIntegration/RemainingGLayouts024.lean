import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0192 : LayoutValid (eraseCore (fastBase 0 48 0)) layout0192 := by decide
theorem validLayout0192 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 48) layout0192 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0192
private theorem fastLayout0193 : LayoutValid (eraseCore (fastBase 0 48 0)) layout0193 := by decide
theorem validLayout0193 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 48) layout0193 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0193
private theorem fastLayout0194 : LayoutValid (eraseCore (fastBase 0 48 0)) layout0194 := by decide
theorem validLayout0194 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 48) layout0194 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0194
private theorem fastLayout0195 : LayoutValid (eraseCore (fastBase 0 49 0)) layout0195 := by decide
theorem validLayout0195 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 49) layout0195 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0195
private theorem fastLayout0196 : LayoutValid (eraseCore (fastBase 0 49 0)) layout0196 := by decide
theorem validLayout0196 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 49) layout0196 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0196
private theorem fastLayout0197 : LayoutValid (eraseCore (fastBase 0 49 0)) layout0197 := by decide
theorem validLayout0197 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 49) layout0197 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0197
private theorem fastLayout0198 : LayoutValid (eraseCore (fastBase 0 49 0)) layout0198 := by decide
theorem validLayout0198 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 49) layout0198 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0198
private theorem fastLayout0199 : LayoutValid (eraseCore (fastBase 0 49 0)) layout0199 := by decide
theorem validLayout0199 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 49) layout0199 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0199
end PricingIntegration.RemainingGWitnesses
