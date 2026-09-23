import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0288 : LayoutValid (eraseCore (fastBase 0 70 0)) layout0288 := by decide
theorem validLayout0288 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 70) layout0288 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0288
end PricingIntegration.RemainingGWitnesses
