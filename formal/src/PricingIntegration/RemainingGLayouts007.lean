import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0056 : LayoutValid (eraseCore (fastBase 0 11 0)) layout0056 := by decide
theorem validLayout0056 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 11) layout0056 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0056
private theorem fastLayout0057 : LayoutValid (eraseCore (fastBase 0 12 0)) layout0057 := by decide
theorem validLayout0057 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 12) layout0057 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0057
private theorem fastLayout0058 : LayoutValid (eraseCore (fastBase 0 12 0)) layout0058 := by decide
theorem validLayout0058 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 12) layout0058 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0058
private theorem fastLayout0059 : LayoutValid (eraseCore (fastBase 0 12 0)) layout0059 := by decide
theorem validLayout0059 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 12) layout0059 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0059
private theorem fastLayout0060 : LayoutValid (eraseCore (fastBase 0 13 0)) layout0060 := by decide
theorem validLayout0060 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 13) layout0060 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0060
private theorem fastLayout0061 : LayoutValid (eraseCore (fastBase 0 13 0)) layout0061 := by decide
theorem validLayout0061 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 13) layout0061 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0061
private theorem fastLayout0062 : LayoutValid (eraseCore (fastBase 0 13 0)) layout0062 := by decide
theorem validLayout0062 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 13) layout0062 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0062
private theorem fastLayout0063 : LayoutValid (eraseCore (fastBase 0 13 0)) layout0063 := by decide
theorem validLayout0063 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 13) layout0063 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0063
end PricingIntegration.RemainingGWitnesses
