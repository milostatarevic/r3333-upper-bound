import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0088 : LayoutValid (eraseCore (fastBase 0 20 0)) layout0088 := by decide
theorem validLayout0088 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 20) layout0088 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0088
private theorem fastLayout0089 : LayoutValid (eraseCore (fastBase 0 20 0)) layout0089 := by decide
theorem validLayout0089 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 20) layout0089 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0089
private theorem fastLayout0090 : LayoutValid (eraseCore (fastBase 0 20 0)) layout0090 := by decide
theorem validLayout0090 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 20) layout0090 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0090
private theorem fastLayout0091 : LayoutValid (eraseCore (fastBase 0 21 0)) layout0091 := by decide
theorem validLayout0091 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 21) layout0091 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0091
private theorem fastLayout0092 : LayoutValid (eraseCore (fastBase 0 21 0)) layout0092 := by decide
theorem validLayout0092 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 21) layout0092 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0092
private theorem fastLayout0093 : LayoutValid (eraseCore (fastBase 0 22 0)) layout0093 := by decide
theorem validLayout0093 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 22) layout0093 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0093
private theorem fastLayout0094 : LayoutValid (eraseCore (fastBase 0 22 0)) layout0094 := by decide
theorem validLayout0094 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 22) layout0094 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0094
private theorem fastLayout0095 : LayoutValid (eraseCore (fastBase 0 22 0)) layout0095 := by decide
theorem validLayout0095 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 22) layout0095 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0095
end PricingIntegration.RemainingGWitnesses
