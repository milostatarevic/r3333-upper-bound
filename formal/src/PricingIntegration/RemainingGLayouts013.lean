import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0104 : LayoutValid (eraseCore (fastBase 0 25 0)) layout0104 := by decide
theorem validLayout0104 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 25) layout0104 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0104
private theorem fastLayout0105 : LayoutValid (eraseCore (fastBase 0 25 0)) layout0105 := by decide
theorem validLayout0105 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 25) layout0105 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0105
private theorem fastLayout0106 : LayoutValid (eraseCore (fastBase 0 25 0)) layout0106 := by decide
theorem validLayout0106 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 25) layout0106 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0106
private theorem fastLayout0107 : LayoutValid (eraseCore (fastBase 0 26 0)) layout0107 := by decide
theorem validLayout0107 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 26) layout0107 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0107
private theorem fastLayout0108 : LayoutValid (eraseCore (fastBase 0 26 0)) layout0108 := by decide
theorem validLayout0108 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 26) layout0108 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0108
private theorem fastLayout0109 : LayoutValid (eraseCore (fastBase 0 26 0)) layout0109 := by decide
theorem validLayout0109 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 26) layout0109 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0109
private theorem fastLayout0110 : LayoutValid (eraseCore (fastBase 0 27 0)) layout0110 := by decide
theorem validLayout0110 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 27) layout0110 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0110
private theorem fastLayout0111 : LayoutValid (eraseCore (fastBase 0 27 0)) layout0111 := by decide
theorem validLayout0111 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 27) layout0111 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0111
end PricingIntegration.RemainingGWitnesses
