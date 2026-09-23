import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0024 : LayoutValid (eraseCore (fastBase 0 5 0)) layout0024 := by decide
theorem validLayout0024 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 5) layout0024 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0024
private theorem fastLayout0025 : LayoutValid (eraseCore (fastBase 0 5 0)) layout0025 := by decide
theorem validLayout0025 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 5) layout0025 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0025
private theorem fastLayout0026 : LayoutValid (eraseCore (fastBase 0 5 0)) layout0026 := by decide
theorem validLayout0026 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 5) layout0026 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0026
private theorem fastLayout0027 : LayoutValid (eraseCore (fastBase 0 5 0)) layout0027 := by decide
theorem validLayout0027 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 5) layout0027 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0027
private theorem fastLayout0028 : LayoutValid (eraseCore (fastBase 0 5 0)) layout0028 := by decide
theorem validLayout0028 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 5) layout0028 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0028
private theorem fastLayout0029 : LayoutValid (eraseCore (fastBase 0 6 0)) layout0029 := by decide
theorem validLayout0029 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 6) layout0029 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0029
private theorem fastLayout0030 : LayoutValid (eraseCore (fastBase 0 6 0)) layout0030 := by decide
theorem validLayout0030 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 6) layout0030 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0030
private theorem fastLayout0031 : LayoutValid (eraseCore (fastBase 0 6 0)) layout0031 := by decide
theorem validLayout0031 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 6) layout0031 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0031
end PricingIntegration.RemainingGWitnesses
