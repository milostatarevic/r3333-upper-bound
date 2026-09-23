import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0048 : LayoutValid (eraseCore (fastBase 0 9 0)) layout0048 := by decide
theorem validLayout0048 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 9) layout0048 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0048
private theorem fastLayout0049 : LayoutValid (eraseCore (fastBase 0 10 0)) layout0049 := by decide
theorem validLayout0049 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 10) layout0049 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0049
private theorem fastLayout0050 : LayoutValid (eraseCore (fastBase 0 10 0)) layout0050 := by decide
theorem validLayout0050 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 10) layout0050 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0050
private theorem fastLayout0051 : LayoutValid (eraseCore (fastBase 0 10 0)) layout0051 := by decide
theorem validLayout0051 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 10) layout0051 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0051
private theorem fastLayout0052 : LayoutValid (eraseCore (fastBase 0 10 0)) layout0052 := by decide
theorem validLayout0052 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 10) layout0052 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0052
private theorem fastLayout0053 : LayoutValid (eraseCore (fastBase 0 10 0)) layout0053 := by decide
theorem validLayout0053 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 10) layout0053 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0053
private theorem fastLayout0054 : LayoutValid (eraseCore (fastBase 0 11 0)) layout0054 := by decide
theorem validLayout0054 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 11) layout0054 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0054
private theorem fastLayout0055 : LayoutValid (eraseCore (fastBase 0 11 0)) layout0055 := by decide
theorem validLayout0055 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 11) layout0055 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0055
end PricingIntegration.RemainingGWitnesses
