import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0144 : LayoutValid (eraseCore (fastBase 0 37 0)) layout0144 := by decide
theorem validLayout0144 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 37) layout0144 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0144
private theorem fastLayout0145 : LayoutValid (eraseCore (fastBase 0 37 0)) layout0145 := by decide
theorem validLayout0145 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 37) layout0145 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0145
private theorem fastLayout0146 : LayoutValid (eraseCore (fastBase 0 37 0)) layout0146 := by decide
theorem validLayout0146 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 37) layout0146 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0146
private theorem fastLayout0147 : LayoutValid (eraseCore (fastBase 0 38 0)) layout0147 := by decide
theorem validLayout0147 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 38) layout0147 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0147
private theorem fastLayout0148 : LayoutValid (eraseCore (fastBase 0 38 0)) layout0148 := by decide
theorem validLayout0148 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 38) layout0148 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0148
private theorem fastLayout0149 : LayoutValid (eraseCore (fastBase 0 38 0)) layout0149 := by decide
theorem validLayout0149 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 38) layout0149 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0149
private theorem fastLayout0150 : LayoutValid (eraseCore (fastBase 0 38 0)) layout0150 := by decide
theorem validLayout0150 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 38) layout0150 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0150
private theorem fastLayout0151 : LayoutValid (eraseCore (fastBase 0 38 0)) layout0151 := by decide
theorem validLayout0151 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 38) layout0151 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0151
end PricingIntegration.RemainingGWitnesses
