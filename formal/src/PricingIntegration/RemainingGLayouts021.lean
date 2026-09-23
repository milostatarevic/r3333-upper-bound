import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0168 : LayoutValid (eraseCore (fastBase 0 42 0)) layout0168 := by decide
theorem validLayout0168 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 42) layout0168 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0168
private theorem fastLayout0169 : LayoutValid (eraseCore (fastBase 0 42 0)) layout0169 := by decide
theorem validLayout0169 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 42) layout0169 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0169
private theorem fastLayout0170 : LayoutValid (eraseCore (fastBase 0 42 0)) layout0170 := by decide
theorem validLayout0170 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 42) layout0170 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0170
private theorem fastLayout0171 : LayoutValid (eraseCore (fastBase 0 43 0)) layout0171 := by decide
theorem validLayout0171 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 43) layout0171 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0171
private theorem fastLayout0172 : LayoutValid (eraseCore (fastBase 0 43 0)) layout0172 := by decide
theorem validLayout0172 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 43) layout0172 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0172
private theorem fastLayout0173 : LayoutValid (eraseCore (fastBase 0 43 0)) layout0173 := by decide
theorem validLayout0173 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 43) layout0173 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0173
private theorem fastLayout0174 : LayoutValid (eraseCore (fastBase 0 43 0)) layout0174 := by decide
theorem validLayout0174 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 43) layout0174 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0174
private theorem fastLayout0175 : LayoutValid (eraseCore (fastBase 0 43 0)) layout0175 := by decide
theorem validLayout0175 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 43) layout0175 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0175
end PricingIntegration.RemainingGWitnesses
