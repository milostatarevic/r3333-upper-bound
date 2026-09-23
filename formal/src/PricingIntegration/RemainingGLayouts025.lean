import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0200 : LayoutValid (eraseCore (fastBase 0 50 0)) layout0200 := by decide
theorem validLayout0200 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 50) layout0200 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0200
private theorem fastLayout0201 : LayoutValid (eraseCore (fastBase 0 50 0)) layout0201 := by decide
theorem validLayout0201 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 50) layout0201 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0201
private theorem fastLayout0202 : LayoutValid (eraseCore (fastBase 0 50 0)) layout0202 := by decide
theorem validLayout0202 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 50) layout0202 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0202
private theorem fastLayout0203 : LayoutValid (eraseCore (fastBase 0 51 0)) layout0203 := by decide
theorem validLayout0203 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 51) layout0203 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0203
private theorem fastLayout0204 : LayoutValid (eraseCore (fastBase 0 51 0)) layout0204 := by decide
theorem validLayout0204 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 51) layout0204 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0204
private theorem fastLayout0205 : LayoutValid (eraseCore (fastBase 0 51 0)) layout0205 := by decide
theorem validLayout0205 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 51) layout0205 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0205
private theorem fastLayout0206 : LayoutValid (eraseCore (fastBase 0 52 0)) layout0206 := by decide
theorem validLayout0206 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 52) layout0206 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0206
private theorem fastLayout0207 : LayoutValid (eraseCore (fastBase 0 52 0)) layout0207 := by decide
theorem validLayout0207 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 52) layout0207 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0207
end PricingIntegration.RemainingGWitnesses
