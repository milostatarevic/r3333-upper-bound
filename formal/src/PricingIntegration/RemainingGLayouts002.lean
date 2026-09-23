import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0016 : LayoutValid (eraseCore (fastBase 0 3 0)) layout0016 := by decide
theorem validLayout0016 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 3) layout0016 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0016
private theorem fastLayout0017 : LayoutValid (eraseCore (fastBase 0 3 0)) layout0017 := by decide
theorem validLayout0017 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 3) layout0017 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0017
private theorem fastLayout0018 : LayoutValid (eraseCore (fastBase 0 3 0)) layout0018 := by decide
theorem validLayout0018 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 3) layout0018 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0018
private theorem fastLayout0019 : LayoutValid (eraseCore (fastBase 0 4 0)) layout0019 := by decide
theorem validLayout0019 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 4) layout0019 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0019
private theorem fastLayout0020 : LayoutValid (eraseCore (fastBase 0 4 0)) layout0020 := by decide
theorem validLayout0020 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 4) layout0020 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0020
private theorem fastLayout0021 : LayoutValid (eraseCore (fastBase 0 4 0)) layout0021 := by decide
theorem validLayout0021 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 4) layout0021 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0021
private theorem fastLayout0022 : LayoutValid (eraseCore (fastBase 0 4 0)) layout0022 := by decide
theorem validLayout0022 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 4) layout0022 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0022
private theorem fastLayout0023 : LayoutValid (eraseCore (fastBase 0 5 0)) layout0023 := by decide
theorem validLayout0023 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 5) layout0023 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0023
end PricingIntegration.RemainingGWitnesses
