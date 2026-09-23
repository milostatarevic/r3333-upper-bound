import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0008 : LayoutValid (eraseCore (fastBase 0 1 0)) layout0008 := by decide
theorem validLayout0008 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 1) layout0008 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0008
private theorem fastLayout0009 : LayoutValid (eraseCore (fastBase 0 1 0)) layout0009 := by decide
theorem validLayout0009 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 1) layout0009 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0009
private theorem fastLayout0010 : LayoutValid (eraseCore (fastBase 0 2 0)) layout0010 := by decide
theorem validLayout0010 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 2) layout0010 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0010
private theorem fastLayout0011 : LayoutValid (eraseCore (fastBase 0 2 0)) layout0011 := by decide
theorem validLayout0011 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 2) layout0011 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0011
private theorem fastLayout0012 : LayoutValid (eraseCore (fastBase 0 2 0)) layout0012 := by decide
theorem validLayout0012 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 2) layout0012 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0012
private theorem fastLayout0013 : LayoutValid (eraseCore (fastBase 0 2 0)) layout0013 := by decide
theorem validLayout0013 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 2) layout0013 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0013
private theorem fastLayout0014 : LayoutValid (eraseCore (fastBase 0 2 0)) layout0014 := by decide
theorem validLayout0014 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 2) layout0014 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0014
private theorem fastLayout0015 : LayoutValid (eraseCore (fastBase 0 3 0)) layout0015 := by decide
theorem validLayout0015 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 3) layout0015 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0015
end PricingIntegration.RemainingGWitnesses
