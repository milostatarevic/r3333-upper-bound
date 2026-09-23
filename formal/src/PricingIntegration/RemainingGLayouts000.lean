import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0000 : LayoutValid (eraseCore (fastBase 0 0 0)) layout0000 := by decide
theorem validLayout0000 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 0) layout0000 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0000
private theorem fastLayout0001 : LayoutValid (eraseCore (fastBase 0 0 0)) layout0001 := by decide
theorem validLayout0001 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 0) layout0001 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0001
private theorem fastLayout0002 : LayoutValid (eraseCore (fastBase 0 0 0)) layout0002 := by decide
theorem validLayout0002 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 0) layout0002 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0002
private theorem fastLayout0003 : LayoutValid (eraseCore (fastBase 0 0 0)) layout0003 := by decide
theorem validLayout0003 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 0) layout0003 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0003
private theorem fastLayout0004 : LayoutValid (eraseCore (fastBase 0 1 0)) layout0004 := by decide
theorem validLayout0004 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 1) layout0004 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0004
private theorem fastLayout0005 : LayoutValid (eraseCore (fastBase 0 1 0)) layout0005 := by decide
theorem validLayout0005 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 1) layout0005 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0005
private theorem fastLayout0006 : LayoutValid (eraseCore (fastBase 0 1 0)) layout0006 := by decide
theorem validLayout0006 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 1) layout0006 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0006
private theorem fastLayout0007 : LayoutValid (eraseCore (fastBase 0 1 0)) layout0007 := by decide
theorem validLayout0007 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 1) layout0007 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0007
end PricingIntegration.RemainingGWitnesses
