import PricingIntegration.RemainingGScopeData
import PricingIntegration.RemainingGFastCore
namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.CoreLayout PricingIntegration.RemainingGCore PricingC.GLayoutRefinement
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fastLayout0160 : LayoutValid (eraseCore (fastBase 0 40 0)) layout0160 := by decide
theorem validLayout0160 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 40) layout0160 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0160
private theorem fastLayout0161 : LayoutValid (eraseCore (fastBase 0 41 0)) layout0161 := by decide
theorem validLayout0161 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 41) layout0161 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0161
private theorem fastLayout0162 : LayoutValid (eraseCore (fastBase 0 41 0)) layout0162 := by decide
theorem validLayout0162 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 41) layout0162 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0162
private theorem fastLayout0163 : LayoutValid (eraseCore (fastBase 0 41 0)) layout0163 := by decide
theorem validLayout0163 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 41) layout0163 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0163
private theorem fastLayout0164 : LayoutValid (eraseCore (fastBase 0 41 0)) layout0164 := by decide
theorem validLayout0164 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 41) layout0164 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0164
private theorem fastLayout0165 : LayoutValid (eraseCore (fastBase 0 41 0)) layout0165 := by decide
theorem validLayout0165 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 41) layout0165 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0165
private theorem fastLayout0166 : LayoutValid (eraseCore (fastBase 0 42 0)) layout0166 := by decide
theorem validLayout0166 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 42) layout0166 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0166
private theorem fastLayout0167 : LayoutValid (eraseCore (fastBase 0 42 0)) layout0167 := by decide
theorem validLayout0167 : LayoutValid (PricingIntegration.RemainingGCore.skeleton 42) layout0167 := by
  simpa only [PricingIntegration.RemainingGCore.skeleton,← fastBase_exact] using fastLayout0167
end PricingIntegration.RemainingGWitnesses
