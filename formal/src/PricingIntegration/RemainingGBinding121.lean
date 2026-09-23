import PricingIntegration.RemainingGLayouts024

import PricingIntegration.RemainingGLayouts035

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks037

import PricingIntegration.RemainingGScopeChecks039

import PricingIntegration.RemainingGScopeChecks040


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind08712_0 : Agrees (spec (fastBase 1 49 0) layout0195) scope0441 := by decide

theorem reject08712 : Rejected (base 1 49 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 0) _ validLayout0195) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind08712_0) certificate0470

private theorem bind08713_0 : Agrees (spec (fastBase 1 49 1) layout0195) scope0433 := by decide

theorem reject08713 : Rejected (base 1 49 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 1) _ validLayout0195) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind08713_0) certificate0460

private theorem bind08714_0 : Agrees (spec (fastBase 1 49 2) layout0195) scope0434 := by decide

theorem reject08714 : Rejected (base 1 49 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 2) _ validLayout0195) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind08714_0) certificate0461

private theorem bind08715_0 : Agrees (spec (fastBase 1 49 3) layout0196) scope0215 := by decide

private theorem bind08715_1 : Agrees (spec (fastBase 1 49 3) layout0197) scope0213 := by decide

theorem reject08715 : Rejected (base 1 49 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0196 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 3) _ validLayout0196) (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 3) _ validLayout0197) (by decide) (by decide) scope0215 scope0213 (by rw [← fastBase_exact]; exact bind08715_0) (by rw [← fastBase_exact]; exact bind08715_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0216 (by decide)

private theorem bind08716_0 : Agrees (spec (fastBase 1 49 4) layout0195) scope0236 := by decide

theorem reject08716 : Rejected (base 1 49 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 4) _ validLayout0195) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind08716_0) certificate0239

private theorem bind08717_0 : Agrees (spec (fastBase 1 49 5) layout0198) scope0058 := by decide

private theorem bind08717_1 : Agrees (spec (fastBase 1 49 5) layout0197) scope0216 := by decide

theorem reject08717 : Rejected (base 1 49 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0198 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 5) _ validLayout0198) (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 5) _ validLayout0197) (by decide) (by decide) scope0058 scope0216 (by rw [← fastBase_exact]; exact bind08717_0) (by rw [← fastBase_exact]; exact bind08717_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0060 certificate0219 (by decide)

private theorem bind08718_0 : Agrees (spec (fastBase 1 49 6) layout0195) scope0444 := by decide

theorem reject08718 : Rejected (base 1 49 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 6) _ validLayout0195) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind08718_0) certificate0475

private theorem bind08719_0 : Agrees (spec (fastBase 1 49 7) layout0195) scope0232 := by decide

theorem reject08719 : Rejected (base 1 49 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 7) _ validLayout0195) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind08719_0) certificate0235

private theorem bind08720_0 : Agrees (spec (fastBase 1 49 8) layout0195) scope0438 := by decide

theorem reject08720 : Rejected (base 1 49 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 8) _ validLayout0195) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind08720_0) certificate0467

private theorem bind08721_0 : Agrees (spec (fastBase 1 49 9) layout0195) scope0547 := by decide

theorem reject08721 : Rejected (base 1 49 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 9) _ validLayout0195) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind08721_0) certificate0589

private theorem bind08722_0 : Agrees (spec (fastBase 1 49 10) layout0195) scope0548 := by decide

theorem reject08722 : Rejected (base 1 49 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 10) _ validLayout0195) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind08722_0) certificate0590

private theorem bind08723_0 : Agrees (spec (fastBase 1 49 11) layout0195) scope0233 := by decide

theorem reject08723 : Rejected (base 1 49 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 11) _ validLayout0195) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind08723_0) certificate0236

private theorem bind08724_0 : Agrees (spec (fastBase 1 49 12) layout0195) scope0433 := by decide

theorem reject08724 : Rejected (base 1 49 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 12) _ validLayout0195) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind08724_0) certificate0460

private theorem bind08725_0 : Agrees (spec (fastBase 1 49 13) layout0195) scope0434 := by decide

theorem reject08725 : Rejected (base 1 49 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 13) _ validLayout0195) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind08725_0) certificate0461

private theorem bind08726_0 : Agrees (spec (fastBase 1 49 14) layout0199) scope0228 := by decide

theorem reject08726 : Rejected (base 1 49 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 14) _ validLayout0199) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind08726_0) certificate0231

private theorem bind08727_0 : Agrees (spec (fastBase 1 49 15) layout0195) scope0443 := by decide

theorem reject08727 : Rejected (base 1 49 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 15) _ validLayout0195) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind08727_0) certificate0474

private theorem bind08728_0 : Agrees (spec (fastBase 1 49 16) layout0195) scope0441 := by decide

theorem reject08728 : Rejected (base 1 49 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 16) _ validLayout0195) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind08728_0) certificate0470

private theorem bind08729_0 : Agrees (spec (fastBase 1 49 17) layout0195) scope0441 := by decide

theorem reject08729 : Rejected (base 1 49 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 17) _ validLayout0195) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind08729_0) certificate0470

private theorem bind08730_0 : Agrees (spec (fastBase 1 49 18) layout0195) scope0433 := by decide

theorem reject08730 : Rejected (base 1 49 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 18) _ validLayout0195) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind08730_0) certificate0460

private theorem bind08731_0 : Agrees (spec (fastBase 1 49 19) layout0195) scope0236 := by decide

theorem reject08731 : Rejected (base 1 49 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 19) _ validLayout0195) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind08731_0) certificate0239

private theorem bind08732_0 : Agrees (spec (fastBase 1 49 20) layout0195) scope0552 := by decide

theorem reject08732 : Rejected (base 1 49 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 20) _ validLayout0195) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind08732_0) certificate0595

private theorem bind08733_0 : Agrees (spec (fastBase 1 49 21) layout0195) scope0389 := by decide

theorem reject08733 : Rejected (base 1 49 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 21) _ validLayout0195) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind08733_0) certificate0402

private theorem bind08734_0 : Agrees (spec (fastBase 1 49 22) layout0195) scope0441 := by decide

theorem reject08734 : Rejected (base 1 49 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 22) _ validLayout0195) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind08734_0) certificate0470

private theorem bind08735_0 : Agrees (spec (fastBase 1 49 23) layout0195) scope0552 := by decide

theorem reject08735 : Rejected (base 1 49 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 23) _ validLayout0195) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind08735_0) certificate0595

private theorem bind08736_0 : Agrees (spec (fastBase 1 49 24) layout0195) scope0434 := by decide

theorem reject08736 : Rejected (base 1 49 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 24) _ validLayout0195) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind08736_0) certificate0461

private theorem bind08737_0 : Agrees (spec (fastBase 1 49 25) layout0195) scope0444 := by decide

theorem reject08737 : Rejected (base 1 49 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 25) _ validLayout0195) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind08737_0) certificate0475

private theorem bind08738_0 : Agrees (spec (fastBase 1 49 26) layout0195) scope0442 := by decide

theorem reject08738 : Rejected (base 1 49 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 26) _ validLayout0195) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind08738_0) certificate0471

private theorem bind08739_0 : Agrees (spec (fastBase 1 49 27) layout0199) scope0233 := by decide

theorem reject08739 : Rejected (base 1 49 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 27) _ validLayout0199) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind08739_0) certificate0236

private theorem bind08740_0 : Agrees (spec (fastBase 1 49 28) layout0199) scope0232 := by decide

theorem reject08740 : Rejected (base 1 49 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 28) _ validLayout0199) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind08740_0) certificate0235

private theorem bind08741_0 : Agrees (spec (fastBase 1 49 29) layout0196) scope0215 := by decide

private theorem bind08741_1 : Agrees (spec (fastBase 1 49 29) layout0197) scope0216 := by decide

theorem reject08741 : Rejected (base 1 49 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0196 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 29) _ validLayout0196) (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 29) _ validLayout0197) (by decide) (by decide) scope0215 scope0216 (by rw [← fastBase_exact]; exact bind08741_0) (by rw [← fastBase_exact]; exact bind08741_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0219 (by decide)

private theorem bind08742_0 : Agrees (spec (fastBase 1 49 30) layout0196) scope0221 := by decide

theorem reject08742 : Rejected (base 1 49 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 30) _ validLayout0196) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind08742_0) certificate0224

private theorem bind08743_0 : Agrees (spec (fastBase 1 49 31) layout0196) scope0220 := by decide

theorem reject08743 : Rejected (base 1 49 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 31) _ validLayout0196) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind08743_0) certificate0223

private theorem bind08744_0 : Agrees (spec (fastBase 1 49 32) layout0195) scope0433 := by decide

theorem reject08744 : Rejected (base 1 49 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 32) _ validLayout0195) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind08744_0) certificate0460

private theorem bind08745_0 : Agrees (spec (fastBase 1 49 33) layout0284) scope0445 := by decide

private theorem bind08745_1 : Agrees (spec (fastBase 1 49 33) layout0198) scope0593 := by decide

theorem reject08745 : Rejected (base 1 49 33) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0284 layout0198 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 33) _ validLayout0284) (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 33) _ validLayout0198) (by decide) (by decide) scope0445 scope0593 (by rw [← fastBase_exact]; exact bind08745_0) (by rw [← fastBase_exact]; exact bind08745_1) 3 8 3 8 (by decide) (by decide) 3 2 (by decide) certificate0638 certificate0639 (by decide)

private theorem bind08746_0 : Agrees (spec (fastBase 1 49 34) layout0196) scope0210 := by decide

theorem reject08746 : Rejected (base 1 49 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 34) _ validLayout0196) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind08746_0) certificate0213

private theorem bind08747_0 : Agrees (spec (fastBase 1 49 35) layout0195) scope0236 := by decide

theorem reject08747 : Rejected (base 1 49 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 35) _ validLayout0195) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind08747_0) certificate0239

private theorem bind08748_0 : Agrees (spec (fastBase 1 49 36) layout0195) scope0551 := by decide

theorem reject08748 : Rejected (base 1 49 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 36) _ validLayout0195) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind08748_0) certificate0594

private theorem bind08749_0 : Agrees (spec (fastBase 1 49 37) layout0195) scope0389 := by decide

theorem reject08749 : Rejected (base 1 49 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 37) _ validLayout0195) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind08749_0) certificate0402

private theorem bind08750_0 : Agrees (spec (fastBase 1 49 38) layout0195) scope0236 := by decide

theorem reject08750 : Rejected (base 1 49 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 38) _ validLayout0195) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind08750_0) certificate0239

private theorem bind08751_0 : Agrees (spec (fastBase 1 49 39) layout0198) scope0058 := by decide

private theorem bind08751_1 : Agrees (spec (fastBase 1 49 39) layout0197) scope0213 := by decide

theorem reject08751 : Rejected (base 1 49 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0198 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 39) _ validLayout0198) (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 39) _ validLayout0197) (by decide) (by decide) scope0058 scope0213 (by rw [← fastBase_exact]; exact bind08751_0) (by rw [← fastBase_exact]; exact bind08751_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0060 certificate0216 (by decide)

private theorem bind08752_0 : Agrees (spec (fastBase 1 49 40) layout0195) scope0547 := by decide

theorem reject08752 : Rejected (base 1 49 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 40) _ validLayout0195) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind08752_0) certificate0589

private theorem bind08753_0 : Agrees (spec (fastBase 1 49 41) layout0195) scope0228 := by decide

theorem reject08753 : Rejected (base 1 49 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 41) _ validLayout0195) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind08753_0) certificate0231

private theorem bind08754_0 : Agrees (spec (fastBase 1 49 42) layout0195) scope0443 := by decide

theorem reject08754 : Rejected (base 1 49 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 42) _ validLayout0195) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind08754_0) certificate0474

private theorem bind08755_0 : Agrees (spec (fastBase 1 49 43) layout0195) scope0434 := by decide

theorem reject08755 : Rejected (base 1 49 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 43) _ validLayout0195) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind08755_0) certificate0461

private theorem bind08756_0 : Agrees (spec (fastBase 1 49 44) layout0195) scope0444 := by decide

theorem reject08756 : Rejected (base 1 49 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 44) _ validLayout0195) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind08756_0) certificate0475

private theorem bind08757_0 : Agrees (spec (fastBase 1 49 45) layout0195) scope0232 := by decide

theorem reject08757 : Rejected (base 1 49 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 45) _ validLayout0195) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind08757_0) certificate0235

private theorem bind08758_0 : Agrees (spec (fastBase 1 49 46) layout0195) scope0439 := by decide

theorem reject08758 : Rejected (base 1 49 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 46) _ validLayout0195) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind08758_0) certificate0468

private theorem bind08759_0 : Agrees (spec (fastBase 1 49 47) layout0195) scope0442 := by decide

theorem reject08759 : Rejected (base 1 49 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 47) _ validLayout0195) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind08759_0) certificate0471

private theorem bind08760_0 : Agrees (spec (fastBase 1 49 48) layout0195) scope0232 := by decide

theorem reject08760 : Rejected (base 1 49 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 48) _ validLayout0195) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind08760_0) certificate0235

private theorem bind08761_0 : Agrees (spec (fastBase 1 49 49) layout0195) scope0444 := by decide

theorem reject08761 : Rejected (base 1 49 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 49) _ validLayout0195) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind08761_0) certificate0475

private theorem bind08762_0 : Agrees (spec (fastBase 1 49 50) layout0195) scope0550 := by decide

theorem reject08762 : Rejected (base 1 49 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 50) _ validLayout0195) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind08762_0) certificate0593

private theorem bind08763_0 : Agrees (spec (fastBase 1 49 51) layout0195) scope0548 := by decide

theorem reject08763 : Rejected (base 1 49 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 51) _ validLayout0195) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind08763_0) certificate0590

private theorem bind08764_0 : Agrees (spec (fastBase 1 49 52) layout0195) scope0438 := by decide

theorem reject08764 : Rejected (base 1 49 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 52) _ validLayout0195) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind08764_0) certificate0467

private theorem bind08765_0 : Agrees (spec (fastBase 1 49 53) layout0195) scope0438 := by decide

theorem reject08765 : Rejected (base 1 49 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 53) _ validLayout0195) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind08765_0) certificate0467

private theorem bind08766_0 : Agrees (spec (fastBase 1 49 54) layout0195) scope0438 := by decide

theorem reject08766 : Rejected (base 1 49 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 54) _ validLayout0195) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind08766_0) certificate0467

private theorem bind08767_0 : Agrees (spec (fastBase 1 49 55) layout0195) scope0438 := by decide

theorem reject08767 : Rejected (base 1 49 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 55) _ validLayout0195) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind08767_0) certificate0467

private theorem bind08768_0 : Agrees (spec (fastBase 1 49 56) layout0195) scope0438 := by decide

theorem reject08768 : Rejected (base 1 49 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 56) _ validLayout0195) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind08768_0) certificate0467

private theorem bind08769_0 : Agrees (spec (fastBase 1 49 57) layout0195) scope0551 := by decide

theorem reject08769 : Rejected (base 1 49 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 57) _ validLayout0195) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind08769_0) certificate0594

private theorem bind08770_0 : Agrees (spec (fastBase 1 49 58) layout0199) scope0236 := by decide

theorem reject08770 : Rejected (base 1 49 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 58) _ validLayout0199) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind08770_0) certificate0239

private theorem bind08771_0 : Agrees (spec (fastBase 1 49 59) layout0195) scope0547 := by decide

theorem reject08771 : Rejected (base 1 49 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 59) _ validLayout0195) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind08771_0) certificate0589

private theorem bind08772_0 : Agrees (spec (fastBase 1 49 60) layout0284) scope0465 := by decide

private theorem bind08772_1 : Agrees (spec (fastBase 1 49 60) layout0198) scope0594 := by decide

theorem reject08772 : Rejected (base 1 49 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0284 layout0198 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 60) _ validLayout0284) (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 60) _ validLayout0198) (by decide) (by decide) scope0465 scope0594 (by rw [← fastBase_exact]; exact bind08772_0) (by rw [← fastBase_exact]; exact bind08772_1) 3 8 3 8 (by decide) (by decide) 2 3 (by decide) certificate0640 certificate0641 (by decide)

private theorem bind08773_0 : Agrees (spec (fastBase 1 49 61) layout0195) scope0233 := by decide

theorem reject08773 : Rejected (base 1 49 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 61) _ validLayout0195) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind08773_0) certificate0236

private theorem bind08774_0 : Agrees (spec (fastBase 1 49 62) layout0195) scope0439 := by decide

theorem reject08774 : Rejected (base 1 49 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 62) _ validLayout0195) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind08774_0) certificate0468

private theorem bind08775_0 : Agrees (spec (fastBase 1 49 63) layout0196) scope0231 := by decide

theorem reject08775 : Rejected (base 1 49 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 63) _ validLayout0196) (by decide) scope0231 (by rw [← fastBase_exact]; exact bind08775_0) certificate0234

private theorem bind08776_0 : Agrees (spec (fastBase 1 49 64) layout0195) scope0232 := by decide

theorem reject08776 : Rejected (base 1 49 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 64) _ validLayout0195) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind08776_0) certificate0235

private theorem bind08777_0 : Agrees (spec (fastBase 1 49 65) layout0195) scope0548 := by decide

theorem reject08777 : Rejected (base 1 49 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 65) _ validLayout0195) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind08777_0) certificate0590

private theorem bind08778_0 : Agrees (spec (fastBase 1 49 66) layout0195) scope0233 := by decide

theorem reject08778 : Rejected (base 1 49 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 66) _ validLayout0195) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind08778_0) certificate0236

private theorem bind08779_0 : Agrees (spec (fastBase 1 49 67) layout0195) scope0233 := by decide

theorem reject08779 : Rejected (base 1 49 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 67) _ validLayout0195) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind08779_0) certificate0236

private theorem bind08780_0 : Agrees (spec (fastBase 1 49 68) layout0195) scope0228 := by decide

theorem reject08780 : Rejected (base 1 49 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 68) _ validLayout0195) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind08780_0) certificate0231

private theorem bind08781_0 : Agrees (spec (fastBase 1 49 69) layout0195) scope0550 := by decide

theorem reject08781 : Rejected (base 1 49 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 69) _ validLayout0195) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind08781_0) certificate0593

private theorem bind08782_0 : Agrees (spec (fastBase 1 49 70) layout0195) scope0547 := by decide

theorem reject08782 : Rejected (base 1 49 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 70) _ validLayout0195) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind08782_0) certificate0589

private theorem bind08783_0 : Agrees (spec (fastBase 1 49 71) layout0195) scope0548 := by decide

theorem reject08783 : Rejected (base 1 49 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 1 49 71) _ validLayout0195) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind08783_0) certificate0590

theorem allCases121 : ∀ y : Fin 72, Rejected (base 1 49 y) := by
  intro y
  fin_cases y

  · exact reject08712

  · exact reject08713

  · exact reject08714

  · exact reject08715

  · exact reject08716

  · exact reject08717

  · exact reject08718

  · exact reject08719

  · exact reject08720

  · exact reject08721

  · exact reject08722

  · exact reject08723

  · exact reject08724

  · exact reject08725

  · exact reject08726

  · exact reject08727

  · exact reject08728

  · exact reject08729

  · exact reject08730

  · exact reject08731

  · exact reject08732

  · exact reject08733

  · exact reject08734

  · exact reject08735

  · exact reject08736

  · exact reject08737

  · exact reject08738

  · exact reject08739

  · exact reject08740

  · exact reject08741

  · exact reject08742

  · exact reject08743

  · exact reject08744

  · exact reject08745

  · exact reject08746

  · exact reject08747

  · exact reject08748

  · exact reject08749

  · exact reject08750

  · exact reject08751

  · exact reject08752

  · exact reject08753

  · exact reject08754

  · exact reject08755

  · exact reject08756

  · exact reject08757

  · exact reject08758

  · exact reject08759

  · exact reject08760

  · exact reject08761

  · exact reject08762

  · exact reject08763

  · exact reject08764

  · exact reject08765

  · exact reject08766

  · exact reject08767

  · exact reject08768

  · exact reject08769

  · exact reject08770

  · exact reject08771

  · exact reject08772

  · exact reject08773

  · exact reject08774

  · exact reject08775

  · exact reject08776

  · exact reject08777

  · exact reject08778

  · exact reject08779

  · exact reject08780

  · exact reject08781

  · exact reject08782

  · exact reject08783

end PricingIntegration.RemainingGWitnesses
