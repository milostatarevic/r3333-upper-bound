import PricingIntegration.RemainingGLayouts030

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks019

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks031

import PricingIntegration.RemainingGScopeChecks036


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind09720_0 : Agrees (spec (fastBase 1 63 0) layout0241) scope0392 := by decide

theorem reject09720 : Rejected (base 1 63 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 0) _ validLayout0241) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09720_0) certificate0405

private theorem bind09721_0 : Agrees (spec (fastBase 1 63 1) layout0241) scope0137 := by decide

theorem reject09721 : Rejected (base 1 63 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 1) _ validLayout0241) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09721_0) certificate0140

private theorem bind09722_0 : Agrees (spec (fastBase 1 63 2) layout0241) scope0399 := by decide

theorem reject09722 : Rejected (base 1 63 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 2) _ validLayout0241) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09722_0) certificate0412

private theorem bind09723_0 : Agrees (spec (fastBase 1 63 3) layout0242) scope0295 := by decide

theorem reject09723 : Rejected (base 1 63 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 3) _ validLayout0242) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind09723_0) certificate0300

private theorem bind09724_0 : Agrees (spec (fastBase 1 63 4) layout0241) scope0133 := by decide

theorem reject09724 : Rejected (base 1 63 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 4) _ validLayout0241) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09724_0) certificate0136

private theorem bind09725_0 : Agrees (spec (fastBase 1 63 5) layout0241) scope0535 := by decide

theorem reject09725 : Rejected (base 1 63 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 5) _ validLayout0241) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09725_0) certificate0577

private theorem bind09726_0 : Agrees (spec (fastBase 1 63 6) layout0241) scope0400 := by decide

theorem reject09726 : Rejected (base 1 63 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 6) _ validLayout0241) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09726_0) certificate0413

private theorem bind09727_0 : Agrees (spec (fastBase 1 63 7) layout0241) scope0393 := by decide

theorem reject09727 : Rejected (base 1 63 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 7) _ validLayout0241) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09727_0) certificate0406

private theorem bind09728_0 : Agrees (spec (fastBase 1 63 8) layout0241) scope0537 := by decide

theorem reject09728 : Rejected (base 1 63 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 8) _ validLayout0241) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09728_0) certificate0579

private theorem bind09729_0 : Agrees (spec (fastBase 1 63 9) layout0241) scope0536 := by decide

theorem reject09729 : Rejected (base 1 63 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 9) _ validLayout0241) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09729_0) certificate0578

private theorem bind09730_0 : Agrees (spec (fastBase 1 63 10) layout0241) scope0534 := by decide

theorem reject09730 : Rejected (base 1 63 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 10) _ validLayout0241) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09730_0) certificate0576

private theorem bind09731_0 : Agrees (spec (fastBase 1 63 11) layout0242) scope0300 := by decide

private theorem bind09731_1 : Agrees (spec (fastBase 1 63 11) layout0243) scope0306 := by decide

theorem reject09731 : Rejected (base 1 63 11) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0242 layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 11) _ validLayout0242) (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 11) _ validLayout0243) (by decide) (by decide) scope0300 scope0306 (by rw [← fastBase_exact]; exact bind09731_0) (by rw [← fastBase_exact]; exact bind09731_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0322 (by decide)

private theorem bind09732_0 : Agrees (spec (fastBase 1 63 12) layout0241) scope0392 := by decide

theorem reject09732 : Rejected (base 1 63 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 12) _ validLayout0241) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09732_0) certificate0405

private theorem bind09733_0 : Agrees (spec (fastBase 1 63 13) layout0241) scope0392 := by decide

theorem reject09733 : Rejected (base 1 63 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 13) _ validLayout0241) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09733_0) certificate0405

private theorem bind09734_0 : Agrees (spec (fastBase 1 63 14) layout0241) scope0392 := by decide

theorem reject09734 : Rejected (base 1 63 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 14) _ validLayout0241) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09734_0) certificate0405

private theorem bind09735_0 : Agrees (spec (fastBase 1 63 15) layout0241) scope0392 := by decide

theorem reject09735 : Rejected (base 1 63 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 15) _ validLayout0241) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09735_0) certificate0405

private theorem bind09736_0 : Agrees (spec (fastBase 1 63 16) layout0241) scope0392 := by decide

theorem reject09736 : Rejected (base 1 63 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 16) _ validLayout0241) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09736_0) certificate0405

private theorem bind09737_0 : Agrees (spec (fastBase 1 63 17) layout0241) scope0137 := by decide

theorem reject09737 : Rejected (base 1 63 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 17) _ validLayout0241) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09737_0) certificate0140

private theorem bind09738_0 : Agrees (spec (fastBase 1 63 18) layout0242) scope0297 := by decide

theorem reject09738 : Rejected (base 1 63 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 18) _ validLayout0242) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind09738_0) certificate0302

private theorem bind09739_0 : Agrees (spec (fastBase 1 63 19) layout0241) scope0394 := by decide

theorem reject09739 : Rejected (base 1 63 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 19) _ validLayout0241) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind09739_0) certificate0407

private theorem bind09740_0 : Agrees (spec (fastBase 1 63 20) layout0241) scope0400 := by decide

theorem reject09740 : Rejected (base 1 63 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 20) _ validLayout0241) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09740_0) certificate0413

private theorem bind09741_0 : Agrees (spec (fastBase 1 63 21) layout0242) scope0318 := by decide

theorem reject09741 : Rejected (base 1 63 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 21) _ validLayout0242) (by decide) scope0318 (by rw [← fastBase_exact]; exact bind09741_0) certificate0324

private theorem bind09742_0 : Agrees (spec (fastBase 1 63 22) layout0241) scope0399 := by decide

theorem reject09742 : Rejected (base 1 63 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 22) _ validLayout0241) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09742_0) certificate0412

private theorem bind09743_0 : Agrees (spec (fastBase 1 63 23) layout0241) scope0133 := by decide

theorem reject09743 : Rejected (base 1 63 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 23) _ validLayout0241) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09743_0) certificate0136

private theorem bind09744_0 : Agrees (spec (fastBase 1 63 24) layout0242) scope0295 := by decide

theorem reject09744 : Rejected (base 1 63 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 24) _ validLayout0242) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind09744_0) certificate0300

private theorem bind09745_0 : Agrees (spec (fastBase 1 63 25) layout0241) scope0394 := by decide

theorem reject09745 : Rejected (base 1 63 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 25) _ validLayout0241) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind09745_0) certificate0407

private theorem bind09746_0 : Agrees (spec (fastBase 1 63 26) layout0242) scope0312 := by decide

theorem reject09746 : Rejected (base 1 63 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 26) _ validLayout0242) (by decide) scope0312 (by rw [← fastBase_exact]; exact bind09746_0) certificate0317

private theorem bind09747_0 : Agrees (spec (fastBase 1 63 27) layout0241) scope0137 := by decide

theorem reject09747 : Rejected (base 1 63 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 27) _ validLayout0241) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09747_0) certificate0140

private theorem bind09748_0 : Agrees (spec (fastBase 1 63 28) layout0241) scope0399 := by decide

theorem reject09748 : Rejected (base 1 63 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 28) _ validLayout0241) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09748_0) certificate0412

private theorem bind09749_0 : Agrees (spec (fastBase 1 63 29) layout0241) scope0544 := by decide

theorem reject09749 : Rejected (base 1 63 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 29) _ validLayout0241) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind09749_0) certificate0586

private theorem bind09750_0 : Agrees (spec (fastBase 1 63 30) layout0241) scope0396 := by decide

theorem reject09750 : Rejected (base 1 63 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 30) _ validLayout0241) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind09750_0) certificate0409

private theorem bind09751_0 : Agrees (spec (fastBase 1 63 31) layout0243) scope0315 := by decide

theorem reject09751 : Rejected (base 1 63 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 31) _ validLayout0243) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind09751_0) certificate0320

private theorem bind09752_0 : Agrees (spec (fastBase 1 63 32) layout0241) scope0544 := by decide

theorem reject09752 : Rejected (base 1 63 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 32) _ validLayout0241) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind09752_0) certificate0586

private theorem bind09753_0 : Agrees (spec (fastBase 1 63 33) layout0241) scope0399 := by decide

theorem reject09753 : Rejected (base 1 63 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 33) _ validLayout0241) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09753_0) certificate0412

private theorem bind09754_0 : Agrees (spec (fastBase 1 63 34) layout0241) scope0535 := by decide

theorem reject09754 : Rejected (base 1 63 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 34) _ validLayout0241) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09754_0) certificate0577

private theorem bind09755_0 : Agrees (spec (fastBase 1 63 35) layout0241) scope0541 := by decide

theorem reject09755 : Rejected (base 1 63 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 35) _ validLayout0241) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind09755_0) certificate0583

private theorem bind09756_0 : Agrees (spec (fastBase 1 63 36) layout0241) scope0133 := by decide

theorem reject09756 : Rejected (base 1 63 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 36) _ validLayout0241) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09756_0) certificate0136

private theorem bind09757_0 : Agrees (spec (fastBase 1 63 37) layout0241) scope0535 := by decide

theorem reject09757 : Rejected (base 1 63 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 37) _ validLayout0241) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09757_0) certificate0577

private theorem bind09758_0 : Agrees (spec (fastBase 1 63 38) layout0241) scope0133 := by decide

theorem reject09758 : Rejected (base 1 63 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 38) _ validLayout0241) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09758_0) certificate0136

private theorem bind09759_0 : Agrees (spec (fastBase 1 63 39) layout0242) scope0308 := by decide

theorem reject09759 : Rejected (base 1 63 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 39) _ validLayout0242) (by decide) scope0308 (by rw [← fastBase_exact]; exact bind09759_0) certificate0313

private theorem bind09760_0 : Agrees (spec (fastBase 1 63 40) layout0241) scope0395 := by decide

theorem reject09760 : Rejected (base 1 63 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 40) _ validLayout0241) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind09760_0) certificate0408

private theorem bind09761_0 : Agrees (spec (fastBase 1 63 41) layout0241) scope0534 := by decide

theorem reject09761 : Rejected (base 1 63 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 41) _ validLayout0241) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09761_0) certificate0576

private theorem bind09762_0 : Agrees (spec (fastBase 1 63 42) layout0241) scope0137 := by decide

theorem reject09762 : Rejected (base 1 63 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 42) _ validLayout0241) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09762_0) certificate0140

private theorem bind09763_0 : Agrees (spec (fastBase 1 63 43) layout0241) scope0396 := by decide

theorem reject09763 : Rejected (base 1 63 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 43) _ validLayout0241) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind09763_0) certificate0409

private theorem bind09764_0 : Agrees (spec (fastBase 1 63 44) layout0241) scope0543 := by decide

theorem reject09764 : Rejected (base 1 63 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 44) _ validLayout0241) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind09764_0) certificate0585

private theorem bind09765_0 : Agrees (spec (fastBase 1 63 45) layout0241) scope0393 := by decide

theorem reject09765 : Rejected (base 1 63 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 45) _ validLayout0241) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09765_0) certificate0406

private theorem bind09766_0 : Agrees (spec (fastBase 1 63 46) layout0241) scope0400 := by decide

theorem reject09766 : Rejected (base 1 63 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 46) _ validLayout0241) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09766_0) certificate0413

private theorem bind09767_0 : Agrees (spec (fastBase 1 63 47) layout0241) scope0393 := by decide

theorem reject09767 : Rejected (base 1 63 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 47) _ validLayout0241) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09767_0) certificate0406

private theorem bind09768_0 : Agrees (spec (fastBase 1 63 48) layout0242) scope0314 := by decide

theorem reject09768 : Rejected (base 1 63 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 48) _ validLayout0242) (by decide) scope0314 (by rw [← fastBase_exact]; exact bind09768_0) certificate0319

private theorem bind09769_0 : Agrees (spec (fastBase 1 63 49) layout0241) scope0400 := by decide

theorem reject09769 : Rejected (base 1 63 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 49) _ validLayout0241) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09769_0) certificate0413

private theorem bind09770_0 : Agrees (spec (fastBase 1 63 50) layout0241) scope0536 := by decide

theorem reject09770 : Rejected (base 1 63 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 50) _ validLayout0241) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09770_0) certificate0578

private theorem bind09771_0 : Agrees (spec (fastBase 1 63 51) layout0241) scope0542 := by decide

theorem reject09771 : Rejected (base 1 63 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 51) _ validLayout0241) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind09771_0) certificate0584

private theorem bind09772_0 : Agrees (spec (fastBase 1 63 52) layout0241) scope0537 := by decide

theorem reject09772 : Rejected (base 1 63 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 52) _ validLayout0241) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09772_0) certificate0579

private theorem bind09773_0 : Agrees (spec (fastBase 1 63 53) layout0241) scope0395 := by decide

theorem reject09773 : Rejected (base 1 63 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 53) _ validLayout0241) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind09773_0) certificate0408

private theorem bind09774_0 : Agrees (spec (fastBase 1 63 54) layout0241) scope0542 := by decide

theorem reject09774 : Rejected (base 1 63 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 54) _ validLayout0241) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind09774_0) certificate0584

private theorem bind09775_0 : Agrees (spec (fastBase 1 63 55) layout0241) scope0536 := by decide

theorem reject09775 : Rejected (base 1 63 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 55) _ validLayout0241) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09775_0) certificate0578

private theorem bind09776_0 : Agrees (spec (fastBase 1 63 56) layout0241) scope0534 := by decide

theorem reject09776 : Rejected (base 1 63 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 56) _ validLayout0241) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09776_0) certificate0576

private theorem bind09777_0 : Agrees (spec (fastBase 1 63 57) layout0241) scope0543 := by decide

theorem reject09777 : Rejected (base 1 63 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 57) _ validLayout0241) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind09777_0) certificate0585

private theorem bind09778_0 : Agrees (spec (fastBase 1 63 58) layout0241) scope0540 := by decide

theorem reject09778 : Rejected (base 1 63 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 58) _ validLayout0241) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind09778_0) certificate0582

private theorem bind09779_0 : Agrees (spec (fastBase 1 63 59) layout0241) scope0537 := by decide

theorem reject09779 : Rejected (base 1 63 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 59) _ validLayout0241) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09779_0) certificate0579

private theorem bind09780_0 : Agrees (spec (fastBase 1 63 60) layout0241) scope0393 := by decide

theorem reject09780 : Rejected (base 1 63 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 60) _ validLayout0241) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09780_0) certificate0406

private theorem bind09781_0 : Agrees (spec (fastBase 1 63 61) layout0241) scope0536 := by decide

theorem reject09781 : Rejected (base 1 63 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 61) _ validLayout0241) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09781_0) certificate0578

private theorem bind09782_0 : Agrees (spec (fastBase 1 63 62) layout0241) scope0541 := by decide

theorem reject09782 : Rejected (base 1 63 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 62) _ validLayout0241) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind09782_0) certificate0583

private theorem bind09783_0 : Agrees (spec (fastBase 1 63 63) layout0241) scope0535 := by decide

theorem reject09783 : Rejected (base 1 63 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 63) _ validLayout0241) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09783_0) certificate0577

private theorem bind09784_0 : Agrees (spec (fastBase 1 63 64) layout0241) scope0540 := by decide

theorem reject09784 : Rejected (base 1 63 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 64) _ validLayout0241) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind09784_0) certificate0582

private theorem bind09785_0 : Agrees (spec (fastBase 1 63 65) layout0241) scope0537 := by decide

theorem reject09785 : Rejected (base 1 63 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 65) _ validLayout0241) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09785_0) certificate0579

private theorem bind09786_0 : Agrees (spec (fastBase 1 63 66) layout0241) scope0534 := by decide

theorem reject09786 : Rejected (base 1 63 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 66) _ validLayout0241) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09786_0) certificate0576

private theorem bind09787_0 : Agrees (spec (fastBase 1 63 67) layout0242) scope0295 := by decide

theorem reject09787 : Rejected (base 1 63 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 67) _ validLayout0242) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind09787_0) certificate0300

private theorem bind09788_0 : Agrees (spec (fastBase 1 63 68) layout0242) scope0296 := by decide

theorem reject09788 : Rejected (base 1 63 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 68) _ validLayout0242) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind09788_0) certificate0301

private theorem bind09789_0 : Agrees (spec (fastBase 1 63 69) layout0242) scope0300 := by decide

private theorem bind09789_1 : Agrees (spec (fastBase 1 63 69) layout0243) scope0301 := by decide

theorem reject09789 : Rejected (base 1 63 69) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0242 layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 69) _ validLayout0242) (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 69) _ validLayout0243) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind09789_0) (by rw [← fastBase_exact]; exact bind09789_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind09790_0 : Agrees (spec (fastBase 1 63 70) layout0243) scope0415 := by decide

theorem reject09790 : Rejected (base 1 63 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 70) _ validLayout0243) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind09790_0) certificate0438

private theorem bind09791_0 : Agrees (spec (fastBase 1 63 71) layout0243) scope0471 := by decide

theorem reject09791 : Rejected (base 1 63 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 1 63 71) _ validLayout0243) (by decide) scope0471 (by rw [← fastBase_exact]; exact bind09791_0) certificate0509

theorem allCases135 : ∀ y : Fin 72, Rejected (base 1 63 y) := by
  intro y
  fin_cases y

  · exact reject09720

  · exact reject09721

  · exact reject09722

  · exact reject09723

  · exact reject09724

  · exact reject09725

  · exact reject09726

  · exact reject09727

  · exact reject09728

  · exact reject09729

  · exact reject09730

  · exact reject09731

  · exact reject09732

  · exact reject09733

  · exact reject09734

  · exact reject09735

  · exact reject09736

  · exact reject09737

  · exact reject09738

  · exact reject09739

  · exact reject09740

  · exact reject09741

  · exact reject09742

  · exact reject09743

  · exact reject09744

  · exact reject09745

  · exact reject09746

  · exact reject09747

  · exact reject09748

  · exact reject09749

  · exact reject09750

  · exact reject09751

  · exact reject09752

  · exact reject09753

  · exact reject09754

  · exact reject09755

  · exact reject09756

  · exact reject09757

  · exact reject09758

  · exact reject09759

  · exact reject09760

  · exact reject09761

  · exact reject09762

  · exact reject09763

  · exact reject09764

  · exact reject09765

  · exact reject09766

  · exact reject09767

  · exact reject09768

  · exact reject09769

  · exact reject09770

  · exact reject09771

  · exact reject09772

  · exact reject09773

  · exact reject09774

  · exact reject09775

  · exact reject09776

  · exact reject09777

  · exact reject09778

  · exact reject09779

  · exact reject09780

  · exact reject09781

  · exact reject09782

  · exact reject09783

  · exact reject09784

  · exact reject09785

  · exact reject09786

  · exact reject09787

  · exact reject09788

  · exact reject09789

  · exact reject09790

  · exact reject09791

end PricingIntegration.RemainingGWitnesses
