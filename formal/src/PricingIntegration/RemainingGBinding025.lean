import PricingIntegration.RemainingGLayouts012

import PricingIntegration.RemainingGLayouts013

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks004

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks024


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind01800_0 : Agrees (spec (fastBase 0 25 0) layout0103) scope0177 := by decide

theorem reject01800 : Rejected (base 0 25 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 0) _ validLayout0103) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01800_0) certificate0180

private theorem bind01801_0 : Agrees (spec (fastBase 0 25 1) layout0104) scope0054 := by decide

theorem reject01801 : Rejected (base 0 25 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 1) _ validLayout0104) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind01801_0) certificate0056

private theorem bind01802_0 : Agrees (spec (fastBase 0 25 2) layout0104) scope0061 := by decide

theorem reject01802 : Rejected (base 0 25 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 2) _ validLayout0104) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind01802_0) certificate0063

private theorem bind01803_0 : Agrees (spec (fastBase 0 25 3) layout0104) scope0062 := by decide

private theorem bind01803_1 : Agrees (spec (fastBase 0 25 3) layout0105) scope0057 := by decide

theorem reject01803 : Rejected (base 0 25 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 3) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 3) _ validLayout0105) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind01803_0) (by rw [← fastBase_exact]; exact bind01803_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind01804_0 : Agrees (spec (fastBase 0 25 4) layout0103) scope0176 := by decide

theorem reject01804 : Rejected (base 0 25 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 4) _ validLayout0103) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01804_0) certificate0179

private theorem bind01805_0 : Agrees (spec (fastBase 0 25 5) layout0104) scope0065 := by decide

theorem reject01805 : Rejected (base 0 25 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 5) _ validLayout0104) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind01805_0) certificate0067

private theorem bind01806_0 : Agrees (spec (fastBase 0 25 6) layout0103) scope0186 := by decide

theorem reject01806 : Rejected (base 0 25 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 6) _ validLayout0103) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01806_0) certificate0189

private theorem bind01807_0 : Agrees (spec (fastBase 0 25 7) layout0104) scope0076 := by decide

private theorem bind01807_1 : Agrees (spec (fastBase 0 25 7) layout0105) scope0063 := by decide

theorem reject01807 : Rejected (base 0 25 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 7) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 7) _ validLayout0105) (by decide) (by decide) scope0076 scope0063 (by rw [← fastBase_exact]; exact bind01807_0) (by rw [← fastBase_exact]; exact bind01807_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0078 certificate0079 (by decide)

private theorem bind01808_0 : Agrees (spec (fastBase 0 25 8) layout0103) scope0184 := by decide

theorem reject01808 : Rejected (base 0 25 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 8) _ validLayout0103) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01808_0) certificate0187

private theorem bind01809_0 : Agrees (spec (fastBase 0 25 9) layout0103) scope0191 := by decide

theorem reject01809 : Rejected (base 0 25 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 9) _ validLayout0103) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01809_0) certificate0194

private theorem bind01810_0 : Agrees (spec (fastBase 0 25 10) layout0103) scope0185 := by decide

theorem reject01810 : Rejected (base 0 25 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 10) _ validLayout0103) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01810_0) certificate0188

private theorem bind01811_0 : Agrees (spec (fastBase 0 25 11) layout0104) scope0066 := by decide

theorem reject01811 : Rejected (base 0 25 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 11) _ validLayout0104) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind01811_0) certificate0068

private theorem bind01812_0 : Agrees (spec (fastBase 0 25 12) layout0104) scope0054 := by decide

theorem reject01812 : Rejected (base 0 25 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 12) _ validLayout0104) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind01812_0) certificate0056

private theorem bind01813_0 : Agrees (spec (fastBase 0 25 13) layout0104) scope0061 := by decide

theorem reject01813 : Rejected (base 0 25 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 13) _ validLayout0104) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind01813_0) certificate0063

private theorem bind01814_0 : Agrees (spec (fastBase 0 25 14) layout0103) scope0194 := by decide

theorem reject01814 : Rejected (base 0 25 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 14) _ validLayout0103) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind01814_0) certificate0197

private theorem bind01815_0 : Agrees (spec (fastBase 0 25 15) layout0103) scope0199 := by decide

theorem reject01815 : Rejected (base 0 25 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 15) _ validLayout0103) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind01815_0) certificate0202

private theorem bind01816_0 : Agrees (spec (fastBase 0 25 16) layout0103) scope0177 := by decide

theorem reject01816 : Rejected (base 0 25 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 16) _ validLayout0103) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01816_0) certificate0180

private theorem bind01817_0 : Agrees (spec (fastBase 0 25 17) layout0103) scope0177 := by decide

theorem reject01817 : Rejected (base 0 25 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 17) _ validLayout0103) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01817_0) certificate0180

private theorem bind01818_0 : Agrees (spec (fastBase 0 25 18) layout0104) scope0062 := by decide

private theorem bind01818_1 : Agrees (spec (fastBase 0 25 18) layout0105) scope0380 := by decide

theorem reject01818 : Rejected (base 0 25 18) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 18) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 18) _ validLayout0105) (by decide) (by decide) scope0062 scope0380 (by rw [← fastBase_exact]; exact bind01818_0) (by rw [← fastBase_exact]; exact bind01818_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0389 (by decide)

private theorem bind01819_0 : Agrees (spec (fastBase 0 25 19) layout0103) scope0176 := by decide

theorem reject01819 : Rejected (base 0 25 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 19) _ validLayout0103) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01819_0) certificate0179

private theorem bind01820_0 : Agrees (spec (fastBase 0 25 20) layout0103) scope0192 := by decide

theorem reject01820 : Rejected (base 0 25 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 20) _ validLayout0103) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind01820_0) certificate0195

private theorem bind01821_0 : Agrees (spec (fastBase 0 25 21) layout0103) scope0200 := by decide

theorem reject01821 : Rejected (base 0 25 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 21) _ validLayout0103) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind01821_0) certificate0203

private theorem bind01822_0 : Agrees (spec (fastBase 0 25 22) layout0103) scope0177 := by decide

theorem reject01822 : Rejected (base 0 25 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 22) _ validLayout0103) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01822_0) certificate0180

private theorem bind01823_0 : Agrees (spec (fastBase 0 25 23) layout0103) scope0192 := by decide

theorem reject01823 : Rejected (base 0 25 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 23) _ validLayout0103) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind01823_0) certificate0195

private theorem bind01824_0 : Agrees (spec (fastBase 0 25 24) layout0104) scope0062 := by decide

private theorem bind01824_1 : Agrees (spec (fastBase 0 25 24) layout0105) scope0057 := by decide

theorem reject01824 : Rejected (base 0 25 24) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 24) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 24) _ validLayout0105) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind01824_0) (by rw [← fastBase_exact]; exact bind01824_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind01825_0 : Agrees (spec (fastBase 0 25 25) layout0103) scope0186 := by decide

theorem reject01825 : Rejected (base 0 25 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 25) _ validLayout0103) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01825_0) certificate0189

private theorem bind01826_0 : Agrees (spec (fastBase 0 25 26) layout0103) scope0193 := by decide

theorem reject01826 : Rejected (base 0 25 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 26) _ validLayout0103) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind01826_0) certificate0196

private theorem bind01827_0 : Agrees (spec (fastBase 0 25 27) layout0104) scope0054 := by decide

theorem reject01827 : Rejected (base 0 25 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 27) _ validLayout0104) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind01827_0) certificate0056

private theorem bind01828_0 : Agrees (spec (fastBase 0 25 28) layout0104) scope0061 := by decide

theorem reject01828 : Rejected (base 0 25 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 28) _ validLayout0104) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind01828_0) certificate0063

private theorem bind01829_0 : Agrees (spec (fastBase 0 25 29) layout0105) scope0377 := by decide

theorem reject01829 : Rejected (base 0 25 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 29) _ validLayout0105) (by decide) scope0377 (by rw [← fastBase_exact]; exact bind01829_0) certificate0386

private theorem bind01830_0 : Agrees (spec (fastBase 0 25 30) layout0104) scope0062 := by decide

private theorem bind01830_1 : Agrees (spec (fastBase 0 25 30) layout0105) scope0063 := by decide

theorem reject01830 : Rejected (base 0 25 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 30) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 30) _ validLayout0105) (by decide) (by decide) scope0062 scope0063 (by rw [← fastBase_exact]; exact bind01830_0) (by rw [← fastBase_exact]; exact bind01830_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0065 (by decide)

private theorem bind01831_0 : Agrees (spec (fastBase 0 25 31) layout0104) scope0062 := by decide

private theorem bind01831_1 : Agrees (spec (fastBase 0 25 31) layout0105) scope0057 := by decide

theorem reject01831 : Rejected (base 0 25 31) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 31) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 31) _ validLayout0105) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind01831_0) (by rw [← fastBase_exact]; exact bind01831_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind01832_0 : Agrees (spec (fastBase 0 25 32) layout0104) scope0064 := by decide

theorem reject01832 : Rejected (base 0 25 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 32) _ validLayout0104) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind01832_0) certificate0066

private theorem bind01833_0 : Agrees (spec (fastBase 0 25 33) layout0103) scope0194 := by decide

theorem reject01833 : Rejected (base 0 25 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 33) _ validLayout0103) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind01833_0) certificate0197

private theorem bind01834_0 : Agrees (spec (fastBase 0 25 34) layout0104) scope0065 := by decide

theorem reject01834 : Rejected (base 0 25 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 34) _ validLayout0104) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind01834_0) certificate0067

private theorem bind01835_0 : Agrees (spec (fastBase 0 25 35) layout0103) scope0176 := by decide

theorem reject01835 : Rejected (base 0 25 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 35) _ validLayout0103) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01835_0) certificate0179

private theorem bind01836_0 : Agrees (spec (fastBase 0 25 36) layout0103) scope0196 := by decide

theorem reject01836 : Rejected (base 0 25 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 36) _ validLayout0103) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind01836_0) certificate0199

private theorem bind01837_0 : Agrees (spec (fastBase 0 25 37) layout0103) scope0200 := by decide

theorem reject01837 : Rejected (base 0 25 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 37) _ validLayout0103) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind01837_0) certificate0203

private theorem bind01838_0 : Agrees (spec (fastBase 0 25 38) layout0103) scope0176 := by decide

theorem reject01838 : Rejected (base 0 25 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 38) _ validLayout0103) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01838_0) certificate0179

private theorem bind01839_0 : Agrees (spec (fastBase 0 25 39) layout0104) scope0065 := by decide

theorem reject01839 : Rejected (base 0 25 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 39) _ validLayout0104) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind01839_0) certificate0067

private theorem bind01840_0 : Agrees (spec (fastBase 0 25 40) layout0103) scope0191 := by decide

theorem reject01840 : Rejected (base 0 25 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 40) _ validLayout0103) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01840_0) certificate0194

private theorem bind01841_0 : Agrees (spec (fastBase 0 25 41) layout0103) scope0201 := by decide

theorem reject01841 : Rejected (base 0 25 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 41) _ validLayout0103) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind01841_0) certificate0204

private theorem bind01842_0 : Agrees (spec (fastBase 0 25 42) layout0103) scope0199 := by decide

theorem reject01842 : Rejected (base 0 25 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 42) _ validLayout0103) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind01842_0) certificate0202

private theorem bind01843_0 : Agrees (spec (fastBase 0 25 43) layout0104) scope0056 := by decide

theorem reject01843 : Rejected (base 0 25 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 43) _ validLayout0104) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind01843_0) certificate0058

private theorem bind01844_0 : Agrees (spec (fastBase 0 25 44) layout0103) scope0186 := by decide

theorem reject01844 : Rejected (base 0 25 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 44) _ validLayout0103) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01844_0) certificate0189

private theorem bind01845_0 : Agrees (spec (fastBase 0 25 45) layout0104) scope0076 := by decide

private theorem bind01845_1 : Agrees (spec (fastBase 0 25 45) layout0105) scope0063 := by decide

theorem reject01845 : Rejected (base 0 25 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 45) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 45) _ validLayout0105) (by decide) (by decide) scope0076 scope0063 (by rw [← fastBase_exact]; exact bind01845_0) (by rw [← fastBase_exact]; exact bind01845_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0078 certificate0079 (by decide)

private theorem bind01846_0 : Agrees (spec (fastBase 0 25 46) layout0103) scope0202 := by decide

theorem reject01846 : Rejected (base 0 25 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 46) _ validLayout0103) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind01846_0) certificate0205

private theorem bind01847_0 : Agrees (spec (fastBase 0 25 47) layout0103) scope0193 := by decide

theorem reject01847 : Rejected (base 0 25 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 47) _ validLayout0103) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind01847_0) certificate0196

private theorem bind01848_0 : Agrees (spec (fastBase 0 25 48) layout0105) scope0057 := by decide

private theorem bind01848_1 : Agrees (spec (fastBase 0 25 48) layout0106) scope0381 := by decide

theorem reject01848 : Rejected (base 0 25 48) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0105 layout0106 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 48) _ validLayout0105) (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 48) _ validLayout0106) (by decide) (by decide) scope0057 scope0381 (by rw [← fastBase_exact]; exact bind01848_0) (by rw [← fastBase_exact]; exact bind01848_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0059 certificate0390 (by decide)

private theorem bind01849_0 : Agrees (spec (fastBase 0 25 49) layout0103) scope0186 := by decide

theorem reject01849 : Rejected (base 0 25 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 49) _ validLayout0103) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01849_0) certificate0189

private theorem bind01850_0 : Agrees (spec (fastBase 0 25 50) layout0103) scope0207 := by decide

theorem reject01850 : Rejected (base 0 25 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 50) _ validLayout0103) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind01850_0) certificate0210

private theorem bind01851_0 : Agrees (spec (fastBase 0 25 51) layout0103) scope0185 := by decide

theorem reject01851 : Rejected (base 0 25 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 51) _ validLayout0103) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01851_0) certificate0188

private theorem bind01852_0 : Agrees (spec (fastBase 0 25 52) layout0103) scope0184 := by decide

theorem reject01852 : Rejected (base 0 25 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 52) _ validLayout0103) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01852_0) certificate0187

private theorem bind01853_0 : Agrees (spec (fastBase 0 25 53) layout0103) scope0184 := by decide

theorem reject01853 : Rejected (base 0 25 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 53) _ validLayout0103) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01853_0) certificate0187

private theorem bind01854_0 : Agrees (spec (fastBase 0 25 54) layout0103) scope0184 := by decide

theorem reject01854 : Rejected (base 0 25 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 54) _ validLayout0103) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01854_0) certificate0187

private theorem bind01855_0 : Agrees (spec (fastBase 0 25 55) layout0103) scope0184 := by decide

theorem reject01855 : Rejected (base 0 25 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 55) _ validLayout0103) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01855_0) certificate0187

private theorem bind01856_0 : Agrees (spec (fastBase 0 25 56) layout0103) scope0184 := by decide

theorem reject01856 : Rejected (base 0 25 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 56) _ validLayout0103) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01856_0) certificate0187

private theorem bind01857_0 : Agrees (spec (fastBase 0 25 57) layout0103) scope0196 := by decide

theorem reject01857 : Rejected (base 0 25 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 57) _ validLayout0103) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind01857_0) certificate0199

private theorem bind01858_0 : Agrees (spec (fastBase 0 25 58) layout0104) scope0060 := by decide

theorem reject01858 : Rejected (base 0 25 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 58) _ validLayout0104) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind01858_0) certificate0062

private theorem bind01859_0 : Agrees (spec (fastBase 0 25 59) layout0103) scope0191 := by decide

theorem reject01859 : Rejected (base 0 25 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 59) _ validLayout0103) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01859_0) certificate0194

private theorem bind01860_0 : Agrees (spec (fastBase 0 25 60) layout0103) scope0203 := by decide

theorem reject01860 : Rejected (base 0 25 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 60) _ validLayout0103) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind01860_0) certificate0206

private theorem bind01861_0 : Agrees (spec (fastBase 0 25 61) layout0104) scope0066 := by decide

theorem reject01861 : Rejected (base 0 25 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 61) _ validLayout0104) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind01861_0) certificate0068

private theorem bind01862_0 : Agrees (spec (fastBase 0 25 62) layout0103) scope0202 := by decide

theorem reject01862 : Rejected (base 0 25 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 62) _ validLayout0103) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind01862_0) certificate0205

private theorem bind01863_0 : Agrees (spec (fastBase 0 25 63) layout0103) scope0203 := by decide

theorem reject01863 : Rejected (base 0 25 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 63) _ validLayout0103) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind01863_0) certificate0206

private theorem bind01864_0 : Agrees (spec (fastBase 0 25 64) layout0104) scope0067 := by decide

theorem reject01864 : Rejected (base 0 25 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 64) _ validLayout0104) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind01864_0) certificate0069

private theorem bind01865_0 : Agrees (spec (fastBase 0 25 65) layout0103) scope0185 := by decide

theorem reject01865 : Rejected (base 0 25 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 65) _ validLayout0103) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01865_0) certificate0188

private theorem bind01866_0 : Agrees (spec (fastBase 0 25 66) layout0104) scope0066 := by decide

theorem reject01866 : Rejected (base 0 25 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 66) _ validLayout0104) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind01866_0) certificate0068

private theorem bind01867_0 : Agrees (spec (fastBase 0 25 67) layout0104) scope0066 := by decide

theorem reject01867 : Rejected (base 0 25 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 67) _ validLayout0104) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind01867_0) certificate0068

private theorem bind01868_0 : Agrees (spec (fastBase 0 25 68) layout0103) scope0201 := by decide

theorem reject01868 : Rejected (base 0 25 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 68) _ validLayout0103) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind01868_0) certificate0204

private theorem bind01869_0 : Agrees (spec (fastBase 0 25 69) layout0103) scope0207 := by decide

theorem reject01869 : Rejected (base 0 25 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 69) _ validLayout0103) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind01869_0) certificate0210

private theorem bind01870_0 : Agrees (spec (fastBase 0 25 70) layout0103) scope0191 := by decide

theorem reject01870 : Rejected (base 0 25 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 70) _ validLayout0103) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01870_0) certificate0194

private theorem bind01871_0 : Agrees (spec (fastBase 0 25 71) layout0103) scope0185 := by decide

theorem reject01871 : Rejected (base 0 25 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 0 25 71) _ validLayout0103) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01871_0) certificate0188

theorem allCases025 : ∀ y : Fin 72, Rejected (base 0 25 y) := by
  intro y
  fin_cases y

  · exact reject01800

  · exact reject01801

  · exact reject01802

  · exact reject01803

  · exact reject01804

  · exact reject01805

  · exact reject01806

  · exact reject01807

  · exact reject01808

  · exact reject01809

  · exact reject01810

  · exact reject01811

  · exact reject01812

  · exact reject01813

  · exact reject01814

  · exact reject01815

  · exact reject01816

  · exact reject01817

  · exact reject01818

  · exact reject01819

  · exact reject01820

  · exact reject01821

  · exact reject01822

  · exact reject01823

  · exact reject01824

  · exact reject01825

  · exact reject01826

  · exact reject01827

  · exact reject01828

  · exact reject01829

  · exact reject01830

  · exact reject01831

  · exact reject01832

  · exact reject01833

  · exact reject01834

  · exact reject01835

  · exact reject01836

  · exact reject01837

  · exact reject01838

  · exact reject01839

  · exact reject01840

  · exact reject01841

  · exact reject01842

  · exact reject01843

  · exact reject01844

  · exact reject01845

  · exact reject01846

  · exact reject01847

  · exact reject01848

  · exact reject01849

  · exact reject01850

  · exact reject01851

  · exact reject01852

  · exact reject01853

  · exact reject01854

  · exact reject01855

  · exact reject01856

  · exact reject01857

  · exact reject01858

  · exact reject01859

  · exact reject01860

  · exact reject01861

  · exact reject01862

  · exact reject01863

  · exact reject01864

  · exact reject01865

  · exact reject01866

  · exact reject01867

  · exact reject01868

  · exact reject01869

  · exact reject01870

  · exact reject01871

end PricingIntegration.RemainingGWitnesses
