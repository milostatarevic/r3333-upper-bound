import PricingIntegration.RemainingGLayouts019

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks005

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks026


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02808_0 : Agrees (spec (fastBase 0 39 0) layout0152) scope0088 := by decide

theorem reject02808 : Rejected (base 0 39 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 0) _ validLayout0152) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind02808_0) certificate0091

private theorem bind02809_0 : Agrees (spec (fastBase 0 39 1) layout0152) scope0090 := by decide

theorem reject02809 : Rejected (base 0 39 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 1) _ validLayout0152) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind02809_0) certificate0093

private theorem bind02810_0 : Agrees (spec (fastBase 0 39 2) layout0152) scope0083 := by decide

theorem reject02810 : Rejected (base 0 39 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 2) _ validLayout0152) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind02810_0) certificate0086

private theorem bind02811_0 : Agrees (spec (fastBase 0 39 3) layout0153) scope0091 := by decide

private theorem bind02811_1 : Agrees (spec (fastBase 0 39 3) layout0154) scope0407 := by decide

theorem reject02811 : Rejected (base 0 39 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0153 layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 3) _ validLayout0153) (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 3) _ validLayout0154) (by decide) (by decide) scope0091 scope0407 (by rw [← fastBase_exact]; exact bind02811_0) (by rw [← fastBase_exact]; exact bind02811_1) 2 7 1 6 (by decide) (by decide) 3 2 (by decide) certificate0424 certificate0425 (by decide)

private theorem bind02812_0 : Agrees (spec (fastBase 0 39 4) layout0152) scope0082 := by decide

theorem reject02812 : Rejected (base 0 39 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 4) _ validLayout0152) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind02812_0) certificate0085

private theorem bind02813_0 : Agrees (spec (fastBase 0 39 5) layout0152) scope0089 := by decide

theorem reject02813 : Rejected (base 0 39 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 5) _ validLayout0152) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind02813_0) certificate0092

private theorem bind02814_0 : Agrees (spec (fastBase 0 39 6) layout0152) scope0086 := by decide

theorem reject02814 : Rejected (base 0 39 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 6) _ validLayout0152) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind02814_0) certificate0089

private theorem bind02815_0 : Agrees (spec (fastBase 0 39 7) layout0153) scope0094 := by decide

private theorem bind02815_1 : Agrees (spec (fastBase 0 39 7) layout0154) scope0398 := by decide

theorem reject02815 : Rejected (base 0 39 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0153 layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 7) _ validLayout0153) (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 7) _ validLayout0154) (by decide) (by decide) scope0094 scope0398 (by rw [← fastBase_exact]; exact bind02815_0) (by rw [← fastBase_exact]; exact bind02815_1) 2 7 1 6 (by decide) (by decide) 3 2 (by decide) certificate0426 certificate0427 (by decide)

private theorem bind02816_0 : Agrees (spec (fastBase 0 39 8) layout0152) scope0084 := by decide

theorem reject02816 : Rejected (base 0 39 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 8) _ validLayout0152) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind02816_0) certificate0087

private theorem bind02817_0 : Agrees (spec (fastBase 0 39 9) layout0152) scope0093 := by decide

theorem reject02817 : Rejected (base 0 39 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 9) _ validLayout0152) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind02817_0) certificate0096

private theorem bind02818_0 : Agrees (spec (fastBase 0 39 10) layout0152) scope0085 := by decide

theorem reject02818 : Rejected (base 0 39 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 10) _ validLayout0152) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind02818_0) certificate0088

private theorem bind02819_0 : Agrees (spec (fastBase 0 39 11) layout0152) scope0087 := by decide

theorem reject02819 : Rejected (base 0 39 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 11) _ validLayout0152) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind02819_0) certificate0090

private theorem bind02820_0 : Agrees (spec (fastBase 0 39 12) layout0152) scope0104 := by decide

theorem reject02820 : Rejected (base 0 39 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 12) _ validLayout0152) (by decide) scope0104 (by rw [← fastBase_exact]; exact bind02820_0) certificate0107

private theorem bind02821_0 : Agrees (spec (fastBase 0 39 13) layout0155) scope0408 := by decide

theorem reject02821 : Rejected (base 0 39 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0155 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 13) _ validLayout0155) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind02821_0) certificate0428

private theorem bind02822_0 : Agrees (spec (fastBase 0 39 14) layout0152) scope0089 := by decide

theorem reject02822 : Rejected (base 0 39 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 14) _ validLayout0152) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind02822_0) certificate0092

private theorem bind02823_0 : Agrees (spec (fastBase 0 39 15) layout0155) scope0166 := by decide

theorem reject02823 : Rejected (base 0 39 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0155 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 15) _ validLayout0155) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind02823_0) certificate0169

private theorem bind02824_0 : Agrees (spec (fastBase 0 39 16) layout0152) scope0088 := by decide

theorem reject02824 : Rejected (base 0 39 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 16) _ validLayout0152) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind02824_0) certificate0091

private theorem bind02825_0 : Agrees (spec (fastBase 0 39 17) layout0152) scope0101 := by decide

theorem reject02825 : Rejected (base 0 39 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 17) _ validLayout0152) (by decide) scope0101 (by rw [← fastBase_exact]; exact bind02825_0) certificate0104

private theorem bind02826_0 : Agrees (spec (fastBase 0 39 18) layout0152) scope0090 := by decide

theorem reject02826 : Rejected (base 0 39 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 18) _ validLayout0152) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind02826_0) certificate0093

private theorem bind02827_0 : Agrees (spec (fastBase 0 39 19) layout0152) scope0102 := by decide

theorem reject02827 : Rejected (base 0 39 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 19) _ validLayout0152) (by decide) scope0102 (by rw [← fastBase_exact]; exact bind02827_0) certificate0105

private theorem bind02828_0 : Agrees (spec (fastBase 0 39 20) layout0152) scope0086 := by decide

theorem reject02828 : Rejected (base 0 39 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 20) _ validLayout0152) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind02828_0) certificate0089

private theorem bind02829_0 : Agrees (spec (fastBase 0 39 21) layout0152) scope0093 := by decide

theorem reject02829 : Rejected (base 0 39 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 21) _ validLayout0152) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind02829_0) certificate0096

private theorem bind02830_0 : Agrees (spec (fastBase 0 39 22) layout0152) scope0099 := by decide

theorem reject02830 : Rejected (base 0 39 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 22) _ validLayout0152) (by decide) scope0099 (by rw [← fastBase_exact]; exact bind02830_0) certificate0102

private theorem bind02831_0 : Agrees (spec (fastBase 0 39 23) layout0152) scope0082 := by decide

theorem reject02831 : Rejected (base 0 39 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 23) _ validLayout0152) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind02831_0) certificate0085

private theorem bind02832_0 : Agrees (spec (fastBase 0 39 24) layout0152) scope0083 := by decide

theorem reject02832 : Rejected (base 0 39 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 24) _ validLayout0152) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind02832_0) certificate0086

private theorem bind02833_0 : Agrees (spec (fastBase 0 39 25) layout0152) scope0098 := by decide

theorem reject02833 : Rejected (base 0 39 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 25) _ validLayout0152) (by decide) scope0098 (by rw [← fastBase_exact]; exact bind02833_0) certificate0101

private theorem bind02834_0 : Agrees (spec (fastBase 0 39 26) layout0152) scope0085 := by decide

theorem reject02834 : Rejected (base 0 39 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 26) _ validLayout0152) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind02834_0) certificate0088

private theorem bind02835_0 : Agrees (spec (fastBase 0 39 27) layout0153) scope0091 := by decide

private theorem bind02835_1 : Agrees (spec (fastBase 0 39 27) layout0154) scope0407 := by decide

theorem reject02835 : Rejected (base 0 39 27) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0153 layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 27) _ validLayout0153) (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 27) _ validLayout0154) (by decide) (by decide) scope0091 scope0407 (by rw [← fastBase_exact]; exact bind02835_0) (by rw [← fastBase_exact]; exact bind02835_1) 2 7 1 6 (by decide) (by decide) 3 2 (by decide) certificate0424 certificate0425 (by decide)

private theorem bind02836_0 : Agrees (spec (fastBase 0 39 28) layout0153) scope0083 := by decide

theorem reject02836 : Rejected (base 0 39 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0153 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 28) _ validLayout0153) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind02836_0) certificate0086

private theorem bind02837_0 : Agrees (spec (fastBase 0 39 29) layout0154) scope0403 := by decide

theorem reject02837 : Rejected (base 0 39 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 29) _ validLayout0154) (by decide) scope0403 (by rw [← fastBase_exact]; exact bind02837_0) certificate0418

private theorem bind02838_0 : Agrees (spec (fastBase 0 39 30) layout0153) scope0091 := by decide

private theorem bind02838_1 : Agrees (spec (fastBase 0 39 30) layout0154) scope0398 := by decide

theorem reject02838 : Rejected (base 0 39 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0153 layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 30) _ validLayout0153) (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 30) _ validLayout0154) (by decide) (by decide) scope0091 scope0398 (by rw [← fastBase_exact]; exact bind02838_0) (by rw [← fastBase_exact]; exact bind02838_1) 2 7 1 6 (by decide) (by decide) 3 2 (by decide) certificate0424 certificate0427 (by decide)

private theorem bind02839_0 : Agrees (spec (fastBase 0 39 31) layout0153) scope0087 := by decide

theorem reject02839 : Rejected (base 0 39 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0153 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 31) _ validLayout0153) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind02839_0) certificate0090

private theorem bind02840_0 : Agrees (spec (fastBase 0 39 32) layout0152) scope0097 := by decide

theorem reject02840 : Rejected (base 0 39 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 32) _ validLayout0152) (by decide) scope0097 (by rw [← fastBase_exact]; exact bind02840_0) certificate0100

private theorem bind02841_0 : Agrees (spec (fastBase 0 39 33) layout0152) scope0083 := by decide

theorem reject02841 : Rejected (base 0 39 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 33) _ validLayout0152) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind02841_0) certificate0086

private theorem bind02842_0 : Agrees (spec (fastBase 0 39 34) layout0152) scope0096 := by decide

theorem reject02842 : Rejected (base 0 39 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 34) _ validLayout0152) (by decide) scope0096 (by rw [← fastBase_exact]; exact bind02842_0) certificate0099

private theorem bind02843_0 : Agrees (spec (fastBase 0 39 35) layout0152) scope0082 := by decide

theorem reject02843 : Rejected (base 0 39 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 35) _ validLayout0152) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind02843_0) certificate0085

private theorem bind02844_0 : Agrees (spec (fastBase 0 39 36) layout0152) scope0087 := by decide

theorem reject02844 : Rejected (base 0 39 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 36) _ validLayout0152) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind02844_0) certificate0090

private theorem bind02845_0 : Agrees (spec (fastBase 0 39 37) layout0152) scope0088 := by decide

theorem reject02845 : Rejected (base 0 39 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 37) _ validLayout0152) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind02845_0) certificate0091

private theorem bind02846_0 : Agrees (spec (fastBase 0 39 38) layout0152) scope0099 := by decide

theorem reject02846 : Rejected (base 0 39 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 38) _ validLayout0152) (by decide) scope0099 (by rw [← fastBase_exact]; exact bind02846_0) certificate0102

private theorem bind02847_0 : Agrees (spec (fastBase 0 39 39) layout0152) scope0089 := by decide

theorem reject02847 : Rejected (base 0 39 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 39) _ validLayout0152) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind02847_0) certificate0092

private theorem bind02848_0 : Agrees (spec (fastBase 0 39 40) layout0152) scope0100 := by decide

theorem reject02848 : Rejected (base 0 39 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 40) _ validLayout0152) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind02848_0) certificate0103

private theorem bind02849_0 : Agrees (spec (fastBase 0 39 41) layout0152) scope0085 := by decide

theorem reject02849 : Rejected (base 0 39 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 41) _ validLayout0152) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind02849_0) certificate0088

private theorem bind02850_0 : Agrees (spec (fastBase 0 39 42) layout0152) scope0090 := by decide

theorem reject02850 : Rejected (base 0 39 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 42) _ validLayout0152) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind02850_0) certificate0093

private theorem bind02851_0 : Agrees (spec (fastBase 0 39 43) layout0152) scope0097 := by decide

theorem reject02851 : Rejected (base 0 39 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 43) _ validLayout0152) (by decide) scope0097 (by rw [← fastBase_exact]; exact bind02851_0) certificate0100

private theorem bind02852_0 : Agrees (spec (fastBase 0 39 44) layout0152) scope0086 := by decide

theorem reject02852 : Rejected (base 0 39 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 44) _ validLayout0152) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind02852_0) certificate0089

private theorem bind02853_0 : Agrees (spec (fastBase 0 39 45) layout0153) scope0101 := by decide

theorem reject02853 : Rejected (base 0 39 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0153 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 45) _ validLayout0153) (by decide) scope0101 (by rw [← fastBase_exact]; exact bind02853_0) certificate0104

private theorem bind02854_0 : Agrees (spec (fastBase 0 39 46) layout0152) scope0087 := by decide

theorem reject02854 : Rejected (base 0 39 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 46) _ validLayout0152) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind02854_0) certificate0090

private theorem bind02855_0 : Agrees (spec (fastBase 0 39 47) layout0152) scope0088 := by decide

theorem reject02855 : Rejected (base 0 39 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 47) _ validLayout0152) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind02855_0) certificate0091

private theorem bind02856_0 : Agrees (spec (fastBase 0 39 48) layout0153) scope0094 := by decide

private theorem bind02856_1 : Agrees (spec (fastBase 0 39 48) layout0154) scope0407 := by decide

theorem reject02856 : Rejected (base 0 39 48) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0153 layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 48) _ validLayout0153) (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 48) _ validLayout0154) (by decide) (by decide) scope0094 scope0407 (by rw [← fastBase_exact]; exact bind02856_0) (by rw [← fastBase_exact]; exact bind02856_1) 2 7 1 6 (by decide) (by decide) 3 2 (by decide) certificate0426 certificate0425 (by decide)

private theorem bind02857_0 : Agrees (spec (fastBase 0 39 49) layout0152) scope0101 := by decide

theorem reject02857 : Rejected (base 0 39 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 49) _ validLayout0152) (by decide) scope0101 (by rw [← fastBase_exact]; exact bind02857_0) certificate0104

private theorem bind02858_0 : Agrees (spec (fastBase 0 39 50) layout0152) scope0093 := by decide

theorem reject02858 : Rejected (base 0 39 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 50) _ validLayout0152) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind02858_0) certificate0096

private theorem bind02859_0 : Agrees (spec (fastBase 0 39 51) layout0152) scope0100 := by decide

theorem reject02859 : Rejected (base 0 39 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 51) _ validLayout0152) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind02859_0) certificate0103

private theorem bind02860_0 : Agrees (spec (fastBase 0 39 52) layout0152) scope0084 := by decide

theorem reject02860 : Rejected (base 0 39 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 52) _ validLayout0152) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind02860_0) certificate0087

private theorem bind02861_0 : Agrees (spec (fastBase 0 39 53) layout0152) scope0084 := by decide

theorem reject02861 : Rejected (base 0 39 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 53) _ validLayout0152) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind02861_0) certificate0087

private theorem bind02862_0 : Agrees (spec (fastBase 0 39 54) layout0152) scope0084 := by decide

theorem reject02862 : Rejected (base 0 39 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 54) _ validLayout0152) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind02862_0) certificate0087

private theorem bind02863_0 : Agrees (spec (fastBase 0 39 55) layout0152) scope0084 := by decide

theorem reject02863 : Rejected (base 0 39 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 55) _ validLayout0152) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind02863_0) certificate0087

private theorem bind02864_0 : Agrees (spec (fastBase 0 39 56) layout0152) scope0084 := by decide

theorem reject02864 : Rejected (base 0 39 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 56) _ validLayout0152) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind02864_0) certificate0087

private theorem bind02865_0 : Agrees (spec (fastBase 0 39 57) layout0152) scope0090 := by decide

theorem reject02865 : Rejected (base 0 39 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 57) _ validLayout0152) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind02865_0) certificate0093

private theorem bind02866_0 : Agrees (spec (fastBase 0 39 58) layout0152) scope0104 := by decide

theorem reject02866 : Rejected (base 0 39 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 58) _ validLayout0152) (by decide) scope0104 (by rw [← fastBase_exact]; exact bind02866_0) certificate0107

private theorem bind02867_0 : Agrees (spec (fastBase 0 39 59) layout0152) scope0093 := by decide

theorem reject02867 : Rejected (base 0 39 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 59) _ validLayout0152) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind02867_0) certificate0096

private theorem bind02868_0 : Agrees (spec (fastBase 0 39 60) layout0153) scope0094 := by decide

private theorem bind02868_1 : Agrees (spec (fastBase 0 39 60) layout0154) scope0409 := by decide

theorem reject02868 : Rejected (base 0 39 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0153 layout0154 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 60) _ validLayout0153) (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 60) _ validLayout0154) (by decide) (by decide) scope0094 scope0409 (by rw [← fastBase_exact]; exact bind02868_0) (by rw [← fastBase_exact]; exact bind02868_1) 2 7 1 6 (by decide) (by decide) 3 2 (by decide) certificate0426 certificate0429 (by decide)

private theorem bind02869_0 : Agrees (spec (fastBase 0 39 61) layout0155) scope0410 := by decide

theorem reject02869 : Rejected (base 0 39 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0155 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 61) _ validLayout0155) (by decide) scope0410 (by rw [← fastBase_exact]; exact bind02869_0) certificate0430

private theorem bind02870_0 : Agrees (spec (fastBase 0 39 62) layout0152) scope0083 := by decide

theorem reject02870 : Rejected (base 0 39 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 62) _ validLayout0152) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind02870_0) certificate0086

private theorem bind02871_0 : Agrees (spec (fastBase 0 39 63) layout0152) scope0089 := by decide

theorem reject02871 : Rejected (base 0 39 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 63) _ validLayout0152) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind02871_0) certificate0092

private theorem bind02872_0 : Agrees (spec (fastBase 0 39 64) layout0153) scope0100 := by decide

theorem reject02872 : Rejected (base 0 39 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0153 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 64) _ validLayout0153) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind02872_0) certificate0103

private theorem bind02873_0 : Agrees (spec (fastBase 0 39 65) layout0152) scope0085 := by decide

theorem reject02873 : Rejected (base 0 39 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 65) _ validLayout0152) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind02873_0) certificate0088

private theorem bind02874_0 : Agrees (spec (fastBase 0 39 66) layout0152) scope0096 := by decide

theorem reject02874 : Rejected (base 0 39 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 66) _ validLayout0152) (by decide) scope0096 (by rw [← fastBase_exact]; exact bind02874_0) certificate0099

private theorem bind02875_0 : Agrees (spec (fastBase 0 39 67) layout0152) scope0087 := by decide

theorem reject02875 : Rejected (base 0 39 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 67) _ validLayout0152) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind02875_0) certificate0090

private theorem bind02876_0 : Agrees (spec (fastBase 0 39 68) layout0152) scope0082 := by decide

theorem reject02876 : Rejected (base 0 39 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 68) _ validLayout0152) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind02876_0) certificate0085

private theorem bind02877_0 : Agrees (spec (fastBase 0 39 69) layout0152) scope0086 := by decide

theorem reject02877 : Rejected (base 0 39 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 69) _ validLayout0152) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind02877_0) certificate0089

private theorem bind02878_0 : Agrees (spec (fastBase 0 39 70) layout0152) scope0102 := by decide

theorem reject02878 : Rejected (base 0 39 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 70) _ validLayout0152) (by decide) scope0102 (by rw [← fastBase_exact]; exact bind02878_0) certificate0105

private theorem bind02879_0 : Agrees (spec (fastBase 0 39 71) layout0152) scope0098 := by decide

theorem reject02879 : Rejected (base 0 39 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0152 (layoutValid_of_refines _ _ (base_refines_skeleton 0 39 71) _ validLayout0152) (by decide) scope0098 (by rw [← fastBase_exact]; exact bind02879_0) certificate0101

theorem allCases039 : ∀ y : Fin 72, Rejected (base 0 39 y) := by
  intro y
  fin_cases y

  · exact reject02808

  · exact reject02809

  · exact reject02810

  · exact reject02811

  · exact reject02812

  · exact reject02813

  · exact reject02814

  · exact reject02815

  · exact reject02816

  · exact reject02817

  · exact reject02818

  · exact reject02819

  · exact reject02820

  · exact reject02821

  · exact reject02822

  · exact reject02823

  · exact reject02824

  · exact reject02825

  · exact reject02826

  · exact reject02827

  · exact reject02828

  · exact reject02829

  · exact reject02830

  · exact reject02831

  · exact reject02832

  · exact reject02833

  · exact reject02834

  · exact reject02835

  · exact reject02836

  · exact reject02837

  · exact reject02838

  · exact reject02839

  · exact reject02840

  · exact reject02841

  · exact reject02842

  · exact reject02843

  · exact reject02844

  · exact reject02845

  · exact reject02846

  · exact reject02847

  · exact reject02848

  · exact reject02849

  · exact reject02850

  · exact reject02851

  · exact reject02852

  · exact reject02853

  · exact reject02854

  · exact reject02855

  · exact reject02856

  · exact reject02857

  · exact reject02858

  · exact reject02859

  · exact reject02860

  · exact reject02861

  · exact reject02862

  · exact reject02863

  · exact reject02864

  · exact reject02865

  · exact reject02866

  · exact reject02867

  · exact reject02868

  · exact reject02869

  · exact reject02870

  · exact reject02871

  · exact reject02872

  · exact reject02873

  · exact reject02874

  · exact reject02875

  · exact reject02876

  · exact reject02877

  · exact reject02878

  · exact reject02879

end PricingIntegration.RemainingGWitnesses
