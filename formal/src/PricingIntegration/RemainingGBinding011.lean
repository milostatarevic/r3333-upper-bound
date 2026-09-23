import PricingIntegration.RemainingGLayouts006

import PricingIntegration.RemainingGLayouts007

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks021

import PricingIntegration.RemainingGScopeChecks022


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00792_0 : Agrees (spec (fastBase 0 11 0) layout0054) scope0323 := by decide

theorem reject00792 : Rejected (base 0 11 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 0) _ validLayout0054) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind00792_0) certificate0330

private theorem bind00793_0 : Agrees (spec (fastBase 0 11 1) layout0054) scope0324 := by decide

theorem reject00793 : Rejected (base 0 11 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 1) _ validLayout0054) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind00793_0) certificate0331

private theorem bind00794_0 : Agrees (spec (fastBase 0 11 2) layout0054) scope0325 := by decide

theorem reject00794 : Rejected (base 0 11 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 2) _ validLayout0054) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind00794_0) certificate0332

private theorem bind00795_0 : Agrees (spec (fastBase 0 11 3) layout0054) scope0326 := by decide

theorem reject00795 : Rejected (base 0 11 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 3) _ validLayout0054) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind00795_0) certificate0333

private theorem bind00796_0 : Agrees (spec (fastBase 0 11 4) layout0055) scope0327 := by decide

private theorem bind00796_1 : Agrees (spec (fastBase 0 11 4) layout0056) scope0328 := by decide

theorem reject00796 : Rejected (base 0 11 4) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0055 layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 4) _ validLayout0055) (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 4) _ validLayout0056) (by decide) (by decide) scope0327 scope0328 (by rw [← fastBase_exact]; exact bind00796_0) (by rw [← fastBase_exact]; exact bind00796_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0335 (by decide)

private theorem bind00797_0 : Agrees (spec (fastBase 0 11 5) layout0054) scope0329 := by decide

theorem reject00797 : Rejected (base 0 11 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 5) _ validLayout0054) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind00797_0) certificate0336

private theorem bind00798_0 : Agrees (spec (fastBase 0 11 6) layout0054) scope0330 := by decide

theorem reject00798 : Rejected (base 0 11 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 6) _ validLayout0054) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind00798_0) certificate0337

private theorem bind00799_0 : Agrees (spec (fastBase 0 11 7) layout0054) scope0331 := by decide

theorem reject00799 : Rejected (base 0 11 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 7) _ validLayout0054) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind00799_0) certificate0338

private theorem bind00800_0 : Agrees (spec (fastBase 0 11 8) layout0055) scope0332 := by decide

private theorem bind00800_1 : Agrees (spec (fastBase 0 11 8) layout0056) scope0333 := by decide

theorem reject00800 : Rejected (base 0 11 8) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0055 layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 8) _ validLayout0055) (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 8) _ validLayout0056) (by decide) (by decide) scope0332 scope0333 (by rw [← fastBase_exact]; exact bind00800_0) (by rw [← fastBase_exact]; exact bind00800_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0340 (by decide)

private theorem bind00801_0 : Agrees (spec (fastBase 0 11 9) layout0054) scope0334 := by decide

theorem reject00801 : Rejected (base 0 11 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 9) _ validLayout0054) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind00801_0) certificate0341

private theorem bind00802_0 : Agrees (spec (fastBase 0 11 10) layout0054) scope0335 := by decide

theorem reject00802 : Rejected (base 0 11 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 10) _ validLayout0054) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind00802_0) certificate0342

private theorem bind00803_0 : Agrees (spec (fastBase 0 11 11) layout0054) scope0336 := by decide

theorem reject00803 : Rejected (base 0 11 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 11) _ validLayout0054) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind00803_0) certificate0343

private theorem bind00804_0 : Agrees (spec (fastBase 0 11 12) layout0054) scope0337 := by decide

theorem reject00804 : Rejected (base 0 11 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 12) _ validLayout0054) (by decide) scope0337 (by rw [← fastBase_exact]; exact bind00804_0) certificate0344

private theorem bind00805_0 : Agrees (spec (fastBase 0 11 13) layout0054) scope0325 := by decide

theorem reject00805 : Rejected (base 0 11 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 13) _ validLayout0054) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind00805_0) certificate0332

private theorem bind00806_0 : Agrees (spec (fastBase 0 11 14) layout0054) scope0329 := by decide

theorem reject00806 : Rejected (base 0 11 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 14) _ validLayout0054) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind00806_0) certificate0336

private theorem bind00807_0 : Agrees (spec (fastBase 0 11 15) layout0054) scope0323 := by decide

theorem reject00807 : Rejected (base 0 11 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 15) _ validLayout0054) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind00807_0) certificate0330

private theorem bind00808_0 : Agrees (spec (fastBase 0 11 16) layout0056) scope0338 := by decide

theorem reject00808 : Rejected (base 0 11 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 16) _ validLayout0056) (by decide) scope0338 (by rw [← fastBase_exact]; exact bind00808_0) certificate0345

private theorem bind00809_0 : Agrees (spec (fastBase 0 11 17) layout0054) scope0339 := by decide

theorem reject00809 : Rejected (base 0 11 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 17) _ validLayout0054) (by decide) scope0339 (by rw [← fastBase_exact]; exact bind00809_0) certificate0346

private theorem bind00810_0 : Agrees (spec (fastBase 0 11 18) layout0054) scope0326 := by decide

theorem reject00810 : Rejected (base 0 11 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 18) _ validLayout0054) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind00810_0) certificate0333

private theorem bind00811_0 : Agrees (spec (fastBase 0 11 19) layout0054) scope0324 := by decide

theorem reject00811 : Rejected (base 0 11 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 19) _ validLayout0054) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind00811_0) certificate0331

private theorem bind00812_0 : Agrees (spec (fastBase 0 11 20) layout0054) scope0340 := by decide

theorem reject00812 : Rejected (base 0 11 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 20) _ validLayout0054) (by decide) scope0340 (by rw [← fastBase_exact]; exact bind00812_0) certificate0347

private theorem bind00813_0 : Agrees (spec (fastBase 0 11 21) layout0054) scope0334 := by decide

theorem reject00813 : Rejected (base 0 11 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 21) _ validLayout0054) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind00813_0) certificate0341

private theorem bind00814_0 : Agrees (spec (fastBase 0 11 22) layout0054) scope0323 := by decide

theorem reject00814 : Rejected (base 0 11 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 22) _ validLayout0054) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind00814_0) certificate0330

private theorem bind00815_0 : Agrees (spec (fastBase 0 11 23) layout0054) scope0325 := by decide

theorem reject00815 : Rejected (base 0 11 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 23) _ validLayout0054) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind00815_0) certificate0332

private theorem bind00816_0 : Agrees (spec (fastBase 0 11 24) layout0054) scope0341 := by decide

theorem reject00816 : Rejected (base 0 11 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 24) _ validLayout0054) (by decide) scope0341 (by rw [← fastBase_exact]; exact bind00816_0) certificate0348

private theorem bind00817_0 : Agrees (spec (fastBase 0 11 25) layout0054) scope0342 := by decide

theorem reject00817 : Rejected (base 0 11 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 25) _ validLayout0054) (by decide) scope0342 (by rw [← fastBase_exact]; exact bind00817_0) certificate0349

private theorem bind00818_0 : Agrees (spec (fastBase 0 11 26) layout0054) scope0335 := by decide

theorem reject00818 : Rejected (base 0 11 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 26) _ validLayout0054) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind00818_0) certificate0342

private theorem bind00819_0 : Agrees (spec (fastBase 0 11 27) layout0054) scope0324 := by decide

theorem reject00819 : Rejected (base 0 11 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 27) _ validLayout0054) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind00819_0) certificate0331

private theorem bind00820_0 : Agrees (spec (fastBase 0 11 28) layout0054) scope0337 := by decide

theorem reject00820 : Rejected (base 0 11 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 28) _ validLayout0054) (by decide) scope0337 (by rw [← fastBase_exact]; exact bind00820_0) certificate0344

private theorem bind00821_0 : Agrees (spec (fastBase 0 11 29) layout0054) scope0329 := by decide

theorem reject00821 : Rejected (base 0 11 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 29) _ validLayout0054) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind00821_0) certificate0336

private theorem bind00822_0 : Agrees (spec (fastBase 0 11 30) layout0054) scope0326 := by decide

theorem reject00822 : Rejected (base 0 11 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 30) _ validLayout0054) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind00822_0) certificate0333

private theorem bind00823_0 : Agrees (spec (fastBase 0 11 31) layout0054) scope0343 := by decide

theorem reject00823 : Rejected (base 0 11 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 31) _ validLayout0054) (by decide) scope0343 (by rw [← fastBase_exact]; exact bind00823_0) certificate0350

private theorem bind00824_0 : Agrees (spec (fastBase 0 11 32) layout0056) scope0344 := by decide

theorem reject00824 : Rejected (base 0 11 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 32) _ validLayout0056) (by decide) scope0344 (by rw [← fastBase_exact]; exact bind00824_0) certificate0351

private theorem bind00825_0 : Agrees (spec (fastBase 0 11 33) layout0055) scope0327 := by decide

private theorem bind00825_1 : Agrees (spec (fastBase 0 11 33) layout0056) scope0328 := by decide

theorem reject00825 : Rejected (base 0 11 33) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0055 layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 33) _ validLayout0055) (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 33) _ validLayout0056) (by decide) (by decide) scope0327 scope0328 (by rw [← fastBase_exact]; exact bind00825_0) (by rw [← fastBase_exact]; exact bind00825_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0335 (by decide)

private theorem bind00826_0 : Agrees (spec (fastBase 0 11 34) layout0056) scope0345 := by decide

theorem reject00826 : Rejected (base 0 11 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 34) _ validLayout0056) (by decide) scope0345 (by rw [← fastBase_exact]; exact bind00826_0) certificate0352

private theorem bind00827_0 : Agrees (spec (fastBase 0 11 35) layout0055) scope0332 := by decide

private theorem bind00827_1 : Agrees (spec (fastBase 0 11 35) layout0056) scope0328 := by decide

theorem reject00827 : Rejected (base 0 11 35) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0055 layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 35) _ validLayout0055) (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 35) _ validLayout0056) (by decide) (by decide) scope0332 scope0328 (by rw [← fastBase_exact]; exact bind00827_0) (by rw [← fastBase_exact]; exact bind00827_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0335 (by decide)

private theorem bind00828_0 : Agrees (spec (fastBase 0 11 36) layout0055) scope0336 := by decide

theorem reject00828 : Rejected (base 0 11 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0055 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 36) _ validLayout0055) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind00828_0) certificate0343

private theorem bind00829_0 : Agrees (spec (fastBase 0 11 37) layout0054) scope0323 := by decide

theorem reject00829 : Rejected (base 0 11 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 37) _ validLayout0054) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind00829_0) certificate0330

private theorem bind00830_0 : Agrees (spec (fastBase 0 11 38) layout0054) scope0329 := by decide

theorem reject00830 : Rejected (base 0 11 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 38) _ validLayout0054) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind00830_0) certificate0336

private theorem bind00831_0 : Agrees (spec (fastBase 0 11 39) layout0054) scope0326 := by decide

theorem reject00831 : Rejected (base 0 11 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 39) _ validLayout0054) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind00831_0) certificate0333

private theorem bind00832_0 : Agrees (spec (fastBase 0 11 40) layout0054) scope0339 := by decide

theorem reject00832 : Rejected (base 0 11 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 40) _ validLayout0054) (by decide) scope0339 (by rw [← fastBase_exact]; exact bind00832_0) certificate0346

private theorem bind00833_0 : Agrees (spec (fastBase 0 11 41) layout0054) scope0341 := by decide

theorem reject00833 : Rejected (base 0 11 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 41) _ validLayout0054) (by decide) scope0341 (by rw [← fastBase_exact]; exact bind00833_0) certificate0348

private theorem bind00834_0 : Agrees (spec (fastBase 0 11 42) layout0055) scope0340 := by decide

theorem reject00834 : Rejected (base 0 11 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0055 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 42) _ validLayout0055) (by decide) scope0340 (by rw [← fastBase_exact]; exact bind00834_0) certificate0347

private theorem bind00835_0 : Agrees (spec (fastBase 0 11 43) layout0054) scope0346 := by decide

theorem reject00835 : Rejected (base 0 11 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 43) _ validLayout0054) (by decide) scope0346 (by rw [← fastBase_exact]; exact bind00835_0) certificate0353

private theorem bind00836_0 : Agrees (spec (fastBase 0 11 44) layout0055) scope0332 := by decide

private theorem bind00836_1 : Agrees (spec (fastBase 0 11 44) layout0056) scope0333 := by decide

theorem reject00836 : Rejected (base 0 11 44) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0055 layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 44) _ validLayout0055) (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 44) _ validLayout0056) (by decide) (by decide) scope0332 scope0333 (by rw [← fastBase_exact]; exact bind00836_0) (by rw [← fastBase_exact]; exact bind00836_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0340 (by decide)

private theorem bind00837_0 : Agrees (spec (fastBase 0 11 45) layout0054) scope0330 := by decide

theorem reject00837 : Rejected (base 0 11 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 45) _ validLayout0054) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind00837_0) certificate0337

private theorem bind00838_0 : Agrees (spec (fastBase 0 11 46) layout0054) scope0336 := by decide

theorem reject00838 : Rejected (base 0 11 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 46) _ validLayout0054) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind00838_0) certificate0343

private theorem bind00839_0 : Agrees (spec (fastBase 0 11 47) layout0054) scope0331 := by decide

theorem reject00839 : Rejected (base 0 11 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 47) _ validLayout0054) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind00839_0) certificate0338

private theorem bind00840_0 : Agrees (spec (fastBase 0 11 48) layout0054) scope0331 := by decide

theorem reject00840 : Rejected (base 0 11 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 48) _ validLayout0054) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind00840_0) certificate0338

private theorem bind00841_0 : Agrees (spec (fastBase 0 11 49) layout0054) scope0331 := by decide

theorem reject00841 : Rejected (base 0 11 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 49) _ validLayout0054) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind00841_0) certificate0338

private theorem bind00842_0 : Agrees (spec (fastBase 0 11 50) layout0054) scope0331 := by decide

theorem reject00842 : Rejected (base 0 11 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 50) _ validLayout0054) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind00842_0) certificate0338

private theorem bind00843_0 : Agrees (spec (fastBase 0 11 51) layout0054) scope0331 := by decide

theorem reject00843 : Rejected (base 0 11 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 51) _ validLayout0054) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind00843_0) certificate0338

private theorem bind00844_0 : Agrees (spec (fastBase 0 11 52) layout0054) scope0342 := by decide

theorem reject00844 : Rejected (base 0 11 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 52) _ validLayout0054) (by decide) scope0342 (by rw [← fastBase_exact]; exact bind00844_0) certificate0349

private theorem bind00845_0 : Agrees (spec (fastBase 0 11 53) layout0055) scope0327 := by decide

private theorem bind00845_1 : Agrees (spec (fastBase 0 11 53) layout0056) scope0333 := by decide

theorem reject00845 : Rejected (base 0 11 53) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0055 layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 53) _ validLayout0055) (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 53) _ validLayout0056) (by decide) (by decide) scope0327 scope0333 (by rw [← fastBase_exact]; exact bind00845_0) (by rw [← fastBase_exact]; exact bind00845_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0340 (by decide)

private theorem bind00846_0 : Agrees (spec (fastBase 0 11 54) layout0054) scope0330 := by decide

theorem reject00846 : Rejected (base 0 11 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 54) _ validLayout0054) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind00846_0) certificate0337

private theorem bind00847_0 : Agrees (spec (fastBase 0 11 55) layout0054) scope0347 := by decide

theorem reject00847 : Rejected (base 0 11 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 55) _ validLayout0054) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind00847_0) certificate0354

private theorem bind00848_0 : Agrees (spec (fastBase 0 11 56) layout0054) scope0335 := by decide

theorem reject00848 : Rejected (base 0 11 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 56) _ validLayout0054) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind00848_0) certificate0342

private theorem bind00849_0 : Agrees (spec (fastBase 0 11 57) layout0054) scope0324 := by decide

theorem reject00849 : Rejected (base 0 11 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 57) _ validLayout0054) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind00849_0) certificate0331

private theorem bind00850_0 : Agrees (spec (fastBase 0 11 58) layout0054) scope0343 := by decide

theorem reject00850 : Rejected (base 0 11 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 58) _ validLayout0054) (by decide) scope0343 (by rw [← fastBase_exact]; exact bind00850_0) certificate0350

private theorem bind00851_0 : Agrees (spec (fastBase 0 11 59) layout0056) scope0348 := by decide

theorem reject00851 : Rejected (base 0 11 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0056 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 59) _ validLayout0056) (by decide) scope0348 (by rw [← fastBase_exact]; exact bind00851_0) certificate0355

private theorem bind00852_0 : Agrees (spec (fastBase 0 11 60) layout0054) scope0334 := by decide

theorem reject00852 : Rejected (base 0 11 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 60) _ validLayout0054) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind00852_0) certificate0341

private theorem bind00853_0 : Agrees (spec (fastBase 0 11 61) layout0054) scope0336 := by decide

theorem reject00853 : Rejected (base 0 11 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 61) _ validLayout0054) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind00853_0) certificate0343

private theorem bind00854_0 : Agrees (spec (fastBase 0 11 62) layout0054) scope0325 := by decide

theorem reject00854 : Rejected (base 0 11 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 62) _ validLayout0054) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind00854_0) certificate0332

private theorem bind00855_0 : Agrees (spec (fastBase 0 11 63) layout0055) scope0341 := by decide

theorem reject00855 : Rejected (base 0 11 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0055 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 63) _ validLayout0055) (by decide) scope0341 (by rw [← fastBase_exact]; exact bind00855_0) certificate0348

private theorem bind00856_0 : Agrees (spec (fastBase 0 11 64) layout0054) scope0335 := by decide

theorem reject00856 : Rejected (base 0 11 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 64) _ validLayout0054) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind00856_0) certificate0342

private theorem bind00857_0 : Agrees (spec (fastBase 0 11 65) layout0055) scope0335 := by decide

theorem reject00857 : Rejected (base 0 11 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0055 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 65) _ validLayout0055) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind00857_0) certificate0342

private theorem bind00858_0 : Agrees (spec (fastBase 0 11 66) layout0054) scope0346 := by decide

theorem reject00858 : Rejected (base 0 11 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 66) _ validLayout0054) (by decide) scope0346 (by rw [← fastBase_exact]; exact bind00858_0) certificate0353

private theorem bind00859_0 : Agrees (spec (fastBase 0 11 67) layout0054) scope0340 := by decide

theorem reject00859 : Rejected (base 0 11 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 67) _ validLayout0054) (by decide) scope0340 (by rw [← fastBase_exact]; exact bind00859_0) certificate0347

private theorem bind00860_0 : Agrees (spec (fastBase 0 11 68) layout0054) scope0336 := by decide

theorem reject00860 : Rejected (base 0 11 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 68) _ validLayout0054) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind00860_0) certificate0343

private theorem bind00861_0 : Agrees (spec (fastBase 0 11 69) layout0054) scope0330 := by decide

theorem reject00861 : Rejected (base 0 11 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 69) _ validLayout0054) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind00861_0) certificate0337

private theorem bind00862_0 : Agrees (spec (fastBase 0 11 70) layout0054) scope0334 := by decide

theorem reject00862 : Rejected (base 0 11 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 70) _ validLayout0054) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind00862_0) certificate0341

private theorem bind00863_0 : Agrees (spec (fastBase 0 11 71) layout0054) scope0347 := by decide

theorem reject00863 : Rejected (base 0 11 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0054 (layoutValid_of_refines _ _ (base_refines_skeleton 0 11 71) _ validLayout0054) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind00863_0) certificate0354

theorem allCases011 : ∀ y : Fin 72, Rejected (base 0 11 y) := by
  intro y
  fin_cases y

  · exact reject00792

  · exact reject00793

  · exact reject00794

  · exact reject00795

  · exact reject00796

  · exact reject00797

  · exact reject00798

  · exact reject00799

  · exact reject00800

  · exact reject00801

  · exact reject00802

  · exact reject00803

  · exact reject00804

  · exact reject00805

  · exact reject00806

  · exact reject00807

  · exact reject00808

  · exact reject00809

  · exact reject00810

  · exact reject00811

  · exact reject00812

  · exact reject00813

  · exact reject00814

  · exact reject00815

  · exact reject00816

  · exact reject00817

  · exact reject00818

  · exact reject00819

  · exact reject00820

  · exact reject00821

  · exact reject00822

  · exact reject00823

  · exact reject00824

  · exact reject00825

  · exact reject00826

  · exact reject00827

  · exact reject00828

  · exact reject00829

  · exact reject00830

  · exact reject00831

  · exact reject00832

  · exact reject00833

  · exact reject00834

  · exact reject00835

  · exact reject00836

  · exact reject00837

  · exact reject00838

  · exact reject00839

  · exact reject00840

  · exact reject00841

  · exact reject00842

  · exact reject00843

  · exact reject00844

  · exact reject00845

  · exact reject00846

  · exact reject00847

  · exact reject00848

  · exact reject00849

  · exact reject00850

  · exact reject00851

  · exact reject00852

  · exact reject00853

  · exact reject00854

  · exact reject00855

  · exact reject00856

  · exact reject00857

  · exact reject00858

  · exact reject00859

  · exact reject00860

  · exact reject00861

  · exact reject00862

  · exact reject00863

end PricingIntegration.RemainingGWitnesses
