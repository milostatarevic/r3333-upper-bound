import PricingIntegration.RemainingGLayouts002

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks007

import PricingIntegration.RemainingGScopeChecks008


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00288_0 : Agrees (spec (fastBase 0 4 0) layout0019) scope0108 := by decide

theorem reject00288 : Rejected (base 0 4 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 0) _ validLayout0019) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind00288_0) certificate0111

private theorem bind00289_0 : Agrees (spec (fastBase 0 4 1) layout0019) scope0109 := by decide

theorem reject00289 : Rejected (base 0 4 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 1) _ validLayout0019) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind00289_0) certificate0112

private theorem bind00290_0 : Agrees (spec (fastBase 0 4 2) layout0019) scope0110 := by decide

theorem reject00290 : Rejected (base 0 4 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 2) _ validLayout0019) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind00290_0) certificate0113

private theorem bind00291_0 : Agrees (spec (fastBase 0 4 3) layout0019) scope0111 := by decide

theorem reject00291 : Rejected (base 0 4 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 3) _ validLayout0019) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind00291_0) certificate0114

private theorem bind00292_0 : Agrees (spec (fastBase 0 4 4) layout0019) scope0112 := by decide

theorem reject00292 : Rejected (base 0 4 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 4) _ validLayout0019) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind00292_0) certificate0115

private theorem bind00293_0 : Agrees (spec (fastBase 0 4 5) layout0019) scope0113 := by decide

theorem reject00293 : Rejected (base 0 4 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 5) _ validLayout0019) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind00293_0) certificate0116

private theorem bind00294_0 : Agrees (spec (fastBase 0 4 6) layout0020) scope0114 := by decide

private theorem bind00294_1 : Agrees (spec (fastBase 0 4 6) layout0021) scope0115 := by decide

theorem reject00294 : Rejected (base 0 4 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 6) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 6) _ validLayout0021) (by decide) (by decide) scope0114 scope0115 (by rw [← fastBase_exact]; exact bind00294_0) (by rw [← fastBase_exact]; exact bind00294_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0118 (by decide)

private theorem bind00295_0 : Agrees (spec (fastBase 0 4 7) layout0020) scope0116 := by decide

private theorem bind00295_1 : Agrees (spec (fastBase 0 4 7) layout0021) scope0117 := by decide

theorem reject00295 : Rejected (base 0 4 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 7) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 7) _ validLayout0021) (by decide) (by decide) scope0116 scope0117 (by rw [← fastBase_exact]; exact bind00295_0) (by rw [← fastBase_exact]; exact bind00295_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0120 (by decide)

private theorem bind00296_0 : Agrees (spec (fastBase 0 4 8) layout0019) scope0118 := by decide

theorem reject00296 : Rejected (base 0 4 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 8) _ validLayout0019) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind00296_0) certificate0121

private theorem bind00297_0 : Agrees (spec (fastBase 0 4 9) layout0019) scope0119 := by decide

theorem reject00297 : Rejected (base 0 4 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 9) _ validLayout0019) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind00297_0) certificate0122

private theorem bind00298_0 : Agrees (spec (fastBase 0 4 10) layout0019) scope0120 := by decide

theorem reject00298 : Rejected (base 0 4 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 10) _ validLayout0019) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind00298_0) certificate0123

private theorem bind00299_0 : Agrees (spec (fastBase 0 4 11) layout0019) scope0121 := by decide

theorem reject00299 : Rejected (base 0 4 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 11) _ validLayout0019) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind00299_0) certificate0124

private theorem bind00300_0 : Agrees (spec (fastBase 0 4 12) layout0019) scope0122 := by decide

theorem reject00300 : Rejected (base 0 4 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 12) _ validLayout0019) (by decide) scope0122 (by rw [← fastBase_exact]; exact bind00300_0) certificate0125

private theorem bind00301_0 : Agrees (spec (fastBase 0 4 13) layout0019) scope0110 := by decide

theorem reject00301 : Rejected (base 0 4 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 13) _ validLayout0019) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind00301_0) certificate0113

private theorem bind00302_0 : Agrees (spec (fastBase 0 4 14) layout0019) scope0108 := by decide

theorem reject00302 : Rejected (base 0 4 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 14) _ validLayout0019) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind00302_0) certificate0111

private theorem bind00303_0 : Agrees (spec (fastBase 0 4 15) layout0020) scope0123 := by decide

private theorem bind00303_1 : Agrees (spec (fastBase 0 4 15) layout0022) scope0124 := by decide

theorem reject00303 : Rejected (base 0 4 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 15) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 15) _ validLayout0022) (by decide) (by decide) scope0123 scope0124 (by rw [← fastBase_exact]; exact bind00303_0) (by rw [← fastBase_exact]; exact bind00303_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0126 certificate0127 (by decide)

private theorem bind00304_0 : Agrees (spec (fastBase 0 4 16) layout0019) scope0118 := by decide

theorem reject00304 : Rejected (base 0 4 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 16) _ validLayout0019) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind00304_0) certificate0121

private theorem bind00305_0 : Agrees (spec (fastBase 0 4 17) layout0019) scope0125 := by decide

theorem reject00305 : Rejected (base 0 4 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 17) _ validLayout0019) (by decide) scope0125 (by rw [← fastBase_exact]; exact bind00305_0) certificate0128

private theorem bind00306_0 : Agrees (spec (fastBase 0 4 18) layout0019) scope0111 := by decide

theorem reject00306 : Rejected (base 0 4 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 18) _ validLayout0019) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind00306_0) certificate0114

private theorem bind00307_0 : Agrees (spec (fastBase 0 4 19) layout0019) scope0112 := by decide

theorem reject00307 : Rejected (base 0 4 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 19) _ validLayout0019) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind00307_0) certificate0115

private theorem bind00308_0 : Agrees (spec (fastBase 0 4 20) layout0019) scope0109 := by decide

theorem reject00308 : Rejected (base 0 4 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 20) _ validLayout0019) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind00308_0) certificate0112

private theorem bind00309_0 : Agrees (spec (fastBase 0 4 21) layout0019) scope0126 := by decide

theorem reject00309 : Rejected (base 0 4 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 21) _ validLayout0019) (by decide) scope0126 (by rw [← fastBase_exact]; exact bind00309_0) certificate0129

private theorem bind00310_0 : Agrees (spec (fastBase 0 4 22) layout0019) scope0108 := by decide

theorem reject00310 : Rejected (base 0 4 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 22) _ validLayout0019) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind00310_0) certificate0111

private theorem bind00311_0 : Agrees (spec (fastBase 0 4 23) layout0019) scope0112 := by decide

theorem reject00311 : Rejected (base 0 4 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 23) _ validLayout0019) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind00311_0) certificate0115

private theorem bind00312_0 : Agrees (spec (fastBase 0 4 24) layout0019) scope0125 := by decide

theorem reject00312 : Rejected (base 0 4 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 24) _ validLayout0019) (by decide) scope0125 (by rw [← fastBase_exact]; exact bind00312_0) certificate0128

private theorem bind00313_0 : Agrees (spec (fastBase 0 4 25) layout0019) scope0110 := by decide

theorem reject00313 : Rejected (base 0 4 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 25) _ validLayout0019) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind00313_0) certificate0113

private theorem bind00314_0 : Agrees (spec (fastBase 0 4 26) layout0019) scope0127 := by decide

theorem reject00314 : Rejected (base 0 4 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 26) _ validLayout0019) (by decide) scope0127 (by rw [← fastBase_exact]; exact bind00314_0) certificate0130

private theorem bind00315_0 : Agrees (spec (fastBase 0 4 27) layout0019) scope0109 := by decide

theorem reject00315 : Rejected (base 0 4 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 27) _ validLayout0019) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind00315_0) certificate0112

private theorem bind00316_0 : Agrees (spec (fastBase 0 4 28) layout0019) scope0128 := by decide

theorem reject00316 : Rejected (base 0 4 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 28) _ validLayout0019) (by decide) scope0128 (by rw [← fastBase_exact]; exact bind00316_0) certificate0131

private theorem bind00317_0 : Agrees (spec (fastBase 0 4 29) layout0019) scope0111 := by decide

theorem reject00317 : Rejected (base 0 4 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 29) _ validLayout0019) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind00317_0) certificate0114

private theorem bind00318_0 : Agrees (spec (fastBase 0 4 30) layout0020) scope0129 := by decide

private theorem bind00318_1 : Agrees (spec (fastBase 0 4 30) layout0022) scope0130 := by decide

theorem reject00318 : Rejected (base 0 4 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 30) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 30) _ validLayout0022) (by decide) (by decide) scope0129 scope0130 (by rw [← fastBase_exact]; exact bind00318_0) (by rw [← fastBase_exact]; exact bind00318_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0132 certificate0133 (by decide)

private theorem bind00319_0 : Agrees (spec (fastBase 0 4 31) layout0019) scope0121 := by decide

theorem reject00319 : Rejected (base 0 4 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 31) _ validLayout0019) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind00319_0) certificate0124

private theorem bind00320_0 : Agrees (spec (fastBase 0 4 32) layout0019) scope0109 := by decide

theorem reject00320 : Rejected (base 0 4 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 32) _ validLayout0019) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind00320_0) certificate0112

private theorem bind00321_0 : Agrees (spec (fastBase 0 4 33) layout0019) scope0110 := by decide

theorem reject00321 : Rejected (base 0 4 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 33) _ validLayout0019) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind00321_0) certificate0113

private theorem bind00322_0 : Agrees (spec (fastBase 0 4 34) layout0019) scope0112 := by decide

theorem reject00322 : Rejected (base 0 4 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 34) _ validLayout0019) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind00322_0) certificate0115

private theorem bind00323_0 : Agrees (spec (fastBase 0 4 35) layout0019) scope0122 := by decide

theorem reject00323 : Rejected (base 0 4 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 35) _ validLayout0019) (by decide) scope0122 (by rw [← fastBase_exact]; exact bind00323_0) certificate0125

private theorem bind00324_0 : Agrees (spec (fastBase 0 4 36) layout0019) scope0128 := by decide

theorem reject00324 : Rejected (base 0 4 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 36) _ validLayout0019) (by decide) scope0128 (by rw [← fastBase_exact]; exact bind00324_0) certificate0131

private theorem bind00325_0 : Agrees (spec (fastBase 0 4 37) layout0019) scope0113 := by decide

theorem reject00325 : Rejected (base 0 4 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 37) _ validLayout0019) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind00325_0) certificate0116

private theorem bind00326_0 : Agrees (spec (fastBase 0 4 38) layout0019) scope0113 := by decide

theorem reject00326 : Rejected (base 0 4 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 38) _ validLayout0019) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind00326_0) certificate0116

private theorem bind00327_0 : Agrees (spec (fastBase 0 4 39) layout0019) scope0113 := by decide

theorem reject00327 : Rejected (base 0 4 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 39) _ validLayout0019) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind00327_0) certificate0116

private theorem bind00328_0 : Agrees (spec (fastBase 0 4 40) layout0019) scope0113 := by decide

theorem reject00328 : Rejected (base 0 4 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 40) _ validLayout0019) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind00328_0) certificate0116

private theorem bind00329_0 : Agrees (spec (fastBase 0 4 41) layout0019) scope0113 := by decide

theorem reject00329 : Rejected (base 0 4 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 41) _ validLayout0019) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind00329_0) certificate0116

private theorem bind00330_0 : Agrees (spec (fastBase 0 4 42) layout0021) scope0131 := by decide

theorem reject00330 : Rejected (base 0 4 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 42) _ validLayout0021) (by decide) scope0131 (by rw [← fastBase_exact]; exact bind00330_0) certificate0134

private theorem bind00331_0 : Agrees (spec (fastBase 0 4 43) layout0021) scope0132 := by decide

theorem reject00331 : Rejected (base 0 4 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 43) _ validLayout0021) (by decide) scope0132 (by rw [← fastBase_exact]; exact bind00331_0) certificate0135

private theorem bind00332_0 : Agrees (spec (fastBase 0 4 44) layout0022) scope0133 := by decide

theorem reject00332 : Rejected (base 0 4 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 44) _ validLayout0022) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind00332_0) certificate0136

private theorem bind00333_0 : Agrees (spec (fastBase 0 4 45) layout0020) scope0116 := by decide

private theorem bind00333_1 : Agrees (spec (fastBase 0 4 45) layout0021) scope0115 := by decide

theorem reject00333 : Rejected (base 0 4 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 45) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 45) _ validLayout0021) (by decide) (by decide) scope0116 scope0115 (by rw [← fastBase_exact]; exact bind00333_0) (by rw [← fastBase_exact]; exact bind00333_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0118 (by decide)

private theorem bind00334_0 : Agrees (spec (fastBase 0 4 46) layout0020) scope0121 := by decide

theorem reject00334 : Rejected (base 0 4 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 46) _ validLayout0020) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind00334_0) certificate0124

private theorem bind00335_0 : Agrees (spec (fastBase 0 4 47) layout0019) scope0134 := by decide

theorem reject00335 : Rejected (base 0 4 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 47) _ validLayout0019) (by decide) scope0134 (by rw [← fastBase_exact]; exact bind00335_0) certificate0137

private theorem bind00336_0 : Agrees (spec (fastBase 0 4 48) layout0019) scope0135 := by decide

theorem reject00336 : Rejected (base 0 4 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 48) _ validLayout0019) (by decide) scope0135 (by rw [← fastBase_exact]; exact bind00336_0) certificate0138

private theorem bind00337_0 : Agrees (spec (fastBase 0 4 49) layout0020) scope0114 := by decide

private theorem bind00337_1 : Agrees (spec (fastBase 0 4 49) layout0021) scope0117 := by decide

theorem reject00337 : Rejected (base 0 4 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 49) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 49) _ validLayout0021) (by decide) (by decide) scope0114 scope0117 (by rw [← fastBase_exact]; exact bind00337_0) (by rw [← fastBase_exact]; exact bind00337_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0120 (by decide)

private theorem bind00338_0 : Agrees (spec (fastBase 0 4 50) layout0019) scope0119 := by decide

theorem reject00338 : Rejected (base 0 4 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 50) _ validLayout0019) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind00338_0) certificate0122

private theorem bind00339_0 : Agrees (spec (fastBase 0 4 51) layout0019) scope0120 := by decide

theorem reject00339 : Rejected (base 0 4 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 51) _ validLayout0019) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind00339_0) certificate0123

private theorem bind00340_0 : Agrees (spec (fastBase 0 4 52) layout0019) scope0108 := by decide

theorem reject00340 : Rejected (base 0 4 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 52) _ validLayout0019) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind00340_0) certificate0111

private theorem bind00341_0 : Agrees (spec (fastBase 0 4 53) layout0019) scope0127 := by decide

theorem reject00341 : Rejected (base 0 4 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 53) _ validLayout0019) (by decide) scope0127 (by rw [← fastBase_exact]; exact bind00341_0) certificate0130

private theorem bind00342_0 : Agrees (spec (fastBase 0 4 54) layout0019) scope0118 := by decide

theorem reject00342 : Rejected (base 0 4 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 54) _ validLayout0019) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind00342_0) certificate0121

private theorem bind00343_0 : Agrees (spec (fastBase 0 4 55) layout0019) scope0134 := by decide

theorem reject00343 : Rejected (base 0 4 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 55) _ validLayout0019) (by decide) scope0134 (by rw [← fastBase_exact]; exact bind00343_0) certificate0137

private theorem bind00344_0 : Agrees (spec (fastBase 0 4 56) layout0019) scope0120 := by decide

theorem reject00344 : Rejected (base 0 4 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 56) _ validLayout0019) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind00344_0) certificate0123

private theorem bind00345_0 : Agrees (spec (fastBase 0 4 57) layout0020) scope0126 := by decide

theorem reject00345 : Rejected (base 0 4 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 57) _ validLayout0020) (by decide) scope0126 (by rw [← fastBase_exact]; exact bind00345_0) certificate0129

private theorem bind00346_0 : Agrees (spec (fastBase 0 4 58) layout0019) scope0119 := by decide

theorem reject00346 : Rejected (base 0 4 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 58) _ validLayout0019) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind00346_0) certificate0122

private theorem bind00347_0 : Agrees (spec (fastBase 0 4 59) layout0019) scope0136 := by decide

theorem reject00347 : Rejected (base 0 4 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 59) _ validLayout0019) (by decide) scope0136 (by rw [← fastBase_exact]; exact bind00347_0) certificate0139

private theorem bind00348_0 : Agrees (spec (fastBase 0 4 60) layout0022) scope0137 := by decide

theorem reject00348 : Rejected (base 0 4 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 60) _ validLayout0022) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind00348_0) certificate0140

private theorem bind00349_0 : Agrees (spec (fastBase 0 4 61) layout0019) scope0121 := by decide

theorem reject00349 : Rejected (base 0 4 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 61) _ validLayout0019) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind00349_0) certificate0124

private theorem bind00350_0 : Agrees (spec (fastBase 0 4 62) layout0020) scope0127 := by decide

theorem reject00350 : Rejected (base 0 4 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 62) _ validLayout0020) (by decide) scope0127 (by rw [← fastBase_exact]; exact bind00350_0) certificate0130

private theorem bind00351_0 : Agrees (spec (fastBase 0 4 63) layout0019) scope0120 := by decide

theorem reject00351 : Rejected (base 0 4 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 63) _ validLayout0019) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind00351_0) certificate0123

private theorem bind00352_0 : Agrees (spec (fastBase 0 4 64) layout0020) scope0120 := by decide

theorem reject00352 : Rejected (base 0 4 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 64) _ validLayout0020) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind00352_0) certificate0123

private theorem bind00353_0 : Agrees (spec (fastBase 0 4 65) layout0019) scope0118 := by decide

theorem reject00353 : Rejected (base 0 4 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 65) _ validLayout0019) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind00353_0) certificate0121

private theorem bind00354_0 : Agrees (spec (fastBase 0 4 66) layout0019) scope0136 := by decide

theorem reject00354 : Rejected (base 0 4 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 66) _ validLayout0019) (by decide) scope0136 (by rw [← fastBase_exact]; exact bind00354_0) certificate0139

private theorem bind00355_0 : Agrees (spec (fastBase 0 4 67) layout0019) scope0111 := by decide

theorem reject00355 : Rejected (base 0 4 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 67) _ validLayout0019) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind00355_0) certificate0114

private theorem bind00356_0 : Agrees (spec (fastBase 0 4 68) layout0019) scope0126 := by decide

theorem reject00356 : Rejected (base 0 4 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 68) _ validLayout0019) (by decide) scope0126 (by rw [← fastBase_exact]; exact bind00356_0) certificate0129

private theorem bind00357_0 : Agrees (spec (fastBase 0 4 69) layout0019) scope0121 := by decide

theorem reject00357 : Rejected (base 0 4 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 69) _ validLayout0019) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind00357_0) certificate0124

private theorem bind00358_0 : Agrees (spec (fastBase 0 4 70) layout0019) scope0119 := by decide

theorem reject00358 : Rejected (base 0 4 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 70) _ validLayout0019) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind00358_0) certificate0122

private theorem bind00359_0 : Agrees (spec (fastBase 0 4 71) layout0019) scope0135 := by decide

theorem reject00359 : Rejected (base 0 4 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 0 4 71) _ validLayout0019) (by decide) scope0135 (by rw [← fastBase_exact]; exact bind00359_0) certificate0138

theorem allCases004 : ∀ y : Fin 72, Rejected (base 0 4 y) := by
  intro y
  fin_cases y

  · exact reject00288

  · exact reject00289

  · exact reject00290

  · exact reject00291

  · exact reject00292

  · exact reject00293

  · exact reject00294

  · exact reject00295

  · exact reject00296

  · exact reject00297

  · exact reject00298

  · exact reject00299

  · exact reject00300

  · exact reject00301

  · exact reject00302

  · exact reject00303

  · exact reject00304

  · exact reject00305

  · exact reject00306

  · exact reject00307

  · exact reject00308

  · exact reject00309

  · exact reject00310

  · exact reject00311

  · exact reject00312

  · exact reject00313

  · exact reject00314

  · exact reject00315

  · exact reject00316

  · exact reject00317

  · exact reject00318

  · exact reject00319

  · exact reject00320

  · exact reject00321

  · exact reject00322

  · exact reject00323

  · exact reject00324

  · exact reject00325

  · exact reject00326

  · exact reject00327

  · exact reject00328

  · exact reject00329

  · exact reject00330

  · exact reject00331

  · exact reject00332

  · exact reject00333

  · exact reject00334

  · exact reject00335

  · exact reject00336

  · exact reject00337

  · exact reject00338

  · exact reject00339

  · exact reject00340

  · exact reject00341

  · exact reject00342

  · exact reject00343

  · exact reject00344

  · exact reject00345

  · exact reject00346

  · exact reject00347

  · exact reject00348

  · exact reject00349

  · exact reject00350

  · exact reject00351

  · exact reject00352

  · exact reject00353

  · exact reject00354

  · exact reject00355

  · exact reject00356

  · exact reject00357

  · exact reject00358

  · exact reject00359

end PricingIntegration.RemainingGWitnesses
