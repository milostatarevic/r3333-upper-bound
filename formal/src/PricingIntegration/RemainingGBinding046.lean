import PricingIntegration.RemainingGLayouts023

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks021

import PricingIntegration.RemainingGScopeChecks022

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03312_0 : Agrees (spec (fastBase 0 46 0) layout0185) scope0335 := by decide

theorem reject03312 : Rejected (base 0 46 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 0) _ validLayout0185) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind03312_0) certificate0342

private theorem bind03313_0 : Agrees (spec (fastBase 0 46 1) layout0185) scope0336 := by decide

theorem reject03313 : Rejected (base 0 46 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 1) _ validLayout0185) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind03313_0) certificate0343

private theorem bind03314_0 : Agrees (spec (fastBase 0 46 2) layout0185) scope0325 := by decide

theorem reject03314 : Rejected (base 0 46 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 2) _ validLayout0185) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind03314_0) certificate0332

private theorem bind03315_0 : Agrees (spec (fastBase 0 46 3) layout0185) scope0330 := by decide

theorem reject03315 : Rejected (base 0 46 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 3) _ validLayout0185) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind03315_0) certificate0337

private theorem bind03316_0 : Agrees (spec (fastBase 0 46 4) layout0186) scope0435 := by decide

private theorem bind03316_1 : Agrees (spec (fastBase 0 46 4) layout0187) scope0328 := by decide

theorem reject03316 : Rejected (base 0 46 4) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 4) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 4) _ validLayout0187) (by decide) (by decide) scope0435 scope0328 (by rw [← fastBase_exact]; exact bind03316_0) (by rw [← fastBase_exact]; exact bind03316_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0462 certificate0463 (by decide)

private theorem bind03317_0 : Agrees (spec (fastBase 0 46 5) layout0186) scope0182 := by decide

private theorem bind03317_1 : Agrees (spec (fastBase 0 46 5) layout0187) scope0333 := by decide

theorem reject03317 : Rejected (base 0 46 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 5) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 5) _ validLayout0187) (by decide) (by decide) scope0182 scope0333 (by rw [← fastBase_exact]; exact bind03317_0) (by rw [← fastBase_exact]; exact bind03317_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0464 (by decide)

private theorem bind03318_0 : Agrees (spec (fastBase 0 46 6) layout0185) scope0326 := by decide

theorem reject03318 : Rejected (base 0 46 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 6) _ validLayout0185) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind03318_0) certificate0333

private theorem bind03319_0 : Agrees (spec (fastBase 0 46 7) layout0185) scope0331 := by decide

theorem reject03319 : Rejected (base 0 46 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 7) _ validLayout0185) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind03319_0) certificate0338

private theorem bind03320_0 : Agrees (spec (fastBase 0 46 8) layout0185) scope0329 := by decide

theorem reject03320 : Rejected (base 0 46 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 8) _ validLayout0185) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind03320_0) certificate0336

private theorem bind03321_0 : Agrees (spec (fastBase 0 46 9) layout0185) scope0334 := by decide

theorem reject03321 : Rejected (base 0 46 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 9) _ validLayout0185) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind03321_0) certificate0341

private theorem bind03322_0 : Agrees (spec (fastBase 0 46 10) layout0185) scope0323 := by decide

theorem reject03322 : Rejected (base 0 46 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 10) _ validLayout0185) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind03322_0) certificate0330

private theorem bind03323_0 : Agrees (spec (fastBase 0 46 11) layout0185) scope0324 := by decide

theorem reject03323 : Rejected (base 0 46 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 11) _ validLayout0185) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind03323_0) certificate0331

private theorem bind03324_0 : Agrees (spec (fastBase 0 46 12) layout0185) scope0346 := by decide

theorem reject03324 : Rejected (base 0 46 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 12) _ validLayout0185) (by decide) scope0346 (by rw [← fastBase_exact]; exact bind03324_0) certificate0353

private theorem bind03325_0 : Agrees (spec (fastBase 0 46 13) layout0185) scope0325 := by decide

theorem reject03325 : Rejected (base 0 46 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 13) _ validLayout0185) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind03325_0) certificate0332

private theorem bind03326_0 : Agrees (spec (fastBase 0 46 14) layout0186) scope0182 := by decide

private theorem bind03326_1 : Agrees (spec (fastBase 0 46 14) layout0187) scope0333 := by decide

theorem reject03326 : Rejected (base 0 46 14) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 14) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 14) _ validLayout0187) (by decide) (by decide) scope0182 scope0333 (by rw [← fastBase_exact]; exact bind03326_0) (by rw [← fastBase_exact]; exact bind03326_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0464 (by decide)

private theorem bind03327_0 : Agrees (spec (fastBase 0 46 15) layout0185) scope0335 := by decide

theorem reject03327 : Rejected (base 0 46 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 15) _ validLayout0185) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind03327_0) certificate0342

private theorem bind03328_0 : Agrees (spec (fastBase 0 46 16) layout0188) scope0436 := by decide

theorem reject03328 : Rejected (base 0 46 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0188 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 16) _ validLayout0188) (by decide) scope0436 (by rw [← fastBase_exact]; exact bind03328_0) certificate0465

private theorem bind03329_0 : Agrees (spec (fastBase 0 46 17) layout0185) scope0347 := by decide

theorem reject03329 : Rejected (base 0 46 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 17) _ validLayout0185) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind03329_0) certificate0354

private theorem bind03330_0 : Agrees (spec (fastBase 0 46 18) layout0185) scope0330 := by decide

theorem reject03330 : Rejected (base 0 46 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 18) _ validLayout0185) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind03330_0) certificate0337

private theorem bind03331_0 : Agrees (spec (fastBase 0 46 19) layout0185) scope0336 := by decide

theorem reject03331 : Rejected (base 0 46 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 19) _ validLayout0185) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind03331_0) certificate0343

private theorem bind03332_0 : Agrees (spec (fastBase 0 46 20) layout0185) scope0340 := by decide

theorem reject03332 : Rejected (base 0 46 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 20) _ validLayout0185) (by decide) scope0340 (by rw [← fastBase_exact]; exact bind03332_0) certificate0347

private theorem bind03333_0 : Agrees (spec (fastBase 0 46 21) layout0185) scope0334 := by decide

theorem reject03333 : Rejected (base 0 46 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 21) _ validLayout0185) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind03333_0) certificate0341

private theorem bind03334_0 : Agrees (spec (fastBase 0 46 22) layout0185) scope0335 := by decide

theorem reject03334 : Rejected (base 0 46 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 22) _ validLayout0185) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind03334_0) certificate0342

private theorem bind03335_0 : Agrees (spec (fastBase 0 46 23) layout0185) scope0325 := by decide

theorem reject03335 : Rejected (base 0 46 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 23) _ validLayout0185) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind03335_0) certificate0332

private theorem bind03336_0 : Agrees (spec (fastBase 0 46 24) layout0185) scope0342 := by decide

theorem reject03336 : Rejected (base 0 46 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 24) _ validLayout0185) (by decide) scope0342 (by rw [← fastBase_exact]; exact bind03336_0) certificate0349

private theorem bind03337_0 : Agrees (spec (fastBase 0 46 25) layout0185) scope0341 := by decide

theorem reject03337 : Rejected (base 0 46 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 25) _ validLayout0185) (by decide) scope0341 (by rw [← fastBase_exact]; exact bind03337_0) certificate0348

private theorem bind03338_0 : Agrees (spec (fastBase 0 46 26) layout0185) scope0323 := by decide

theorem reject03338 : Rejected (base 0 46 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 26) _ validLayout0185) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind03338_0) certificate0330

private theorem bind03339_0 : Agrees (spec (fastBase 0 46 27) layout0185) scope0336 := by decide

theorem reject03339 : Rejected (base 0 46 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 27) _ validLayout0185) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind03339_0) certificate0343

private theorem bind03340_0 : Agrees (spec (fastBase 0 46 28) layout0185) scope0346 := by decide

theorem reject03340 : Rejected (base 0 46 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 28) _ validLayout0185) (by decide) scope0346 (by rw [← fastBase_exact]; exact bind03340_0) certificate0353

private theorem bind03341_0 : Agrees (spec (fastBase 0 46 29) layout0186) scope0178 := by decide

private theorem bind03341_1 : Agrees (spec (fastBase 0 46 29) layout0187) scope0333 := by decide

theorem reject03341 : Rejected (base 0 46 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 29) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 29) _ validLayout0187) (by decide) (by decide) scope0178 scope0333 (by rw [← fastBase_exact]; exact bind03341_0) (by rw [← fastBase_exact]; exact bind03341_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0181 certificate0464 (by decide)

private theorem bind03342_0 : Agrees (spec (fastBase 0 46 30) layout0185) scope0330 := by decide

theorem reject03342 : Rejected (base 0 46 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 30) _ validLayout0185) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind03342_0) certificate0337

private theorem bind03343_0 : Agrees (spec (fastBase 0 46 31) layout0186) scope0178 := by decide

private theorem bind03343_1 : Agrees (spec (fastBase 0 46 31) layout0187) scope0437 := by decide

theorem reject03343 : Rejected (base 0 46 31) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 31) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 31) _ validLayout0187) (by decide) (by decide) scope0178 scope0437 (by rw [← fastBase_exact]; exact bind03343_0) (by rw [← fastBase_exact]; exact bind03343_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0181 certificate0466 (by decide)

private theorem bind03344_0 : Agrees (spec (fastBase 0 46 32) layout0186) scope0435 := by decide

private theorem bind03344_1 : Agrees (spec (fastBase 0 46 32) layout0187) scope0328 := by decide

theorem reject03344 : Rejected (base 0 46 32) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 32) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 32) _ validLayout0187) (by decide) (by decide) scope0435 scope0328 (by rw [← fastBase_exact]; exact bind03344_0) (by rw [← fastBase_exact]; exact bind03344_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0462 certificate0463 (by decide)

private theorem bind03345_0 : Agrees (spec (fastBase 0 46 33) layout0186) scope0177 := by decide

theorem reject03345 : Rejected (base 0 46 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0186 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 33) _ validLayout0186) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03345_0) certificate0180

private theorem bind03346_0 : Agrees (spec (fastBase 0 46 34) layout0186) scope0182 := by decide

private theorem bind03346_1 : Agrees (spec (fastBase 0 46 34) layout0187) scope0328 := by decide

theorem reject03346 : Rejected (base 0 46 34) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 34) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 34) _ validLayout0187) (by decide) (by decide) scope0182 scope0328 (by rw [← fastBase_exact]; exact bind03346_0) (by rw [← fastBase_exact]; exact bind03346_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0463 (by decide)

private theorem bind03347_0 : Agrees (spec (fastBase 0 46 35) layout0186) scope0192 := by decide

theorem reject03347 : Rejected (base 0 46 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0186 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 35) _ validLayout0186) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind03347_0) certificate0195

private theorem bind03348_0 : Agrees (spec (fastBase 0 46 36) layout0186) scope0200 := by decide

theorem reject03348 : Rejected (base 0 46 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0186 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 36) _ validLayout0186) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind03348_0) certificate0203

private theorem bind03349_0 : Agrees (spec (fastBase 0 46 37) layout0185) scope0335 := by decide

theorem reject03349 : Rejected (base 0 46 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 37) _ validLayout0185) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind03349_0) certificate0342

private theorem bind03350_0 : Agrees (spec (fastBase 0 46 38) layout0186) scope0435 := by decide

private theorem bind03350_1 : Agrees (spec (fastBase 0 46 38) layout0187) scope0333 := by decide

theorem reject03350 : Rejected (base 0 46 38) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0186 layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 38) _ validLayout0186) (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 38) _ validLayout0187) (by decide) (by decide) scope0435 scope0333 (by rw [← fastBase_exact]; exact bind03350_0) (by rw [← fastBase_exact]; exact bind03350_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0462 certificate0464 (by decide)

private theorem bind03351_0 : Agrees (spec (fastBase 0 46 39) layout0185) scope0330 := by decide

theorem reject03351 : Rejected (base 0 46 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 39) _ validLayout0185) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind03351_0) certificate0337

private theorem bind03352_0 : Agrees (spec (fastBase 0 46 40) layout0185) scope0347 := by decide

theorem reject03352 : Rejected (base 0 46 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 40) _ validLayout0185) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind03352_0) certificate0354

private theorem bind03353_0 : Agrees (spec (fastBase 0 46 41) layout0185) scope0342 := by decide

theorem reject03353 : Rejected (base 0 46 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 41) _ validLayout0185) (by decide) scope0342 (by rw [← fastBase_exact]; exact bind03353_0) certificate0349

private theorem bind03354_0 : Agrees (spec (fastBase 0 46 42) layout0185) scope0343 := by decide

theorem reject03354 : Rejected (base 0 46 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 42) _ validLayout0185) (by decide) scope0343 (by rw [← fastBase_exact]; exact bind03354_0) certificate0350

private theorem bind03355_0 : Agrees (spec (fastBase 0 46 43) layout0185) scope0337 := by decide

theorem reject03355 : Rejected (base 0 46 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 43) _ validLayout0185) (by decide) scope0337 (by rw [← fastBase_exact]; exact bind03355_0) certificate0344

private theorem bind03356_0 : Agrees (spec (fastBase 0 46 44) layout0185) scope0329 := by decide

theorem reject03356 : Rejected (base 0 46 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 44) _ validLayout0185) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind03356_0) certificate0336

private theorem bind03357_0 : Agrees (spec (fastBase 0 46 45) layout0185) scope0326 := by decide

theorem reject03357 : Rejected (base 0 46 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 45) _ validLayout0185) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind03357_0) certificate0333

private theorem bind03358_0 : Agrees (spec (fastBase 0 46 46) layout0185) scope0324 := by decide

theorem reject03358 : Rejected (base 0 46 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 46) _ validLayout0185) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind03358_0) certificate0331

private theorem bind03359_0 : Agrees (spec (fastBase 0 46 47) layout0185) scope0331 := by decide

theorem reject03359 : Rejected (base 0 46 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 47) _ validLayout0185) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind03359_0) certificate0338

private theorem bind03360_0 : Agrees (spec (fastBase 0 46 48) layout0185) scope0331 := by decide

theorem reject03360 : Rejected (base 0 46 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 48) _ validLayout0185) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind03360_0) certificate0338

private theorem bind03361_0 : Agrees (spec (fastBase 0 46 49) layout0185) scope0331 := by decide

theorem reject03361 : Rejected (base 0 46 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 49) _ validLayout0185) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind03361_0) certificate0338

private theorem bind03362_0 : Agrees (spec (fastBase 0 46 50) layout0185) scope0331 := by decide

theorem reject03362 : Rejected (base 0 46 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 50) _ validLayout0185) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind03362_0) certificate0338

private theorem bind03363_0 : Agrees (spec (fastBase 0 46 51) layout0185) scope0331 := by decide

theorem reject03363 : Rejected (base 0 46 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 51) _ validLayout0185) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind03363_0) certificate0338

private theorem bind03364_0 : Agrees (spec (fastBase 0 46 52) layout0185) scope0341 := by decide

theorem reject03364 : Rejected (base 0 46 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 52) _ validLayout0185) (by decide) scope0341 (by rw [← fastBase_exact]; exact bind03364_0) certificate0348

private theorem bind03365_0 : Agrees (spec (fastBase 0 46 53) layout0185) scope0329 := by decide

theorem reject03365 : Rejected (base 0 46 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 53) _ validLayout0185) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind03365_0) certificate0336

private theorem bind03366_0 : Agrees (spec (fastBase 0 46 54) layout0185) scope0326 := by decide

theorem reject03366 : Rejected (base 0 46 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 54) _ validLayout0185) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind03366_0) certificate0333

private theorem bind03367_0 : Agrees (spec (fastBase 0 46 55) layout0185) scope0339 := by decide

theorem reject03367 : Rejected (base 0 46 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 55) _ validLayout0185) (by decide) scope0339 (by rw [← fastBase_exact]; exact bind03367_0) certificate0346

private theorem bind03368_0 : Agrees (spec (fastBase 0 46 56) layout0185) scope0323 := by decide

theorem reject03368 : Rejected (base 0 46 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 56) _ validLayout0185) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind03368_0) certificate0330

private theorem bind03369_0 : Agrees (spec (fastBase 0 46 57) layout0185) scope0336 := by decide

theorem reject03369 : Rejected (base 0 46 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 57) _ validLayout0185) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind03369_0) certificate0343

private theorem bind03370_0 : Agrees (spec (fastBase 0 46 58) layout0187) scope0348 := by decide

theorem reject03370 : Rejected (base 0 46 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 58) _ validLayout0187) (by decide) scope0348 (by rw [← fastBase_exact]; exact bind03370_0) certificate0355

private theorem bind03371_0 : Agrees (spec (fastBase 0 46 59) layout0185) scope0343 := by decide

theorem reject03371 : Rejected (base 0 46 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 59) _ validLayout0185) (by decide) scope0343 (by rw [← fastBase_exact]; exact bind03371_0) certificate0350

private theorem bind03372_0 : Agrees (spec (fastBase 0 46 60) layout0185) scope0334 := by decide

theorem reject03372 : Rejected (base 0 46 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 60) _ validLayout0185) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind03372_0) certificate0341

private theorem bind03373_0 : Agrees (spec (fastBase 0 46 61) layout0185) scope0324 := by decide

theorem reject03373 : Rejected (base 0 46 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 61) _ validLayout0185) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind03373_0) certificate0331

private theorem bind03374_0 : Agrees (spec (fastBase 0 46 62) layout0185) scope0325 := by decide

theorem reject03374 : Rejected (base 0 46 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 62) _ validLayout0185) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind03374_0) certificate0332

private theorem bind03375_0 : Agrees (spec (fastBase 0 46 63) layout0187) scope0338 := by decide

theorem reject03375 : Rejected (base 0 46 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0187 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 63) _ validLayout0187) (by decide) scope0338 (by rw [← fastBase_exact]; exact bind03375_0) certificate0345

private theorem bind03376_0 : Agrees (spec (fastBase 0 46 64) layout0185) scope0323 := by decide

theorem reject03376 : Rejected (base 0 46 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 64) _ validLayout0185) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind03376_0) certificate0330

private theorem bind03377_0 : Agrees (spec (fastBase 0 46 65) layout0185) scope0329 := by decide

theorem reject03377 : Rejected (base 0 46 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 65) _ validLayout0185) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind03377_0) certificate0336

private theorem bind03378_0 : Agrees (spec (fastBase 0 46 66) layout0185) scope0337 := by decide

theorem reject03378 : Rejected (base 0 46 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 66) _ validLayout0185) (by decide) scope0337 (by rw [← fastBase_exact]; exact bind03378_0) certificate0344

private theorem bind03379_0 : Agrees (spec (fastBase 0 46 67) layout0185) scope0340 := by decide

theorem reject03379 : Rejected (base 0 46 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 67) _ validLayout0185) (by decide) scope0340 (by rw [← fastBase_exact]; exact bind03379_0) certificate0347

private theorem bind03380_0 : Agrees (spec (fastBase 0 46 68) layout0185) scope0324 := by decide

theorem reject03380 : Rejected (base 0 46 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 68) _ validLayout0185) (by decide) scope0324 (by rw [← fastBase_exact]; exact bind03380_0) certificate0331

private theorem bind03381_0 : Agrees (spec (fastBase 0 46 69) layout0185) scope0326 := by decide

theorem reject03381 : Rejected (base 0 46 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 69) _ validLayout0185) (by decide) scope0326 (by rw [← fastBase_exact]; exact bind03381_0) certificate0333

private theorem bind03382_0 : Agrees (spec (fastBase 0 46 70) layout0185) scope0334 := by decide

theorem reject03382 : Rejected (base 0 46 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 70) _ validLayout0185) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind03382_0) certificate0341

private theorem bind03383_0 : Agrees (spec (fastBase 0 46 71) layout0185) scope0339 := by decide

theorem reject03383 : Rejected (base 0 46 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0185 (layoutValid_of_refines _ _ (base_refines_skeleton 0 46 71) _ validLayout0185) (by decide) scope0339 (by rw [← fastBase_exact]; exact bind03383_0) certificate0346

theorem allCases046 : ∀ y : Fin 72, Rejected (base 0 46 y) := by
  intro y
  fin_cases y

  · exact reject03312

  · exact reject03313

  · exact reject03314

  · exact reject03315

  · exact reject03316

  · exact reject03317

  · exact reject03318

  · exact reject03319

  · exact reject03320

  · exact reject03321

  · exact reject03322

  · exact reject03323

  · exact reject03324

  · exact reject03325

  · exact reject03326

  · exact reject03327

  · exact reject03328

  · exact reject03329

  · exact reject03330

  · exact reject03331

  · exact reject03332

  · exact reject03333

  · exact reject03334

  · exact reject03335

  · exact reject03336

  · exact reject03337

  · exact reject03338

  · exact reject03339

  · exact reject03340

  · exact reject03341

  · exact reject03342

  · exact reject03343

  · exact reject03344

  · exact reject03345

  · exact reject03346

  · exact reject03347

  · exact reject03348

  · exact reject03349

  · exact reject03350

  · exact reject03351

  · exact reject03352

  · exact reject03353

  · exact reject03354

  · exact reject03355

  · exact reject03356

  · exact reject03357

  · exact reject03358

  · exact reject03359

  · exact reject03360

  · exact reject03361

  · exact reject03362

  · exact reject03363

  · exact reject03364

  · exact reject03365

  · exact reject03366

  · exact reject03367

  · exact reject03368

  · exact reject03369

  · exact reject03370

  · exact reject03371

  · exact reject03372

  · exact reject03373

  · exact reject03374

  · exact reject03375

  · exact reject03376

  · exact reject03377

  · exact reject03378

  · exact reject03379

  · exact reject03380

  · exact reject03381

  · exact reject03382

  · exact reject03383

end PricingIntegration.RemainingGWitnesses
