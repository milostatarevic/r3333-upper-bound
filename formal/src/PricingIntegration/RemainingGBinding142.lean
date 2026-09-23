import PricingIntegration.RemainingGLayouts033

import PricingIntegration.RemainingGLayouts036

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks021

import PricingIntegration.RemainingGScopeChecks022

import PricingIntegration.RemainingGScopeChecks032

import PricingIntegration.RemainingGScopeChecks033

import PricingIntegration.RemainingGScopeChecks037

import PricingIntegration.RemainingGScopeChecks038


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind10224_0 : Agrees (spec (fastBase 1 70 0) layout0266) scope0329 := by decide

theorem reject10224 : Rejected (base 1 70 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 0) _ validLayout0266) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind10224_0) certificate0336

private theorem bind10225_0 : Agrees (spec (fastBase 1 70 1) layout0265) scope0478 := by decide

theorem reject10225 : Rejected (base 1 70 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 1) _ validLayout0265) (by decide) scope0478 (by rw [← fastBase_exact]; exact bind10225_0) certificate0517

private theorem bind10226_0 : Agrees (spec (fastBase 1 70 2) layout0266) scope0327 := by decide

private theorem bind10226_1 : Agrees (spec (fastBase 1 70 2) layout0288) scope0328 := by decide

theorem reject10226 : Rejected (base 1 70 2) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0266 layout0288 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 2) _ validLayout0266) (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 2) _ validLayout0288) (by decide) (by decide) scope0327 scope0328 (by rw [← fastBase_exact]; exact bind10226_0) (by rw [← fastBase_exact]; exact bind10226_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0335 (by decide)

private theorem bind10227_0 : Agrees (spec (fastBase 1 70 3) layout0265) scope0482 := by decide

theorem reject10227 : Rejected (base 1 70 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 3) _ validLayout0265) (by decide) scope0482 (by rw [← fastBase_exact]; exact bind10227_0) certificate0524

private theorem bind10228_0 : Agrees (spec (fastBase 1 70 4) layout0265) scope0563 := by decide

theorem reject10228 : Rejected (base 1 70 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 4) _ validLayout0265) (by decide) scope0563 (by rw [← fastBase_exact]; exact bind10228_0) certificate0606

private theorem bind10229_0 : Agrees (spec (fastBase 1 70 5) layout0265) scope0565 := by decide

theorem reject10229 : Rejected (base 1 70 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 5) _ validLayout0265) (by decide) scope0565 (by rw [← fastBase_exact]; exact bind10229_0) certificate0608

private theorem bind10230_0 : Agrees (spec (fastBase 1 70 6) layout0265) scope0344 := by decide

theorem reject10230 : Rejected (base 1 70 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 6) _ validLayout0265) (by decide) scope0344 (by rw [← fastBase_exact]; exact bind10230_0) certificate0351

private theorem bind10231_0 : Agrees (spec (fastBase 1 70 7) layout0265) scope0479 := by decide

theorem reject10231 : Rejected (base 1 70 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 7) _ validLayout0265) (by decide) scope0479 (by rw [← fastBase_exact]; exact bind10231_0) certificate0518

private theorem bind10232_0 : Agrees (spec (fastBase 1 70 8) layout0265) scope0562 := by decide

theorem reject10232 : Rejected (base 1 70 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 8) _ validLayout0265) (by decide) scope0562 (by rw [← fastBase_exact]; exact bind10232_0) certificate0605

private theorem bind10233_0 : Agrees (spec (fastBase 1 70 9) layout0265) scope0485 := by decide

theorem reject10233 : Rejected (base 1 70 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 9) _ validLayout0265) (by decide) scope0485 (by rw [← fastBase_exact]; exact bind10233_0) certificate0527

private theorem bind10234_0 : Agrees (spec (fastBase 1 70 10) layout0265) scope0345 := by decide

theorem reject10234 : Rejected (base 1 70 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 10) _ validLayout0265) (by decide) scope0345 (by rw [← fastBase_exact]; exact bind10234_0) certificate0352

private theorem bind10235_0 : Agrees (spec (fastBase 1 70 11) layout0265) scope0564 := by decide

theorem reject10235 : Rejected (base 1 70 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 11) _ validLayout0265) (by decide) scope0564 (by rw [← fastBase_exact]; exact bind10235_0) certificate0607

private theorem bind10236_0 : Agrees (spec (fastBase 1 70 12) layout0265) scope0478 := by decide

theorem reject10236 : Rejected (base 1 70 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 12) _ validLayout0265) (by decide) scope0478 (by rw [← fastBase_exact]; exact bind10236_0) certificate0517

private theorem bind10237_0 : Agrees (spec (fastBase 1 70 13) layout0266) scope0329 := by decide

theorem reject10237 : Rejected (base 1 70 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 13) _ validLayout0266) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind10237_0) certificate0336

private theorem bind10238_0 : Agrees (spec (fastBase 1 70 14) layout0265) scope0565 := by decide

theorem reject10238 : Rejected (base 1 70 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 14) _ validLayout0265) (by decide) scope0565 (by rw [← fastBase_exact]; exact bind10238_0) certificate0608

private theorem bind10239_0 : Agrees (spec (fastBase 1 70 15) layout0265) scope0348 := by decide

theorem reject10239 : Rejected (base 1 70 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 15) _ validLayout0265) (by decide) scope0348 (by rw [← fastBase_exact]; exact bind10239_0) certificate0355

private theorem bind10240_0 : Agrees (spec (fastBase 1 70 16) layout0265) scope0338 := by decide

theorem reject10240 : Rejected (base 1 70 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 16) _ validLayout0265) (by decide) scope0338 (by rw [← fastBase_exact]; exact bind10240_0) certificate0345

private theorem bind10241_0 : Agrees (spec (fastBase 1 70 17) layout0266) scope0329 := by decide

theorem reject10241 : Rejected (base 1 70 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 17) _ validLayout0266) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind10241_0) certificate0336

private theorem bind10242_0 : Agrees (spec (fastBase 1 70 18) layout0265) scope0482 := by decide

theorem reject10242 : Rejected (base 1 70 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 18) _ validLayout0265) (by decide) scope0482 (by rw [← fastBase_exact]; exact bind10242_0) certificate0524

private theorem bind10243_0 : Agrees (spec (fastBase 1 70 19) layout0265) scope0486 := by decide

theorem reject10243 : Rejected (base 1 70 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 19) _ validLayout0265) (by decide) scope0486 (by rw [← fastBase_exact]; exact bind10243_0) certificate0528

private theorem bind10244_0 : Agrees (spec (fastBase 1 70 20) layout0266) scope0343 := by decide

theorem reject10244 : Rejected (base 1 70 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 20) _ validLayout0266) (by decide) scope0343 (by rw [← fastBase_exact]; exact bind10244_0) certificate0350

private theorem bind10245_0 : Agrees (spec (fastBase 1 70 21) layout0265) scope0478 := by decide

theorem reject10245 : Rejected (base 1 70 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 21) _ validLayout0265) (by decide) scope0478 (by rw [← fastBase_exact]; exact bind10245_0) certificate0517

private theorem bind10246_0 : Agrees (spec (fastBase 1 70 22) layout0288) scope0345 := by decide

theorem reject10246 : Rejected (base 1 70 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0288 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 22) _ validLayout0288) (by decide) scope0345 (by rw [← fastBase_exact]; exact bind10246_0) certificate0352

private theorem bind10247_0 : Agrees (spec (fastBase 1 70 23) layout0266) scope0327 := by decide

private theorem bind10247_1 : Agrees (spec (fastBase 1 70 23) layout0288) scope0328 := by decide

theorem reject10247 : Rejected (base 1 70 23) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0266 layout0288 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 23) _ validLayout0266) (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 23) _ validLayout0288) (by decide) (by decide) scope0327 scope0328 (by rw [← fastBase_exact]; exact bind10247_0) (by rw [← fastBase_exact]; exact bind10247_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0335 (by decide)

private theorem bind10248_0 : Agrees (spec (fastBase 1 70 24) layout0288) scope0344 := by decide

theorem reject10248 : Rejected (base 1 70 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0288 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 24) _ validLayout0288) (by decide) scope0344 (by rw [← fastBase_exact]; exact bind10248_0) certificate0351

private theorem bind10249_0 : Agrees (spec (fastBase 1 70 25) layout0266) scope0336 := by decide

theorem reject10249 : Rejected (base 1 70 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 25) _ validLayout0266) (by decide) scope0336 (by rw [← fastBase_exact]; exact bind10249_0) certificate0343

private theorem bind10250_0 : Agrees (spec (fastBase 1 70 26) layout0266) scope0332 := by decide

private theorem bind10250_1 : Agrees (spec (fastBase 1 70 26) layout0288) scope0328 := by decide

theorem reject10250 : Rejected (base 1 70 26) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0266 layout0288 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 26) _ validLayout0266) (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 26) _ validLayout0288) (by decide) (by decide) scope0332 scope0328 (by rw [← fastBase_exact]; exact bind10250_0) (by rw [← fastBase_exact]; exact bind10250_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0335 (by decide)

private theorem bind10251_0 : Agrees (spec (fastBase 1 70 27) layout0265) scope0478 := by decide

theorem reject10251 : Rejected (base 1 70 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 27) _ validLayout0265) (by decide) scope0478 (by rw [← fastBase_exact]; exact bind10251_0) certificate0517

private theorem bind10252_0 : Agrees (spec (fastBase 1 70 28) layout0265) scope0482 := by decide

theorem reject10252 : Rejected (base 1 70 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 28) _ validLayout0265) (by decide) scope0482 (by rw [← fastBase_exact]; exact bind10252_0) certificate0524

private theorem bind10253_0 : Agrees (spec (fastBase 1 70 29) layout0265) scope0348 := by decide

theorem reject10253 : Rejected (base 1 70 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 29) _ validLayout0265) (by decide) scope0348 (by rw [← fastBase_exact]; exact bind10253_0) certificate0355

private theorem bind10254_0 : Agrees (spec (fastBase 1 70 30) layout0265) scope0479 := by decide

theorem reject10254 : Rejected (base 1 70 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 30) _ validLayout0265) (by decide) scope0479 (by rw [← fastBase_exact]; exact bind10254_0) certificate0518

private theorem bind10255_0 : Agrees (spec (fastBase 1 70 31) layout0265) scope0484 := by decide

theorem reject10255 : Rejected (base 1 70 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 31) _ validLayout0265) (by decide) scope0484 (by rw [← fastBase_exact]; exact bind10255_0) certificate0526

private theorem bind10256_0 : Agrees (spec (fastBase 1 70 32) layout0265) scope0338 := by decide

theorem reject10256 : Rejected (base 1 70 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 32) _ validLayout0265) (by decide) scope0338 (by rw [← fastBase_exact]; exact bind10256_0) certificate0345

private theorem bind10257_0 : Agrees (spec (fastBase 1 70 33) layout0265) scope0563 := by decide

theorem reject10257 : Rejected (base 1 70 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 33) _ validLayout0265) (by decide) scope0563 (by rw [← fastBase_exact]; exact bind10257_0) certificate0606

private theorem bind10258_0 : Agrees (spec (fastBase 1 70 34) layout0265) scope0565 := by decide

theorem reject10258 : Rejected (base 1 70 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 34) _ validLayout0265) (by decide) scope0565 (by rw [← fastBase_exact]; exact bind10258_0) certificate0608

private theorem bind10259_0 : Agrees (spec (fastBase 1 70 35) layout0265) scope0562 := by decide

theorem reject10259 : Rejected (base 1 70 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 35) _ validLayout0265) (by decide) scope0562 (by rw [← fastBase_exact]; exact bind10259_0) certificate0605

private theorem bind10260_0 : Agrees (spec (fastBase 1 70 36) layout0265) scope0483 := by decide

theorem reject10260 : Rejected (base 1 70 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 36) _ validLayout0265) (by decide) scope0483 (by rw [← fastBase_exact]; exact bind10260_0) certificate0525

private theorem bind10261_0 : Agrees (spec (fastBase 1 70 37) layout0266) scope0329 := by decide

theorem reject10261 : Rejected (base 1 70 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 37) _ validLayout0266) (by decide) scope0329 (by rw [← fastBase_exact]; exact bind10261_0) certificate0336

private theorem bind10262_0 : Agrees (spec (fastBase 1 70 38) layout0265) scope0563 := by decide

theorem reject10262 : Rejected (base 1 70 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 38) _ validLayout0265) (by decide) scope0563 (by rw [← fastBase_exact]; exact bind10262_0) certificate0606

private theorem bind10263_0 : Agrees (spec (fastBase 1 70 39) layout0265) scope0486 := by decide

theorem reject10263 : Rejected (base 1 70 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 39) _ validLayout0265) (by decide) scope0486 (by rw [← fastBase_exact]; exact bind10263_0) certificate0528

private theorem bind10264_0 : Agrees (spec (fastBase 1 70 40) layout0265) scope0565 := by decide

theorem reject10264 : Rejected (base 1 70 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 40) _ validLayout0265) (by decide) scope0565 (by rw [← fastBase_exact]; exact bind10264_0) certificate0608

private theorem bind10265_0 : Agrees (spec (fastBase 1 70 41) layout0288) scope0338 := by decide

theorem reject10265 : Rejected (base 1 70 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0288 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 41) _ validLayout0288) (by decide) scope0338 (by rw [← fastBase_exact]; exact bind10265_0) certificate0345

private theorem bind10266_0 : Agrees (spec (fastBase 1 70 42) layout0265) scope0484 := by decide

theorem reject10266 : Rejected (base 1 70 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 42) _ validLayout0265) (by decide) scope0484 (by rw [← fastBase_exact]; exact bind10266_0) certificate0526

private theorem bind10267_0 : Agrees (spec (fastBase 1 70 43) layout0265) scope0344 := by decide

theorem reject10267 : Rejected (base 1 70 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 43) _ validLayout0265) (by decide) scope0344 (by rw [← fastBase_exact]; exact bind10267_0) certificate0351

private theorem bind10268_0 : Agrees (spec (fastBase 1 70 44) layout0265) scope0567 := by decide

theorem reject10268 : Rejected (base 1 70 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 44) _ validLayout0265) (by decide) scope0567 (by rw [← fastBase_exact]; exact bind10268_0) certificate0610

private theorem bind10269_0 : Agrees (spec (fastBase 1 70 45) layout0265) scope0479 := by decide

theorem reject10269 : Rejected (base 1 70 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 45) _ validLayout0265) (by decide) scope0479 (by rw [← fastBase_exact]; exact bind10269_0) certificate0518

private theorem bind10270_0 : Agrees (spec (fastBase 1 70 46) layout0265) scope0564 := by decide

theorem reject10270 : Rejected (base 1 70 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 46) _ validLayout0265) (by decide) scope0564 (by rw [← fastBase_exact]; exact bind10270_0) certificate0607

private theorem bind10271_0 : Agrees (spec (fastBase 1 70 47) layout0266) scope0339 := by decide

theorem reject10271 : Rejected (base 1 70 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 47) _ validLayout0266) (by decide) scope0339 (by rw [← fastBase_exact]; exact bind10271_0) certificate0346

private theorem bind10272_0 : Agrees (spec (fastBase 1 70 48) layout0265) scope0482 := by decide

theorem reject10272 : Rejected (base 1 70 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 48) _ validLayout0265) (by decide) scope0482 (by rw [← fastBase_exact]; exact bind10272_0) certificate0524

private theorem bind10273_0 : Agrees (spec (fastBase 1 70 49) layout0265) scope0344 := by decide

theorem reject10273 : Rejected (base 1 70 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 49) _ validLayout0265) (by decide) scope0344 (by rw [← fastBase_exact]; exact bind10273_0) certificate0351

private theorem bind10274_0 : Agrees (spec (fastBase 1 70 50) layout0265) scope0479 := by decide

theorem reject10274 : Rejected (base 1 70 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 50) _ validLayout0265) (by decide) scope0479 (by rw [← fastBase_exact]; exact bind10274_0) certificate0518

private theorem bind10275_0 : Agrees (spec (fastBase 1 70 51) layout0265) scope0568 := by decide

theorem reject10275 : Rejected (base 1 70 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 51) _ validLayout0265) (by decide) scope0568 (by rw [← fastBase_exact]; exact bind10275_0) certificate0611

private theorem bind10276_0 : Agrees (spec (fastBase 1 70 52) layout0266) scope0341 := by decide

theorem reject10276 : Rejected (base 1 70 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0266 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 52) _ validLayout0266) (by decide) scope0341 (by rw [← fastBase_exact]; exact bind10276_0) certificate0348

private theorem bind10277_0 : Agrees (spec (fastBase 1 70 53) layout0265) scope0563 := by decide

theorem reject10277 : Rejected (base 1 70 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 53) _ validLayout0265) (by decide) scope0563 (by rw [← fastBase_exact]; exact bind10277_0) certificate0606

private theorem bind10278_0 : Agrees (spec (fastBase 1 70 54) layout0265) scope0566 := by decide

theorem reject10278 : Rejected (base 1 70 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 54) _ validLayout0265) (by decide) scope0566 (by rw [← fastBase_exact]; exact bind10278_0) certificate0609

private theorem bind10279_0 : Agrees (spec (fastBase 1 70 55) layout0265) scope0562 := by decide

theorem reject10279 : Rejected (base 1 70 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 55) _ validLayout0265) (by decide) scope0562 (by rw [← fastBase_exact]; exact bind10279_0) certificate0605

private theorem bind10280_0 : Agrees (spec (fastBase 1 70 56) layout0265) scope0345 := by decide

theorem reject10280 : Rejected (base 1 70 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 56) _ validLayout0265) (by decide) scope0345 (by rw [← fastBase_exact]; exact bind10280_0) certificate0352

private theorem bind10281_0 : Agrees (spec (fastBase 1 70 57) layout0265) scope0485 := by decide

theorem reject10281 : Rejected (base 1 70 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 57) _ validLayout0265) (by decide) scope0485 (by rw [← fastBase_exact]; exact bind10281_0) certificate0527

private theorem bind10282_0 : Agrees (spec (fastBase 1 70 58) layout0265) scope0485 := by decide

theorem reject10282 : Rejected (base 1 70 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 58) _ validLayout0265) (by decide) scope0485 (by rw [← fastBase_exact]; exact bind10282_0) certificate0527

private theorem bind10283_0 : Agrees (spec (fastBase 1 70 59) layout0265) scope0485 := by decide

theorem reject10283 : Rejected (base 1 70 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 59) _ validLayout0265) (by decide) scope0485 (by rw [← fastBase_exact]; exact bind10283_0) certificate0527

private theorem bind10284_0 : Agrees (spec (fastBase 1 70 60) layout0265) scope0485 := by decide

theorem reject10284 : Rejected (base 1 70 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 60) _ validLayout0265) (by decide) scope0485 (by rw [← fastBase_exact]; exact bind10284_0) certificate0527

private theorem bind10285_0 : Agrees (spec (fastBase 1 70 61) layout0265) scope0485 := by decide

theorem reject10285 : Rejected (base 1 70 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 61) _ validLayout0265) (by decide) scope0485 (by rw [← fastBase_exact]; exact bind10285_0) certificate0527

private theorem bind10286_0 : Agrees (spec (fastBase 1 70 62) layout0265) scope0345 := by decide

theorem reject10286 : Rejected (base 1 70 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 62) _ validLayout0265) (by decide) scope0345 (by rw [← fastBase_exact]; exact bind10286_0) certificate0352

private theorem bind10287_0 : Agrees (spec (fastBase 1 70 63) layout0265) scope0483 := by decide

theorem reject10287 : Rejected (base 1 70 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 63) _ validLayout0265) (by decide) scope0483 (by rw [← fastBase_exact]; exact bind10287_0) certificate0525

private theorem bind10288_0 : Agrees (spec (fastBase 1 70 64) layout0265) scope0567 := by decide

theorem reject10288 : Rejected (base 1 70 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 64) _ validLayout0265) (by decide) scope0567 (by rw [← fastBase_exact]; exact bind10288_0) certificate0610

private theorem bind10289_0 : Agrees (spec (fastBase 1 70 65) layout0265) scope0562 := by decide

theorem reject10289 : Rejected (base 1 70 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 65) _ validLayout0265) (by decide) scope0562 (by rw [← fastBase_exact]; exact bind10289_0) certificate0605

private theorem bind10290_0 : Agrees (spec (fastBase 1 70 66) layout0265) scope0564 := by decide

theorem reject10290 : Rejected (base 1 70 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 66) _ validLayout0265) (by decide) scope0564 (by rw [← fastBase_exact]; exact bind10290_0) certificate0607

private theorem bind10291_0 : Agrees (spec (fastBase 1 70 67) layout0265) scope0568 := by decide

theorem reject10291 : Rejected (base 1 70 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 67) _ validLayout0265) (by decide) scope0568 (by rw [← fastBase_exact]; exact bind10291_0) certificate0611

private theorem bind10292_0 : Agrees (spec (fastBase 1 70 68) layout0265) scope0566 := by decide

theorem reject10292 : Rejected (base 1 70 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 68) _ validLayout0265) (by decide) scope0566 (by rw [← fastBase_exact]; exact bind10292_0) certificate0609

private theorem bind10293_0 : Agrees (spec (fastBase 1 70 69) layout0265) scope0344 := by decide

theorem reject10293 : Rejected (base 1 70 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 69) _ validLayout0265) (by decide) scope0344 (by rw [← fastBase_exact]; exact bind10293_0) certificate0351

private theorem bind10294_0 : Agrees (spec (fastBase 1 70 70) layout0265) scope0564 := by decide

theorem reject10294 : Rejected (base 1 70 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 70) _ validLayout0265) (by decide) scope0564 (by rw [← fastBase_exact]; exact bind10294_0) certificate0607

private theorem bind10295_0 : Agrees (spec (fastBase 1 70 71) layout0265) scope0345 := by decide

theorem reject10295 : Rejected (base 1 70 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0265 (layoutValid_of_refines _ _ (base_refines_skeleton 1 70 71) _ validLayout0265) (by decide) scope0345 (by rw [← fastBase_exact]; exact bind10295_0) certificate0352

theorem allCases142 : ∀ y : Fin 72, Rejected (base 1 70 y) := by
  intro y
  fin_cases y

  · exact reject10224

  · exact reject10225

  · exact reject10226

  · exact reject10227

  · exact reject10228

  · exact reject10229

  · exact reject10230

  · exact reject10231

  · exact reject10232

  · exact reject10233

  · exact reject10234

  · exact reject10235

  · exact reject10236

  · exact reject10237

  · exact reject10238

  · exact reject10239

  · exact reject10240

  · exact reject10241

  · exact reject10242

  · exact reject10243

  · exact reject10244

  · exact reject10245

  · exact reject10246

  · exact reject10247

  · exact reject10248

  · exact reject10249

  · exact reject10250

  · exact reject10251

  · exact reject10252

  · exact reject10253

  · exact reject10254

  · exact reject10255

  · exact reject10256

  · exact reject10257

  · exact reject10258

  · exact reject10259

  · exact reject10260

  · exact reject10261

  · exact reject10262

  · exact reject10263

  · exact reject10264

  · exact reject10265

  · exact reject10266

  · exact reject10267

  · exact reject10268

  · exact reject10269

  · exact reject10270

  · exact reject10271

  · exact reject10272

  · exact reject10273

  · exact reject10274

  · exact reject10275

  · exact reject10276

  · exact reject10277

  · exact reject10278

  · exact reject10279

  · exact reject10280

  · exact reject10281

  · exact reject10282

  · exact reject10283

  · exact reject10284

  · exact reject10285

  · exact reject10286

  · exact reject10287

  · exact reject10288

  · exact reject10289

  · exact reject10290

  · exact reject10291

  · exact reject10292

  · exact reject10293

  · exact reject10294

  · exact reject10295

end PricingIntegration.RemainingGWitnesses
