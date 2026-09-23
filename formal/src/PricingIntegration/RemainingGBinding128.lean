import PricingIntegration.RemainingGLayouts027

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks015

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks030

import PricingIntegration.RemainingGScopeChecks038


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind09216_0 : Agrees (spec (fastBase 1 56 0) layout0220) scope0450 := by decide

theorem reject09216 : Rejected (base 1 56 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 0) _ validLayout0220) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind09216_0) certificate0483

private theorem bind09217_0 : Agrees (spec (fastBase 1 56 1) layout0221) scope0243 := by decide

theorem reject09217 : Rejected (base 1 56 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 1) _ validLayout0221) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind09217_0) certificate0246

private theorem bind09218_0 : Agrees (spec (fastBase 1 56 2) layout0220) scope0259 := by decide

theorem reject09218 : Rejected (base 1 56 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 2) _ validLayout0220) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind09218_0) certificate0262

private theorem bind09219_0 : Agrees (spec (fastBase 1 56 3) layout0221) scope0244 := by decide

private theorem bind09219_1 : Agrees (spec (fastBase 1 56 3) layout0222) scope0245 := by decide

theorem reject09219 : Rejected (base 1 56 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0221 layout0222 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 3) _ validLayout0221) (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 3) _ validLayout0222) (by decide) (by decide) scope0244 scope0245 (by rw [← fastBase_exact]; exact bind09219_0) (by rw [← fastBase_exact]; exact bind09219_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0247 certificate0248 (by decide)

private theorem bind09220_0 : Agrees (spec (fastBase 1 56 4) layout0220) scope0264 := by decide

theorem reject09220 : Rejected (base 1 56 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 4) _ validLayout0220) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind09220_0) certificate0267

private theorem bind09221_0 : Agrees (spec (fastBase 1 56 5) layout0220) scope0454 := by decide

theorem reject09221 : Rejected (base 1 56 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 5) _ validLayout0220) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind09221_0) certificate0489

private theorem bind09222_0 : Agrees (spec (fastBase 1 56 6) layout0220) scope0451 := by decide

theorem reject09222 : Rejected (base 1 56 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 6) _ validLayout0220) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind09222_0) certificate0484

private theorem bind09223_0 : Agrees (spec (fastBase 1 56 7) layout0220) scope0569 := by decide

theorem reject09223 : Rejected (base 1 56 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 7) _ validLayout0220) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind09223_0) certificate0612

private theorem bind09224_0 : Agrees (spec (fastBase 1 56 8) layout0220) scope0448 := by decide

theorem reject09224 : Rejected (base 1 56 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 8) _ validLayout0220) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind09224_0) certificate0480

private theorem bind09225_0 : Agrees (spec (fastBase 1 56 9) layout0220) scope0449 := by decide

theorem reject09225 : Rejected (base 1 56 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 9) _ validLayout0220) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind09225_0) certificate0481

private theorem bind09226_0 : Agrees (spec (fastBase 1 56 10) layout0220) scope0447 := by decide

theorem reject09226 : Rejected (base 1 56 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 10) _ validLayout0220) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind09226_0) certificate0479

private theorem bind09227_0 : Agrees (spec (fastBase 1 56 11) layout0220) scope0570 := by decide

theorem reject09227 : Rejected (base 1 56 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 11) _ validLayout0220) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind09227_0) certificate0613

private theorem bind09228_0 : Agrees (spec (fastBase 1 56 12) layout0221) scope0243 := by decide

theorem reject09228 : Rejected (base 1 56 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 12) _ validLayout0221) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind09228_0) certificate0246

private theorem bind09229_0 : Agrees (spec (fastBase 1 56 13) layout0220) scope0259 := by decide

theorem reject09229 : Rejected (base 1 56 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 13) _ validLayout0220) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind09229_0) certificate0262

private theorem bind09230_0 : Agrees (spec (fastBase 1 56 14) layout0220) scope0573 := by decide

theorem reject09230 : Rejected (base 1 56 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 14) _ validLayout0220) (by decide) scope0573 (by rw [← fastBase_exact]; exact bind09230_0) certificate0616

private theorem bind09231_0 : Agrees (spec (fastBase 1 56 15) layout0221) scope0254 := by decide

theorem reject09231 : Rejected (base 1 56 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 15) _ validLayout0221) (by decide) scope0254 (by rw [← fastBase_exact]; exact bind09231_0) certificate0257

private theorem bind09232_0 : Agrees (spec (fastBase 1 56 16) layout0220) scope0450 := by decide

theorem reject09232 : Rejected (base 1 56 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 16) _ validLayout0220) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind09232_0) certificate0483

private theorem bind09233_0 : Agrees (spec (fastBase 1 56 17) layout0220) scope0450 := by decide

theorem reject09233 : Rejected (base 1 56 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 17) _ validLayout0220) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind09233_0) certificate0483

private theorem bind09234_0 : Agrees (spec (fastBase 1 56 18) layout0222) scope0570 := by decide

theorem reject09234 : Rejected (base 1 56 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0222 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 18) _ validLayout0222) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind09234_0) certificate0613

private theorem bind09235_0 : Agrees (spec (fastBase 1 56 19) layout0220) scope0264 := by decide

theorem reject09235 : Rejected (base 1 56 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 19) _ validLayout0220) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind09235_0) certificate0267

private theorem bind09236_0 : Agrees (spec (fastBase 1 56 20) layout0220) scope0456 := by decide

theorem reject09236 : Rejected (base 1 56 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 20) _ validLayout0220) (by decide) scope0456 (by rw [← fastBase_exact]; exact bind09236_0) certificate0491

private theorem bind09237_0 : Agrees (spec (fastBase 1 56 21) layout0220) scope0453 := by decide

theorem reject09237 : Rejected (base 1 56 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 21) _ validLayout0220) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind09237_0) certificate0488

private theorem bind09238_0 : Agrees (spec (fastBase 1 56 22) layout0220) scope0450 := by decide

theorem reject09238 : Rejected (base 1 56 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 22) _ validLayout0220) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind09238_0) certificate0483

private theorem bind09239_0 : Agrees (spec (fastBase 1 56 23) layout0220) scope0456 := by decide

theorem reject09239 : Rejected (base 1 56 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 23) _ validLayout0220) (by decide) scope0456 (by rw [← fastBase_exact]; exact bind09239_0) certificate0491

private theorem bind09240_0 : Agrees (spec (fastBase 1 56 24) layout0220) scope0259 := by decide

theorem reject09240 : Rejected (base 1 56 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 24) _ validLayout0220) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind09240_0) certificate0262

private theorem bind09241_0 : Agrees (spec (fastBase 1 56 25) layout0220) scope0451 := by decide

theorem reject09241 : Rejected (base 1 56 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 25) _ validLayout0220) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind09241_0) certificate0484

private theorem bind09242_0 : Agrees (spec (fastBase 1 56 26) layout0220) scope0260 := by decide

theorem reject09242 : Rejected (base 1 56 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 26) _ validLayout0220) (by decide) scope0260 (by rw [← fastBase_exact]; exact bind09242_0) certificate0263

private theorem bind09243_0 : Agrees (spec (fastBase 1 56 27) layout0221) scope0243 := by decide

theorem reject09243 : Rejected (base 1 56 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 27) _ validLayout0221) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind09243_0) certificate0246

private theorem bind09244_0 : Agrees (spec (fastBase 1 56 28) layout0221) scope0239 := by decide

theorem reject09244 : Rejected (base 1 56 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 28) _ validLayout0221) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind09244_0) certificate0242

private theorem bind09245_0 : Agrees (spec (fastBase 1 56 29) layout0221) scope0244 := by decide

private theorem bind09245_1 : Agrees (spec (fastBase 1 56 29) layout0222) scope0245 := by decide

theorem reject09245 : Rejected (base 1 56 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0221 layout0222 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 29) _ validLayout0221) (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 29) _ validLayout0222) (by decide) (by decide) scope0244 scope0245 (by rw [← fastBase_exact]; exact bind09245_0) (by rw [← fastBase_exact]; exact bind09245_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0247 certificate0248 (by decide)

private theorem bind09246_0 : Agrees (spec (fastBase 1 56 30) layout0222) scope0259 := by decide

theorem reject09246 : Rejected (base 1 56 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0222 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 30) _ validLayout0222) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind09246_0) certificate0262

private theorem bind09247_0 : Agrees (spec (fastBase 1 56 31) layout0221) scope0244 := by decide

private theorem bind09247_1 : Agrees (spec (fastBase 1 56 31) layout0222) scope0250 := by decide

theorem reject09247 : Rejected (base 1 56 31) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0221 layout0222 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 31) _ validLayout0221) (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 31) _ validLayout0222) (by decide) (by decide) scope0244 scope0250 (by rw [← fastBase_exact]; exact bind09247_0) (by rw [← fastBase_exact]; exact bind09247_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0247 certificate0253 (by decide)

private theorem bind09248_0 : Agrees (spec (fastBase 1 56 32) layout0221) scope0240 := by decide

theorem reject09248 : Rejected (base 1 56 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 32) _ validLayout0221) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind09248_0) certificate0243

private theorem bind09249_0 : Agrees (spec (fastBase 1 56 33) layout0220) scope0573 := by decide

theorem reject09249 : Rejected (base 1 56 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 33) _ validLayout0220) (by decide) scope0573 (by rw [← fastBase_exact]; exact bind09249_0) certificate0616

private theorem bind09250_0 : Agrees (spec (fastBase 1 56 34) layout0220) scope0454 := by decide

theorem reject09250 : Rejected (base 1 56 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 34) _ validLayout0220) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind09250_0) certificate0489

private theorem bind09251_0 : Agrees (spec (fastBase 1 56 35) layout0220) scope0264 := by decide

theorem reject09251 : Rejected (base 1 56 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 35) _ validLayout0220) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind09251_0) certificate0267

private theorem bind09252_0 : Agrees (spec (fastBase 1 56 36) layout0221) scope0256 := by decide

theorem reject09252 : Rejected (base 1 56 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 36) _ validLayout0221) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind09252_0) certificate0259

private theorem bind09253_0 : Agrees (spec (fastBase 1 56 37) layout0220) scope0453 := by decide

theorem reject09253 : Rejected (base 1 56 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 37) _ validLayout0220) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind09253_0) certificate0488

private theorem bind09254_0 : Agrees (spec (fastBase 1 56 38) layout0220) scope0264 := by decide

theorem reject09254 : Rejected (base 1 56 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 38) _ validLayout0220) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind09254_0) certificate0267

private theorem bind09255_0 : Agrees (spec (fastBase 1 56 39) layout0220) scope0454 := by decide

theorem reject09255 : Rejected (base 1 56 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 39) _ validLayout0220) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind09255_0) certificate0489

private theorem bind09256_0 : Agrees (spec (fastBase 1 56 40) layout0220) scope0449 := by decide

theorem reject09256 : Rejected (base 1 56 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 40) _ validLayout0220) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind09256_0) certificate0481

private theorem bind09257_0 : Agrees (spec (fastBase 1 56 41) layout0220) scope0263 := by decide

theorem reject09257 : Rejected (base 1 56 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 41) _ validLayout0220) (by decide) scope0263 (by rw [← fastBase_exact]; exact bind09257_0) certificate0266

private theorem bind09258_0 : Agrees (spec (fastBase 1 56 42) layout0221) scope0257 := by decide

theorem reject09258 : Rejected (base 1 56 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0221 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 42) _ validLayout0221) (by decide) scope0257 (by rw [← fastBase_exact]; exact bind09258_0) certificate0260

private theorem bind09259_0 : Agrees (spec (fastBase 1 56 43) layout0220) scope0259 := by decide

theorem reject09259 : Rejected (base 1 56 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 43) _ validLayout0220) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind09259_0) certificate0262

private theorem bind09260_0 : Agrees (spec (fastBase 1 56 44) layout0220) scope0451 := by decide

theorem reject09260 : Rejected (base 1 56 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 44) _ validLayout0220) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind09260_0) certificate0484

private theorem bind09261_0 : Agrees (spec (fastBase 1 56 45) layout0220) scope0569 := by decide

theorem reject09261 : Rejected (base 1 56 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 45) _ validLayout0220) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind09261_0) certificate0612

private theorem bind09262_0 : Agrees (spec (fastBase 1 56 46) layout0220) scope0572 := by decide

theorem reject09262 : Rejected (base 1 56 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 46) _ validLayout0220) (by decide) scope0572 (by rw [← fastBase_exact]; exact bind09262_0) certificate0615

private theorem bind09263_0 : Agrees (spec (fastBase 1 56 47) layout0220) scope0260 := by decide

theorem reject09263 : Rejected (base 1 56 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 47) _ validLayout0220) (by decide) scope0260 (by rw [← fastBase_exact]; exact bind09263_0) certificate0263

private theorem bind09264_0 : Agrees (spec (fastBase 1 56 48) layout0220) scope0569 := by decide

theorem reject09264 : Rejected (base 1 56 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 48) _ validLayout0220) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind09264_0) certificate0612

private theorem bind09265_0 : Agrees (spec (fastBase 1 56 49) layout0220) scope0451 := by decide

theorem reject09265 : Rejected (base 1 56 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 49) _ validLayout0220) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind09265_0) certificate0484

private theorem bind09266_0 : Agrees (spec (fastBase 1 56 50) layout0220) scope0446 := by decide

theorem reject09266 : Rejected (base 1 56 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 50) _ validLayout0220) (by decide) scope0446 (by rw [← fastBase_exact]; exact bind09266_0) certificate0478

private theorem bind09267_0 : Agrees (spec (fastBase 1 56 51) layout0220) scope0447 := by decide

theorem reject09267 : Rejected (base 1 56 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 51) _ validLayout0220) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind09267_0) certificate0479

private theorem bind09268_0 : Agrees (spec (fastBase 1 56 52) layout0220) scope0448 := by decide

theorem reject09268 : Rejected (base 1 56 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 52) _ validLayout0220) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind09268_0) certificate0480

private theorem bind09269_0 : Agrees (spec (fastBase 1 56 53) layout0220) scope0448 := by decide

theorem reject09269 : Rejected (base 1 56 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 53) _ validLayout0220) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind09269_0) certificate0480

private theorem bind09270_0 : Agrees (spec (fastBase 1 56 54) layout0220) scope0448 := by decide

theorem reject09270 : Rejected (base 1 56 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 54) _ validLayout0220) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind09270_0) certificate0480

private theorem bind09271_0 : Agrees (spec (fastBase 1 56 55) layout0220) scope0448 := by decide

theorem reject09271 : Rejected (base 1 56 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 55) _ validLayout0220) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind09271_0) certificate0480

private theorem bind09272_0 : Agrees (spec (fastBase 1 56 56) layout0220) scope0448 := by decide

theorem reject09272 : Rejected (base 1 56 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 56) _ validLayout0220) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind09272_0) certificate0480

private theorem bind09273_0 : Agrees (spec (fastBase 1 56 57) layout0222) scope0263 := by decide

theorem reject09273 : Rejected (base 1 56 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0222 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 57) _ validLayout0222) (by decide) scope0263 (by rw [← fastBase_exact]; exact bind09273_0) certificate0266

private theorem bind09274_0 : Agrees (spec (fastBase 1 56 58) layout0220) scope0454 := by decide

theorem reject09274 : Rejected (base 1 56 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 58) _ validLayout0220) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind09274_0) certificate0489

private theorem bind09275_0 : Agrees (spec (fastBase 1 56 59) layout0220) scope0449 := by decide

theorem reject09275 : Rejected (base 1 56 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 59) _ validLayout0220) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind09275_0) certificate0481

private theorem bind09276_0 : Agrees (spec (fastBase 1 56 60) layout0220) scope0571 := by decide

theorem reject09276 : Rejected (base 1 56 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 60) _ validLayout0220) (by decide) scope0571 (by rw [← fastBase_exact]; exact bind09276_0) certificate0614

private theorem bind09277_0 : Agrees (spec (fastBase 1 56 61) layout0220) scope0570 := by decide

theorem reject09277 : Rejected (base 1 56 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 61) _ validLayout0220) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind09277_0) certificate0613

private theorem bind09278_0 : Agrees (spec (fastBase 1 56 62) layout0220) scope0572 := by decide

theorem reject09278 : Rejected (base 1 56 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 62) _ validLayout0220) (by decide) scope0572 (by rw [← fastBase_exact]; exact bind09278_0) certificate0615

private theorem bind09279_0 : Agrees (spec (fastBase 1 56 63) layout0220) scope0571 := by decide

theorem reject09279 : Rejected (base 1 56 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 63) _ validLayout0220) (by decide) scope0571 (by rw [← fastBase_exact]; exact bind09279_0) certificate0614

private theorem bind09280_0 : Agrees (spec (fastBase 1 56 64) layout0220) scope0569 := by decide

theorem reject09280 : Rejected (base 1 56 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 64) _ validLayout0220) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind09280_0) certificate0612

private theorem bind09281_0 : Agrees (spec (fastBase 1 56 65) layout0220) scope0447 := by decide

theorem reject09281 : Rejected (base 1 56 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 65) _ validLayout0220) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind09281_0) certificate0479

private theorem bind09282_0 : Agrees (spec (fastBase 1 56 66) layout0220) scope0570 := by decide

theorem reject09282 : Rejected (base 1 56 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 66) _ validLayout0220) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind09282_0) certificate0613

private theorem bind09283_0 : Agrees (spec (fastBase 1 56 67) layout0220) scope0570 := by decide

theorem reject09283 : Rejected (base 1 56 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 67) _ validLayout0220) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind09283_0) certificate0613

private theorem bind09284_0 : Agrees (spec (fastBase 1 56 68) layout0220) scope0263 := by decide

theorem reject09284 : Rejected (base 1 56 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 68) _ validLayout0220) (by decide) scope0263 (by rw [← fastBase_exact]; exact bind09284_0) certificate0266

private theorem bind09285_0 : Agrees (spec (fastBase 1 56 69) layout0220) scope0446 := by decide

theorem reject09285 : Rejected (base 1 56 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 69) _ validLayout0220) (by decide) scope0446 (by rw [← fastBase_exact]; exact bind09285_0) certificate0478

private theorem bind09286_0 : Agrees (spec (fastBase 1 56 70) layout0220) scope0449 := by decide

theorem reject09286 : Rejected (base 1 56 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 70) _ validLayout0220) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind09286_0) certificate0481

private theorem bind09287_0 : Agrees (spec (fastBase 1 56 71) layout0220) scope0447 := by decide

theorem reject09287 : Rejected (base 1 56 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0220 (layoutValid_of_refines _ _ (base_refines_skeleton 1 56 71) _ validLayout0220) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind09287_0) certificate0479

theorem allCases128 : ∀ y : Fin 72, Rejected (base 1 56 y) := by
  intro y
  fin_cases y

  · exact reject09216

  · exact reject09217

  · exact reject09218

  · exact reject09219

  · exact reject09220

  · exact reject09221

  · exact reject09222

  · exact reject09223

  · exact reject09224

  · exact reject09225

  · exact reject09226

  · exact reject09227

  · exact reject09228

  · exact reject09229

  · exact reject09230

  · exact reject09231

  · exact reject09232

  · exact reject09233

  · exact reject09234

  · exact reject09235

  · exact reject09236

  · exact reject09237

  · exact reject09238

  · exact reject09239

  · exact reject09240

  · exact reject09241

  · exact reject09242

  · exact reject09243

  · exact reject09244

  · exact reject09245

  · exact reject09246

  · exact reject09247

  · exact reject09248

  · exact reject09249

  · exact reject09250

  · exact reject09251

  · exact reject09252

  · exact reject09253

  · exact reject09254

  · exact reject09255

  · exact reject09256

  · exact reject09257

  · exact reject09258

  · exact reject09259

  · exact reject09260

  · exact reject09261

  · exact reject09262

  · exact reject09263

  · exact reject09264

  · exact reject09265

  · exact reject09266

  · exact reject09267

  · exact reject09268

  · exact reject09269

  · exact reject09270

  · exact reject09271

  · exact reject09272

  · exact reject09273

  · exact reject09274

  · exact reject09275

  · exact reject09276

  · exact reject09277

  · exact reject09278

  · exact reject09279

  · exact reject09280

  · exact reject09281

  · exact reject09282

  · exact reject09283

  · exact reject09284

  · exact reject09285

  · exact reject09286

  · exact reject09287

end PricingIntegration.RemainingGWitnesses
