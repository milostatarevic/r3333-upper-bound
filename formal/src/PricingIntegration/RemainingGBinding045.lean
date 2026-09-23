import PricingIntegration.RemainingGLayouts022

import PricingIntegration.RemainingGLayouts023

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks028


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03240_0 : Agrees (spec (fastBase 0 45 0) layout0180) scope0218 := by decide

theorem reject03240 : Rejected (base 0 45 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 0) _ validLayout0180) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind03240_0) certificate0221

private theorem bind03241_0 : Agrees (spec (fastBase 0 45 1) layout0180) scope0220 := by decide

theorem reject03241 : Rejected (base 0 45 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 1) _ validLayout0180) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03241_0) certificate0223

private theorem bind03242_0 : Agrees (spec (fastBase 0 45 2) layout0180) scope0221 := by decide

theorem reject03242 : Rejected (base 0 45 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 2) _ validLayout0180) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03242_0) certificate0224

private theorem bind03243_0 : Agrees (spec (fastBase 0 45 3) layout0181) scope0429 := by decide

private theorem bind03243_1 : Agrees (spec (fastBase 0 45 3) layout0182) scope0430 := by decide

theorem reject03243 : Rejected (base 0 45 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0181 layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 3) _ validLayout0181) (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 3) _ validLayout0182) (by decide) (by decide) scope0429 scope0430 (by rw [← fastBase_exact]; exact bind03243_0) (by rw [← fastBase_exact]; exact bind03243_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0456 certificate0457 (by decide)

private theorem bind03244_0 : Agrees (spec (fastBase 0 45 4) layout0180) scope0222 := by decide

theorem reject03244 : Rejected (base 0 45 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 4) _ validLayout0180) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind03244_0) certificate0225

private theorem bind03245_0 : Agrees (spec (fastBase 0 45 5) layout0181) scope0431 := by decide

private theorem bind03245_1 : Agrees (spec (fastBase 0 45 5) layout0182) scope0432 := by decide

theorem reject03245 : Rejected (base 0 45 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0181 layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 5) _ validLayout0181) (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 5) _ validLayout0182) (by decide) (by decide) scope0431 scope0432 (by rw [← fastBase_exact]; exact bind03245_0) (by rw [← fastBase_exact]; exact bind03245_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0458 certificate0459 (by decide)

private theorem bind03246_0 : Agrees (spec (fastBase 0 45 6) layout0180) scope0219 := by decide

theorem reject03246 : Rejected (base 0 45 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 6) _ validLayout0180) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind03246_0) certificate0222

private theorem bind03247_0 : Agrees (spec (fastBase 0 45 7) layout0180) scope0209 := by decide

theorem reject03247 : Rejected (base 0 45 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 7) _ validLayout0180) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03247_0) certificate0212

private theorem bind03248_0 : Agrees (spec (fastBase 0 45 8) layout0180) scope0217 := by decide

theorem reject03248 : Rejected (base 0 45 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 8) _ validLayout0180) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind03248_0) certificate0220

private theorem bind03249_0 : Agrees (spec (fastBase 0 45 9) layout0180) scope0210 := by decide

theorem reject03249 : Rejected (base 0 45 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 9) _ validLayout0180) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind03249_0) certificate0213

private theorem bind03250_0 : Agrees (spec (fastBase 0 45 10) layout0180) scope0211 := by decide

theorem reject03250 : Rejected (base 0 45 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 10) _ validLayout0180) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind03250_0) certificate0214

private theorem bind03251_0 : Agrees (spec (fastBase 0 45 11) layout0180) scope0214 := by decide

theorem reject03251 : Rejected (base 0 45 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 11) _ validLayout0180) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03251_0) certificate0217

private theorem bind03252_0 : Agrees (spec (fastBase 0 45 12) layout0180) scope0220 := by decide

theorem reject03252 : Rejected (base 0 45 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 12) _ validLayout0180) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03252_0) certificate0223

private theorem bind03253_0 : Agrees (spec (fastBase 0 45 13) layout0180) scope0221 := by decide

theorem reject03253 : Rejected (base 0 45 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 13) _ validLayout0180) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03253_0) certificate0224

private theorem bind03254_0 : Agrees (spec (fastBase 0 45 14) layout0183) scope0200 := by decide

theorem reject03254 : Rejected (base 0 45 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 14) _ validLayout0183) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind03254_0) certificate0203

private theorem bind03255_0 : Agrees (spec (fastBase 0 45 15) layout0180) scope0234 := by decide

theorem reject03255 : Rejected (base 0 45 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 15) _ validLayout0180) (by decide) scope0234 (by rw [← fastBase_exact]; exact bind03255_0) certificate0237

private theorem bind03256_0 : Agrees (spec (fastBase 0 45 16) layout0180) scope0218 := by decide

theorem reject03256 : Rejected (base 0 45 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 16) _ validLayout0180) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind03256_0) certificate0221

private theorem bind03257_0 : Agrees (spec (fastBase 0 45 17) layout0180) scope0218 := by decide

theorem reject03257 : Rejected (base 0 45 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 17) _ validLayout0180) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind03257_0) certificate0221

private theorem bind03258_0 : Agrees (spec (fastBase 0 45 18) layout0180) scope0220 := by decide

theorem reject03258 : Rejected (base 0 45 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 18) _ validLayout0180) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03258_0) certificate0223

private theorem bind03259_0 : Agrees (spec (fastBase 0 45 19) layout0180) scope0222 := by decide

theorem reject03259 : Rejected (base 0 45 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 19) _ validLayout0180) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind03259_0) certificate0225

private theorem bind03260_0 : Agrees (spec (fastBase 0 45 20) layout0180) scope0235 := by decide

theorem reject03260 : Rejected (base 0 45 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 20) _ validLayout0180) (by decide) scope0235 (by rw [← fastBase_exact]; exact bind03260_0) certificate0238

private theorem bind03261_0 : Agrees (spec (fastBase 0 45 21) layout0180) scope0231 := by decide

theorem reject03261 : Rejected (base 0 45 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 21) _ validLayout0180) (by decide) scope0231 (by rw [← fastBase_exact]; exact bind03261_0) certificate0234

private theorem bind03262_0 : Agrees (spec (fastBase 0 45 22) layout0180) scope0218 := by decide

theorem reject03262 : Rejected (base 0 45 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 22) _ validLayout0180) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind03262_0) certificate0221

private theorem bind03263_0 : Agrees (spec (fastBase 0 45 23) layout0180) scope0235 := by decide

theorem reject03263 : Rejected (base 0 45 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 23) _ validLayout0180) (by decide) scope0235 (by rw [← fastBase_exact]; exact bind03263_0) certificate0238

private theorem bind03264_0 : Agrees (spec (fastBase 0 45 24) layout0180) scope0221 := by decide

theorem reject03264 : Rejected (base 0 45 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 24) _ validLayout0180) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03264_0) certificate0224

private theorem bind03265_0 : Agrees (spec (fastBase 0 45 25) layout0180) scope0219 := by decide

theorem reject03265 : Rejected (base 0 45 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 25) _ validLayout0180) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind03265_0) certificate0222

private theorem bind03266_0 : Agrees (spec (fastBase 0 45 26) layout0180) scope0224 := by decide

theorem reject03266 : Rejected (base 0 45 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 26) _ validLayout0180) (by decide) scope0224 (by rw [← fastBase_exact]; exact bind03266_0) certificate0227

private theorem bind03267_0 : Agrees (spec (fastBase 0 45 27) layout0181) scope0433 := by decide

theorem reject03267 : Rejected (base 0 45 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0181 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 27) _ validLayout0181) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind03267_0) certificate0460

private theorem bind03268_0 : Agrees (spec (fastBase 0 45 28) layout0181) scope0434 := by decide

theorem reject03268 : Rejected (base 0 45 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0181 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 28) _ validLayout0181) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind03268_0) certificate0461

private theorem bind03269_0 : Agrees (spec (fastBase 0 45 29) layout0181) scope0429 := by decide

private theorem bind03269_1 : Agrees (spec (fastBase 0 45 29) layout0182) scope0432 := by decide

theorem reject03269 : Rejected (base 0 45 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0181 layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 29) _ validLayout0181) (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 29) _ validLayout0182) (by decide) (by decide) scope0429 scope0432 (by rw [← fastBase_exact]; exact bind03269_0) (by rw [← fastBase_exact]; exact bind03269_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0456 certificate0459 (by decide)

private theorem bind03270_0 : Agrees (spec (fastBase 0 45 30) layout0181) scope0232 := by decide

theorem reject03270 : Rejected (base 0 45 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0181 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 30) _ validLayout0181) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind03270_0) certificate0235

private theorem bind03271_0 : Agrees (spec (fastBase 0 45 31) layout0181) scope0233 := by decide

theorem reject03271 : Rejected (base 0 45 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0181 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 31) _ validLayout0181) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind03271_0) certificate0236

private theorem bind03272_0 : Agrees (spec (fastBase 0 45 32) layout0180) scope0220 := by decide

theorem reject03272 : Rejected (base 0 45 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 32) _ validLayout0180) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03272_0) certificate0223

private theorem bind03273_0 : Agrees (spec (fastBase 0 45 33) layout0183) scope0194 := by decide

theorem reject03273 : Rejected (base 0 45 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 33) _ validLayout0183) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind03273_0) certificate0197

private theorem bind03274_0 : Agrees (spec (fastBase 0 45 34) layout0184) scope0195 := by decide

theorem reject03274 : Rejected (base 0 45 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0184 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 34) _ validLayout0184) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind03274_0) certificate0198

private theorem bind03275_0 : Agrees (spec (fastBase 0 45 35) layout0180) scope0222 := by decide

theorem reject03275 : Rejected (base 0 45 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 35) _ validLayout0180) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind03275_0) certificate0225

private theorem bind03276_0 : Agrees (spec (fastBase 0 45 36) layout0180) scope0227 := by decide

theorem reject03276 : Rejected (base 0 45 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 36) _ validLayout0180) (by decide) scope0227 (by rw [← fastBase_exact]; exact bind03276_0) certificate0230

private theorem bind03277_0 : Agrees (spec (fastBase 0 45 37) layout0180) scope0231 := by decide

theorem reject03277 : Rejected (base 0 45 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 37) _ validLayout0180) (by decide) scope0231 (by rw [← fastBase_exact]; exact bind03277_0) certificate0234

private theorem bind03278_0 : Agrees (spec (fastBase 0 45 38) layout0180) scope0222 := by decide

theorem reject03278 : Rejected (base 0 45 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 38) _ validLayout0180) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind03278_0) certificate0225

private theorem bind03279_0 : Agrees (spec (fastBase 0 45 39) layout0181) scope0431 := by decide

private theorem bind03279_1 : Agrees (spec (fastBase 0 45 39) layout0182) scope0430 := by decide

theorem reject03279 : Rejected (base 0 45 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0181 layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 39) _ validLayout0181) (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 39) _ validLayout0182) (by decide) (by decide) scope0431 scope0430 (by rw [← fastBase_exact]; exact bind03279_0) (by rw [← fastBase_exact]; exact bind03279_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0458 certificate0457 (by decide)

private theorem bind03280_0 : Agrees (spec (fastBase 0 45 40) layout0180) scope0210 := by decide

theorem reject03280 : Rejected (base 0 45 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 40) _ validLayout0180) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind03280_0) certificate0213

private theorem bind03281_0 : Agrees (spec (fastBase 0 45 41) layout0180) scope0230 := by decide

theorem reject03281 : Rejected (base 0 45 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 41) _ validLayout0180) (by decide) scope0230 (by rw [← fastBase_exact]; exact bind03281_0) certificate0233

private theorem bind03282_0 : Agrees (spec (fastBase 0 45 42) layout0180) scope0234 := by decide

theorem reject03282 : Rejected (base 0 45 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 42) _ validLayout0180) (by decide) scope0234 (by rw [← fastBase_exact]; exact bind03282_0) certificate0237

private theorem bind03283_0 : Agrees (spec (fastBase 0 45 43) layout0180) scope0221 := by decide

theorem reject03283 : Rejected (base 0 45 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 43) _ validLayout0180) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03283_0) certificate0224

private theorem bind03284_0 : Agrees (spec (fastBase 0 45 44) layout0180) scope0219 := by decide

theorem reject03284 : Rejected (base 0 45 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 44) _ validLayout0180) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind03284_0) certificate0222

private theorem bind03285_0 : Agrees (spec (fastBase 0 45 45) layout0180) scope0209 := by decide

theorem reject03285 : Rejected (base 0 45 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 45) _ validLayout0180) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03285_0) certificate0212

private theorem bind03286_0 : Agrees (spec (fastBase 0 45 46) layout0180) scope0229 := by decide

theorem reject03286 : Rejected (base 0 45 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 46) _ validLayout0180) (by decide) scope0229 (by rw [← fastBase_exact]; exact bind03286_0) certificate0232

private theorem bind03287_0 : Agrees (spec (fastBase 0 45 47) layout0180) scope0224 := by decide

theorem reject03287 : Rejected (base 0 45 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 47) _ validLayout0180) (by decide) scope0224 (by rw [← fastBase_exact]; exact bind03287_0) certificate0227

private theorem bind03288_0 : Agrees (spec (fastBase 0 45 48) layout0180) scope0209 := by decide

theorem reject03288 : Rejected (base 0 45 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 48) _ validLayout0180) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03288_0) certificate0212

private theorem bind03289_0 : Agrees (spec (fastBase 0 45 49) layout0180) scope0219 := by decide

theorem reject03289 : Rejected (base 0 45 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 49) _ validLayout0180) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind03289_0) certificate0222

private theorem bind03290_0 : Agrees (spec (fastBase 0 45 50) layout0180) scope0223 := by decide

theorem reject03290 : Rejected (base 0 45 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 50) _ validLayout0180) (by decide) scope0223 (by rw [← fastBase_exact]; exact bind03290_0) certificate0226

private theorem bind03291_0 : Agrees (spec (fastBase 0 45 51) layout0180) scope0211 := by decide

theorem reject03291 : Rejected (base 0 45 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 51) _ validLayout0180) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind03291_0) certificate0214

private theorem bind03292_0 : Agrees (spec (fastBase 0 45 52) layout0180) scope0217 := by decide

theorem reject03292 : Rejected (base 0 45 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 52) _ validLayout0180) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind03292_0) certificate0220

private theorem bind03293_0 : Agrees (spec (fastBase 0 45 53) layout0180) scope0217 := by decide

theorem reject03293 : Rejected (base 0 45 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 53) _ validLayout0180) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind03293_0) certificate0220

private theorem bind03294_0 : Agrees (spec (fastBase 0 45 54) layout0180) scope0217 := by decide

theorem reject03294 : Rejected (base 0 45 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 54) _ validLayout0180) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind03294_0) certificate0220

private theorem bind03295_0 : Agrees (spec (fastBase 0 45 55) layout0180) scope0217 := by decide

theorem reject03295 : Rejected (base 0 45 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 55) _ validLayout0180) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind03295_0) certificate0220

private theorem bind03296_0 : Agrees (spec (fastBase 0 45 56) layout0180) scope0217 := by decide

theorem reject03296 : Rejected (base 0 45 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 56) _ validLayout0180) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind03296_0) certificate0220

private theorem bind03297_0 : Agrees (spec (fastBase 0 45 57) layout0180) scope0227 := by decide

theorem reject03297 : Rejected (base 0 45 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 57) _ validLayout0180) (by decide) scope0227 (by rw [← fastBase_exact]; exact bind03297_0) certificate0230

private theorem bind03298_0 : Agrees (spec (fastBase 0 45 58) layout0183) scope0191 := by decide

theorem reject03298 : Rejected (base 0 45 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 58) _ validLayout0183) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03298_0) certificate0194

private theorem bind03299_0 : Agrees (spec (fastBase 0 45 59) layout0180) scope0210 := by decide

theorem reject03299 : Rejected (base 0 45 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 59) _ validLayout0180) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind03299_0) certificate0213

private theorem bind03300_0 : Agrees (spec (fastBase 0 45 60) layout0183) scope0203 := by decide

theorem reject03300 : Rejected (base 0 45 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 60) _ validLayout0183) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03300_0) certificate0206

private theorem bind03301_0 : Agrees (spec (fastBase 0 45 61) layout0180) scope0214 := by decide

theorem reject03301 : Rejected (base 0 45 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 61) _ validLayout0180) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03301_0) certificate0217

private theorem bind03302_0 : Agrees (spec (fastBase 0 45 62) layout0180) scope0229 := by decide

theorem reject03302 : Rejected (base 0 45 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 62) _ validLayout0180) (by decide) scope0229 (by rw [← fastBase_exact]; exact bind03302_0) certificate0232

private theorem bind03303_0 : Agrees (spec (fastBase 0 45 63) layout0183) scope0203 := by decide

theorem reject03303 : Rejected (base 0 45 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 63) _ validLayout0183) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03303_0) certificate0206

private theorem bind03304_0 : Agrees (spec (fastBase 0 45 64) layout0180) scope0209 := by decide

theorem reject03304 : Rejected (base 0 45 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 64) _ validLayout0180) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03304_0) certificate0212

private theorem bind03305_0 : Agrees (spec (fastBase 0 45 65) layout0180) scope0211 := by decide

theorem reject03305 : Rejected (base 0 45 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 65) _ validLayout0180) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind03305_0) certificate0214

private theorem bind03306_0 : Agrees (spec (fastBase 0 45 66) layout0180) scope0214 := by decide

theorem reject03306 : Rejected (base 0 45 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 66) _ validLayout0180) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03306_0) certificate0217

private theorem bind03307_0 : Agrees (spec (fastBase 0 45 67) layout0180) scope0214 := by decide

theorem reject03307 : Rejected (base 0 45 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 67) _ validLayout0180) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03307_0) certificate0217

private theorem bind03308_0 : Agrees (spec (fastBase 0 45 68) layout0180) scope0230 := by decide

theorem reject03308 : Rejected (base 0 45 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 68) _ validLayout0180) (by decide) scope0230 (by rw [← fastBase_exact]; exact bind03308_0) certificate0233

private theorem bind03309_0 : Agrees (spec (fastBase 0 45 69) layout0180) scope0223 := by decide

theorem reject03309 : Rejected (base 0 45 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 69) _ validLayout0180) (by decide) scope0223 (by rw [← fastBase_exact]; exact bind03309_0) certificate0226

private theorem bind03310_0 : Agrees (spec (fastBase 0 45 70) layout0180) scope0210 := by decide

theorem reject03310 : Rejected (base 0 45 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 70) _ validLayout0180) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind03310_0) certificate0213

private theorem bind03311_0 : Agrees (spec (fastBase 0 45 71) layout0180) scope0211 := by decide

theorem reject03311 : Rejected (base 0 45 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 0 45 71) _ validLayout0180) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind03311_0) certificate0214

theorem allCases045 : ∀ y : Fin 72, Rejected (base 0 45 y) := by
  intro y
  fin_cases y

  · exact reject03240

  · exact reject03241

  · exact reject03242

  · exact reject03243

  · exact reject03244

  · exact reject03245

  · exact reject03246

  · exact reject03247

  · exact reject03248

  · exact reject03249

  · exact reject03250

  · exact reject03251

  · exact reject03252

  · exact reject03253

  · exact reject03254

  · exact reject03255

  · exact reject03256

  · exact reject03257

  · exact reject03258

  · exact reject03259

  · exact reject03260

  · exact reject03261

  · exact reject03262

  · exact reject03263

  · exact reject03264

  · exact reject03265

  · exact reject03266

  · exact reject03267

  · exact reject03268

  · exact reject03269

  · exact reject03270

  · exact reject03271

  · exact reject03272

  · exact reject03273

  · exact reject03274

  · exact reject03275

  · exact reject03276

  · exact reject03277

  · exact reject03278

  · exact reject03279

  · exact reject03280

  · exact reject03281

  · exact reject03282

  · exact reject03283

  · exact reject03284

  · exact reject03285

  · exact reject03286

  · exact reject03287

  · exact reject03288

  · exact reject03289

  · exact reject03290

  · exact reject03291

  · exact reject03292

  · exact reject03293

  · exact reject03294

  · exact reject03295

  · exact reject03296

  · exact reject03297

  · exact reject03298

  · exact reject03299

  · exact reject03300

  · exact reject03301

  · exact reject03302

  · exact reject03303

  · exact reject03304

  · exact reject03305

  · exact reject03306

  · exact reject03307

  · exact reject03308

  · exact reject03309

  · exact reject03310

  · exact reject03311

end PricingIntegration.RemainingGWitnesses
