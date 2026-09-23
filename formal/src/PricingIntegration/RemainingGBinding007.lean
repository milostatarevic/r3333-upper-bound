import PricingIntegration.RemainingGLayouts004

import PricingIntegration.RemainingGLayouts005

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks015


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00504_0 : Agrees (spec (fastBase 0 7 0) layout0035) scope0209 := by decide

theorem reject00504 : Rejected (base 0 7 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 0) _ validLayout0035) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind00504_0) certificate0212

private theorem bind00505_0 : Agrees (spec (fastBase 0 7 1) layout0035) scope0210 := by decide

theorem reject00505 : Rejected (base 0 7 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 1) _ validLayout0035) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind00505_0) certificate0213

private theorem bind00506_0 : Agrees (spec (fastBase 0 7 2) layout0035) scope0211 := by decide

theorem reject00506 : Rejected (base 0 7 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 2) _ validLayout0035) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind00506_0) certificate0214

private theorem bind00507_0 : Agrees (spec (fastBase 0 7 3) layout0036) scope0212 := by decide

private theorem bind00507_1 : Agrees (spec (fastBase 0 7 3) layout0037) scope0213 := by decide

theorem reject00507 : Rejected (base 0 7 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0036 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 3) _ validLayout0036) (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 3) _ validLayout0037) (by decide) (by decide) scope0212 scope0213 (by rw [← fastBase_exact]; exact bind00507_0) (by rw [← fastBase_exact]; exact bind00507_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0215 certificate0216 (by decide)

private theorem bind00508_0 : Agrees (spec (fastBase 0 7 4) layout0035) scope0214 := by decide

theorem reject00508 : Rejected (base 0 7 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 4) _ validLayout0035) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind00508_0) certificate0217

private theorem bind00509_0 : Agrees (spec (fastBase 0 7 5) layout0038) scope0215 := by decide

private theorem bind00509_1 : Agrees (spec (fastBase 0 7 5) layout0037) scope0216 := by decide

theorem reject00509 : Rejected (base 0 7 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0038 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 5) _ validLayout0038) (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 5) _ validLayout0037) (by decide) (by decide) scope0215 scope0216 (by rw [← fastBase_exact]; exact bind00509_0) (by rw [← fastBase_exact]; exact bind00509_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0219 (by decide)

private theorem bind00510_0 : Agrees (spec (fastBase 0 7 6) layout0035) scope0217 := by decide

theorem reject00510 : Rejected (base 0 7 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 6) _ validLayout0035) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind00510_0) certificate0220

private theorem bind00511_0 : Agrees (spec (fastBase 0 7 7) layout0035) scope0218 := by decide

theorem reject00511 : Rejected (base 0 7 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 7) _ validLayout0035) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind00511_0) certificate0221

private theorem bind00512_0 : Agrees (spec (fastBase 0 7 8) layout0035) scope0219 := by decide

theorem reject00512 : Rejected (base 0 7 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 8) _ validLayout0035) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind00512_0) certificate0222

private theorem bind00513_0 : Agrees (spec (fastBase 0 7 9) layout0035) scope0220 := by decide

theorem reject00513 : Rejected (base 0 7 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 9) _ validLayout0035) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind00513_0) certificate0223

private theorem bind00514_0 : Agrees (spec (fastBase 0 7 10) layout0035) scope0221 := by decide

theorem reject00514 : Rejected (base 0 7 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 10) _ validLayout0035) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind00514_0) certificate0224

private theorem bind00515_0 : Agrees (spec (fastBase 0 7 11) layout0035) scope0222 := by decide

theorem reject00515 : Rejected (base 0 7 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 11) _ validLayout0035) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind00515_0) certificate0225

private theorem bind00516_0 : Agrees (spec (fastBase 0 7 12) layout0035) scope0223 := by decide

theorem reject00516 : Rejected (base 0 7 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 12) _ validLayout0035) (by decide) scope0223 (by rw [← fastBase_exact]; exact bind00516_0) certificate0226

private theorem bind00517_0 : Agrees (spec (fastBase 0 7 13) layout0035) scope0211 := by decide

theorem reject00517 : Rejected (base 0 7 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 13) _ validLayout0035) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind00517_0) certificate0214

private theorem bind00518_0 : Agrees (spec (fastBase 0 7 14) layout0035) scope0209 := by decide

theorem reject00518 : Rejected (base 0 7 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 14) _ validLayout0035) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind00518_0) certificate0212

private theorem bind00519_0 : Agrees (spec (fastBase 0 7 15) layout0035) scope0224 := by decide

theorem reject00519 : Rejected (base 0 7 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 15) _ validLayout0035) (by decide) scope0224 (by rw [← fastBase_exact]; exact bind00519_0) certificate0227

private theorem bind00520_0 : Agrees (spec (fastBase 0 7 16) layout0035) scope0219 := by decide

theorem reject00520 : Rejected (base 0 7 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 16) _ validLayout0035) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind00520_0) certificate0222

private theorem bind00521_0 : Agrees (spec (fastBase 0 7 17) layout0039) scope0225 := by decide

private theorem bind00521_1 : Agrees (spec (fastBase 0 7 17) layout0036) scope0226 := by decide

theorem reject00521 : Rejected (base 0 7 17) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0039 layout0036 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 17) _ validLayout0039) (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 17) _ validLayout0036) (by decide) (by decide) scope0225 scope0226 (by rw [← fastBase_exact]; exact bind00521_0) (by rw [← fastBase_exact]; exact bind00521_1) 3 8 3 8 (by decide) (by decide) 2 3 (by decide) certificate0228 certificate0229 (by decide)

private theorem bind00522_0 : Agrees (spec (fastBase 0 7 18) layout0038) scope0210 := by decide

theorem reject00522 : Rejected (base 0 7 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 18) _ validLayout0038) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind00522_0) certificate0213

private theorem bind00523_0 : Agrees (spec (fastBase 0 7 19) layout0035) scope0214 := by decide

theorem reject00523 : Rejected (base 0 7 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 19) _ validLayout0035) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind00523_0) certificate0217

private theorem bind00524_0 : Agrees (spec (fastBase 0 7 20) layout0035) scope0210 := by decide

theorem reject00524 : Rejected (base 0 7 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 20) _ validLayout0035) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind00524_0) certificate0213

private theorem bind00525_0 : Agrees (spec (fastBase 0 7 21) layout0035) scope0227 := by decide

theorem reject00525 : Rejected (base 0 7 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 21) _ validLayout0035) (by decide) scope0227 (by rw [← fastBase_exact]; exact bind00525_0) certificate0230

private theorem bind00526_0 : Agrees (spec (fastBase 0 7 22) layout0035) scope0209 := by decide

theorem reject00526 : Rejected (base 0 7 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 22) _ validLayout0035) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind00526_0) certificate0212

private theorem bind00527_0 : Agrees (spec (fastBase 0 7 23) layout0035) scope0214 := by decide

theorem reject00527 : Rejected (base 0 7 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 23) _ validLayout0035) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind00527_0) certificate0217

private theorem bind00528_0 : Agrees (spec (fastBase 0 7 24) layout0040) scope0228 := by decide

theorem reject00528 : Rejected (base 0 7 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 24) _ validLayout0040) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind00528_0) certificate0231

private theorem bind00529_0 : Agrees (spec (fastBase 0 7 25) layout0035) scope0211 := by decide

theorem reject00529 : Rejected (base 0 7 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 25) _ validLayout0035) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind00529_0) certificate0214

private theorem bind00530_0 : Agrees (spec (fastBase 0 7 26) layout0035) scope0229 := by decide

theorem reject00530 : Rejected (base 0 7 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 26) _ validLayout0035) (by decide) scope0229 (by rw [← fastBase_exact]; exact bind00530_0) certificate0232

private theorem bind00531_0 : Agrees (spec (fastBase 0 7 27) layout0035) scope0210 := by decide

theorem reject00531 : Rejected (base 0 7 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 27) _ validLayout0035) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind00531_0) certificate0213

private theorem bind00532_0 : Agrees (spec (fastBase 0 7 28) layout0035) scope0230 := by decide

theorem reject00532 : Rejected (base 0 7 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 28) _ validLayout0035) (by decide) scope0230 (by rw [← fastBase_exact]; exact bind00532_0) certificate0233

private theorem bind00533_0 : Agrees (spec (fastBase 0 7 29) layout0036) scope0212 := by decide

private theorem bind00533_1 : Agrees (spec (fastBase 0 7 29) layout0037) scope0216 := by decide

theorem reject00533 : Rejected (base 0 7 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0036 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 29) _ validLayout0036) (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 29) _ validLayout0037) (by decide) (by decide) scope0212 scope0216 (by rw [← fastBase_exact]; exact bind00533_0) (by rw [← fastBase_exact]; exact bind00533_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0215 certificate0219 (by decide)

private theorem bind00534_0 : Agrees (spec (fastBase 0 7 30) layout0035) scope0231 := by decide

theorem reject00534 : Rejected (base 0 7 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 30) _ validLayout0035) (by decide) scope0231 (by rw [← fastBase_exact]; exact bind00534_0) certificate0234

private theorem bind00535_0 : Agrees (spec (fastBase 0 7 31) layout0035) scope0222 := by decide

theorem reject00535 : Rejected (base 0 7 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 31) _ validLayout0035) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind00535_0) certificate0225

private theorem bind00536_0 : Agrees (spec (fastBase 0 7 32) layout0035) scope0210 := by decide

theorem reject00536 : Rejected (base 0 7 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 32) _ validLayout0035) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind00536_0) certificate0213

private theorem bind00537_0 : Agrees (spec (fastBase 0 7 33) layout0035) scope0211 := by decide

theorem reject00537 : Rejected (base 0 7 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 33) _ validLayout0035) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind00537_0) certificate0214

private theorem bind00538_0 : Agrees (spec (fastBase 0 7 34) layout0035) scope0214 := by decide

theorem reject00538 : Rejected (base 0 7 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 34) _ validLayout0035) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind00538_0) certificate0217

private theorem bind00539_0 : Agrees (spec (fastBase 0 7 35) layout0035) scope0223 := by decide

theorem reject00539 : Rejected (base 0 7 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 35) _ validLayout0035) (by decide) scope0223 (by rw [← fastBase_exact]; exact bind00539_0) certificate0226

private theorem bind00540_0 : Agrees (spec (fastBase 0 7 36) layout0035) scope0230 := by decide

theorem reject00540 : Rejected (base 0 7 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 36) _ validLayout0035) (by decide) scope0230 (by rw [← fastBase_exact]; exact bind00540_0) certificate0233

private theorem bind00541_0 : Agrees (spec (fastBase 0 7 37) layout0040) scope0232 := by decide

theorem reject00541 : Rejected (base 0 7 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 37) _ validLayout0040) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind00541_0) certificate0235

private theorem bind00542_0 : Agrees (spec (fastBase 0 7 38) layout0040) scope0233 := by decide

theorem reject00542 : Rejected (base 0 7 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 38) _ validLayout0040) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind00542_0) certificate0236

private theorem bind00543_0 : Agrees (spec (fastBase 0 7 39) layout0038) scope0215 := by decide

private theorem bind00543_1 : Agrees (spec (fastBase 0 7 39) layout0037) scope0213 := by decide

theorem reject00543 : Rejected (base 0 7 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0038 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 39) _ validLayout0038) (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 39) _ validLayout0037) (by decide) (by decide) scope0215 scope0213 (by rw [← fastBase_exact]; exact bind00543_0) (by rw [← fastBase_exact]; exact bind00543_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0216 (by decide)

private theorem bind00544_0 : Agrees (spec (fastBase 0 7 40) layout0038) scope0220 := by decide

theorem reject00544 : Rejected (base 0 7 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 40) _ validLayout0038) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind00544_0) certificate0223

private theorem bind00545_0 : Agrees (spec (fastBase 0 7 41) layout0038) scope0221 := by decide

theorem reject00545 : Rejected (base 0 7 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 41) _ validLayout0038) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind00545_0) certificate0224

private theorem bind00546_0 : Agrees (spec (fastBase 0 7 42) layout0035) scope0217 := by decide

theorem reject00546 : Rejected (base 0 7 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 42) _ validLayout0035) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind00546_0) certificate0220

private theorem bind00547_0 : Agrees (spec (fastBase 0 7 43) layout0035) scope0217 := by decide

theorem reject00547 : Rejected (base 0 7 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 43) _ validLayout0035) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind00547_0) certificate0220

private theorem bind00548_0 : Agrees (spec (fastBase 0 7 44) layout0035) scope0217 := by decide

theorem reject00548 : Rejected (base 0 7 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 44) _ validLayout0035) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind00548_0) certificate0220

private theorem bind00549_0 : Agrees (spec (fastBase 0 7 45) layout0035) scope0217 := by decide

theorem reject00549 : Rejected (base 0 7 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 45) _ validLayout0035) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind00549_0) certificate0220

private theorem bind00550_0 : Agrees (spec (fastBase 0 7 46) layout0035) scope0217 := by decide

theorem reject00550 : Rejected (base 0 7 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 46) _ validLayout0035) (by decide) scope0217 (by rw [← fastBase_exact]; exact bind00550_0) certificate0220

private theorem bind00551_0 : Agrees (spec (fastBase 0 7 47) layout0035) scope0234 := by decide

theorem reject00551 : Rejected (base 0 7 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 47) _ validLayout0035) (by decide) scope0234 (by rw [← fastBase_exact]; exact bind00551_0) certificate0237

private theorem bind00552_0 : Agrees (spec (fastBase 0 7 48) layout0038) scope0231 := by decide

theorem reject00552 : Rejected (base 0 7 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 48) _ validLayout0038) (by decide) scope0231 (by rw [← fastBase_exact]; exact bind00552_0) certificate0234

private theorem bind00553_0 : Agrees (spec (fastBase 0 7 49) layout0035) scope0218 := by decide

theorem reject00553 : Rejected (base 0 7 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 49) _ validLayout0035) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind00553_0) certificate0221

private theorem bind00554_0 : Agrees (spec (fastBase 0 7 50) layout0035) scope0220 := by decide

theorem reject00554 : Rejected (base 0 7 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 50) _ validLayout0035) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind00554_0) certificate0223

private theorem bind00555_0 : Agrees (spec (fastBase 0 7 51) layout0035) scope0221 := by decide

theorem reject00555 : Rejected (base 0 7 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 51) _ validLayout0035) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind00555_0) certificate0224

private theorem bind00556_0 : Agrees (spec (fastBase 0 7 52) layout0035) scope0209 := by decide

theorem reject00556 : Rejected (base 0 7 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 52) _ validLayout0035) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind00556_0) certificate0212

private theorem bind00557_0 : Agrees (spec (fastBase 0 7 53) layout0035) scope0229 := by decide

theorem reject00557 : Rejected (base 0 7 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 53) _ validLayout0035) (by decide) scope0229 (by rw [← fastBase_exact]; exact bind00557_0) certificate0232

private theorem bind00558_0 : Agrees (spec (fastBase 0 7 54) layout0035) scope0219 := by decide

theorem reject00558 : Rejected (base 0 7 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 54) _ validLayout0035) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind00558_0) certificate0222

private theorem bind00559_0 : Agrees (spec (fastBase 0 7 55) layout0035) scope0234 := by decide

theorem reject00559 : Rejected (base 0 7 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 55) _ validLayout0035) (by decide) scope0234 (by rw [← fastBase_exact]; exact bind00559_0) certificate0237

private theorem bind00560_0 : Agrees (spec (fastBase 0 7 56) layout0035) scope0221 := by decide

theorem reject00560 : Rejected (base 0 7 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 56) _ validLayout0035) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind00560_0) certificate0224

private theorem bind00561_0 : Agrees (spec (fastBase 0 7 57) layout0035) scope0231 := by decide

theorem reject00561 : Rejected (base 0 7 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 57) _ validLayout0035) (by decide) scope0231 (by rw [← fastBase_exact]; exact bind00561_0) certificate0234

private theorem bind00562_0 : Agrees (spec (fastBase 0 7 58) layout0035) scope0220 := by decide

theorem reject00562 : Rejected (base 0 7 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 58) _ validLayout0035) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind00562_0) certificate0223

private theorem bind00563_0 : Agrees (spec (fastBase 0 7 59) layout0035) scope0235 := by decide

theorem reject00563 : Rejected (base 0 7 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 59) _ validLayout0035) (by decide) scope0235 (by rw [← fastBase_exact]; exact bind00563_0) certificate0238

private theorem bind00564_0 : Agrees (spec (fastBase 0 7 60) layout0035) scope0218 := by decide

theorem reject00564 : Rejected (base 0 7 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 60) _ validLayout0035) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind00564_0) certificate0221

private theorem bind00565_0 : Agrees (spec (fastBase 0 7 61) layout0035) scope0222 := by decide

theorem reject00565 : Rejected (base 0 7 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 61) _ validLayout0035) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind00565_0) certificate0225

private theorem bind00566_0 : Agrees (spec (fastBase 0 7 62) layout0035) scope0224 := by decide

theorem reject00566 : Rejected (base 0 7 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 62) _ validLayout0035) (by decide) scope0224 (by rw [← fastBase_exact]; exact bind00566_0) certificate0227

private theorem bind00567_0 : Agrees (spec (fastBase 0 7 63) layout0035) scope0221 := by decide

theorem reject00567 : Rejected (base 0 7 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 63) _ validLayout0035) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind00567_0) certificate0224

private theorem bind00568_0 : Agrees (spec (fastBase 0 7 64) layout0035) scope0218 := by decide

theorem reject00568 : Rejected (base 0 7 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 64) _ validLayout0035) (by decide) scope0218 (by rw [← fastBase_exact]; exact bind00568_0) certificate0221

private theorem bind00569_0 : Agrees (spec (fastBase 0 7 65) layout0035) scope0219 := by decide

theorem reject00569 : Rejected (base 0 7 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 65) _ validLayout0035) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind00569_0) certificate0222

private theorem bind00570_0 : Agrees (spec (fastBase 0 7 66) layout0035) scope0235 := by decide

theorem reject00570 : Rejected (base 0 7 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 66) _ validLayout0035) (by decide) scope0235 (by rw [← fastBase_exact]; exact bind00570_0) certificate0238

private theorem bind00571_0 : Agrees (spec (fastBase 0 7 67) layout0040) scope0236 := by decide

theorem reject00571 : Rejected (base 0 7 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 67) _ validLayout0040) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind00571_0) certificate0239

private theorem bind00572_0 : Agrees (spec (fastBase 0 7 68) layout0035) scope0227 := by decide

theorem reject00572 : Rejected (base 0 7 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 68) _ validLayout0035) (by decide) scope0227 (by rw [← fastBase_exact]; exact bind00572_0) certificate0230

private theorem bind00573_0 : Agrees (spec (fastBase 0 7 69) layout0035) scope0222 := by decide

theorem reject00573 : Rejected (base 0 7 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 69) _ validLayout0035) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind00573_0) certificate0225

private theorem bind00574_0 : Agrees (spec (fastBase 0 7 70) layout0035) scope0220 := by decide

theorem reject00574 : Rejected (base 0 7 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 70) _ validLayout0035) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind00574_0) certificate0223

private theorem bind00575_0 : Agrees (spec (fastBase 0 7 71) layout0039) scope0237 := by decide

private theorem bind00575_1 : Agrees (spec (fastBase 0 7 71) layout0036) scope0238 := by decide

theorem reject00575 : Rejected (base 0 7 71) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0039 layout0036 (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 71) _ validLayout0039) (layoutValid_of_refines _ _ (base_refines_skeleton 0 7 71) _ validLayout0036) (by decide) (by decide) scope0237 scope0238 (by rw [← fastBase_exact]; exact bind00575_0) (by rw [← fastBase_exact]; exact bind00575_1) 3 8 3 8 (by decide) (by decide) 3 2 (by decide) certificate0240 certificate0241 (by decide)

theorem allCases007 : ∀ y : Fin 72, Rejected (base 0 7 y) := by
  intro y
  fin_cases y

  · exact reject00504

  · exact reject00505

  · exact reject00506

  · exact reject00507

  · exact reject00508

  · exact reject00509

  · exact reject00510

  · exact reject00511

  · exact reject00512

  · exact reject00513

  · exact reject00514

  · exact reject00515

  · exact reject00516

  · exact reject00517

  · exact reject00518

  · exact reject00519

  · exact reject00520

  · exact reject00521

  · exact reject00522

  · exact reject00523

  · exact reject00524

  · exact reject00525

  · exact reject00526

  · exact reject00527

  · exact reject00528

  · exact reject00529

  · exact reject00530

  · exact reject00531

  · exact reject00532

  · exact reject00533

  · exact reject00534

  · exact reject00535

  · exact reject00536

  · exact reject00537

  · exact reject00538

  · exact reject00539

  · exact reject00540

  · exact reject00541

  · exact reject00542

  · exact reject00543

  · exact reject00544

  · exact reject00545

  · exact reject00546

  · exact reject00547

  · exact reject00548

  · exact reject00549

  · exact reject00550

  · exact reject00551

  · exact reject00552

  · exact reject00553

  · exact reject00554

  · exact reject00555

  · exact reject00556

  · exact reject00557

  · exact reject00558

  · exact reject00559

  · exact reject00560

  · exact reject00561

  · exact reject00562

  · exact reject00563

  · exact reject00564

  · exact reject00565

  · exact reject00566

  · exact reject00567

  · exact reject00568

  · exact reject00569

  · exact reject00570

  · exact reject00571

  · exact reject00572

  · exact reject00573

  · exact reject00574

  · exact reject00575

end PricingIntegration.RemainingGWitnesses
