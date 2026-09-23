import PricingIntegration.RemainingGLayouts024

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03528_0 : Agrees (spec (fastBase 0 49 0) layout0195) scope0185 := by decide

theorem reject03528 : Rejected (base 0 49 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 0) _ validLayout0195) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03528_0) certificate0188

private theorem bind03529_0 : Agrees (spec (fastBase 0 49 1) layout0196) scope0214 := by decide

theorem reject03529 : Rejected (base 0 49 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 1) _ validLayout0196) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03529_0) certificate0217

private theorem bind03530_0 : Agrees (spec (fastBase 0 49 2) layout0196) scope0209 := by decide

theorem reject03530 : Rejected (base 0 49 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 2) _ validLayout0196) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03530_0) certificate0212

private theorem bind03531_0 : Agrees (spec (fastBase 0 49 3) layout0196) scope0215 := by decide

private theorem bind03531_1 : Agrees (spec (fastBase 0 49 3) layout0197) scope0213 := by decide

theorem reject03531 : Rejected (base 0 49 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0196 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 3) _ validLayout0196) (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 3) _ validLayout0197) (by decide) (by decide) scope0215 scope0213 (by rw [← fastBase_exact]; exact bind03531_0) (by rw [← fastBase_exact]; exact bind03531_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0216 (by decide)

private theorem bind03532_0 : Agrees (spec (fastBase 0 49 4) layout0195) scope0191 := by decide

theorem reject03532 : Rejected (base 0 49 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 4) _ validLayout0195) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03532_0) certificate0194

private theorem bind03533_0 : Agrees (spec (fastBase 0 49 5) layout0198) scope0440 := by decide

private theorem bind03533_1 : Agrees (spec (fastBase 0 49 5) layout0197) scope0216 := by decide

theorem reject03533 : Rejected (base 0 49 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0198 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 5) _ validLayout0198) (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 5) _ validLayout0197) (by decide) (by decide) scope0440 scope0216 (by rw [← fastBase_exact]; exact bind03533_0) (by rw [← fastBase_exact]; exact bind03533_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0469 certificate0219 (by decide)

private theorem bind03534_0 : Agrees (spec (fastBase 0 49 6) layout0195) scope0186 := by decide

theorem reject03534 : Rejected (base 0 49 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 6) _ validLayout0195) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03534_0) certificate0189

private theorem bind03535_0 : Agrees (spec (fastBase 0 49 7) layout0196) scope0221 := by decide

theorem reject03535 : Rejected (base 0 49 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 7) _ validLayout0196) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03535_0) certificate0224

private theorem bind03536_0 : Agrees (spec (fastBase 0 49 8) layout0195) scope0184 := by decide

theorem reject03536 : Rejected (base 0 49 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 8) _ validLayout0195) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03536_0) certificate0187

private theorem bind03537_0 : Agrees (spec (fastBase 0 49 9) layout0195) scope0176 := by decide

theorem reject03537 : Rejected (base 0 49 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 9) _ validLayout0195) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03537_0) certificate0179

private theorem bind03538_0 : Agrees (spec (fastBase 0 49 10) layout0195) scope0177 := by decide

theorem reject03538 : Rejected (base 0 49 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 10) _ validLayout0195) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03538_0) certificate0180

private theorem bind03539_0 : Agrees (spec (fastBase 0 49 11) layout0196) scope0220 := by decide

theorem reject03539 : Rejected (base 0 49 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 11) _ validLayout0196) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03539_0) certificate0223

private theorem bind03540_0 : Agrees (spec (fastBase 0 49 12) layout0196) scope0214 := by decide

theorem reject03540 : Rejected (base 0 49 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 12) _ validLayout0196) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03540_0) certificate0217

private theorem bind03541_0 : Agrees (spec (fastBase 0 49 13) layout0196) scope0211 := by decide

theorem reject03541 : Rejected (base 0 49 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 13) _ validLayout0196) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind03541_0) certificate0214

private theorem bind03542_0 : Agrees (spec (fastBase 0 49 14) layout0195) scope0203 := by decide

theorem reject03542 : Rejected (base 0 49 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 14) _ validLayout0195) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03542_0) certificate0206

private theorem bind03543_0 : Agrees (spec (fastBase 0 49 15) layout0195) scope0202 := by decide

theorem reject03543 : Rejected (base 0 49 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 15) _ validLayout0195) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind03543_0) certificate0205

private theorem bind03544_0 : Agrees (spec (fastBase 0 49 16) layout0195) scope0185 := by decide

theorem reject03544 : Rejected (base 0 49 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 16) _ validLayout0195) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03544_0) certificate0188

private theorem bind03545_0 : Agrees (spec (fastBase 0 49 17) layout0195) scope0185 := by decide

theorem reject03545 : Rejected (base 0 49 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 17) _ validLayout0195) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03545_0) certificate0188

private theorem bind03546_0 : Agrees (spec (fastBase 0 49 18) layout0196) scope0214 := by decide

theorem reject03546 : Rejected (base 0 49 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 18) _ validLayout0196) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03546_0) certificate0217

private theorem bind03547_0 : Agrees (spec (fastBase 0 49 19) layout0195) scope0191 := by decide

theorem reject03547 : Rejected (base 0 49 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 19) _ validLayout0195) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03547_0) certificate0194

private theorem bind03548_0 : Agrees (spec (fastBase 0 49 20) layout0195) scope0207 := by decide

theorem reject03548 : Rejected (base 0 49 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 20) _ validLayout0195) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind03548_0) certificate0210

private theorem bind03549_0 : Agrees (spec (fastBase 0 49 21) layout0195) scope0201 := by decide

theorem reject03549 : Rejected (base 0 49 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 21) _ validLayout0195) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind03549_0) certificate0204

private theorem bind03550_0 : Agrees (spec (fastBase 0 49 22) layout0195) scope0185 := by decide

theorem reject03550 : Rejected (base 0 49 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 22) _ validLayout0195) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03550_0) certificate0188

private theorem bind03551_0 : Agrees (spec (fastBase 0 49 23) layout0195) scope0207 := by decide

theorem reject03551 : Rejected (base 0 49 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 23) _ validLayout0195) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind03551_0) certificate0210

private theorem bind03552_0 : Agrees (spec (fastBase 0 49 24) layout0196) scope0209 := by decide

theorem reject03552 : Rejected (base 0 49 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 24) _ validLayout0196) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03552_0) certificate0212

private theorem bind03553_0 : Agrees (spec (fastBase 0 49 25) layout0195) scope0186 := by decide

theorem reject03553 : Rejected (base 0 49 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 25) _ validLayout0195) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03553_0) certificate0189

private theorem bind03554_0 : Agrees (spec (fastBase 0 49 26) layout0195) scope0193 := by decide

theorem reject03554 : Rejected (base 0 49 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 26) _ validLayout0195) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind03554_0) certificate0196

private theorem bind03555_0 : Agrees (spec (fastBase 0 49 27) layout0199) scope0233 := by decide

theorem reject03555 : Rejected (base 0 49 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 27) _ validLayout0199) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind03555_0) certificate0236

private theorem bind03556_0 : Agrees (spec (fastBase 0 49 28) layout0199) scope0232 := by decide

theorem reject03556 : Rejected (base 0 49 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 28) _ validLayout0199) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind03556_0) certificate0235

private theorem bind03557_0 : Agrees (spec (fastBase 0 49 29) layout0196) scope0215 := by decide

private theorem bind03557_1 : Agrees (spec (fastBase 0 49 29) layout0197) scope0216 := by decide

theorem reject03557 : Rejected (base 0 49 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0196 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 29) _ validLayout0196) (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 29) _ validLayout0197) (by decide) (by decide) scope0215 scope0216 (by rw [← fastBase_exact]; exact bind03557_0) (by rw [← fastBase_exact]; exact bind03557_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0219 (by decide)

private theorem bind03558_0 : Agrees (spec (fastBase 0 49 30) layout0196) scope0221 := by decide

theorem reject03558 : Rejected (base 0 49 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 30) _ validLayout0196) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03558_0) certificate0224

private theorem bind03559_0 : Agrees (spec (fastBase 0 49 31) layout0196) scope0220 := by decide

theorem reject03559 : Rejected (base 0 49 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 31) _ validLayout0196) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03559_0) certificate0223

private theorem bind03560_0 : Agrees (spec (fastBase 0 49 32) layout0196) scope0214 := by decide

theorem reject03560 : Rejected (base 0 49 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 32) _ validLayout0196) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind03560_0) certificate0217

private theorem bind03561_0 : Agrees (spec (fastBase 0 49 33) layout0195) scope0203 := by decide

theorem reject03561 : Rejected (base 0 49 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 33) _ validLayout0195) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03561_0) certificate0206

private theorem bind03562_0 : Agrees (spec (fastBase 0 49 34) layout0196) scope0210 := by decide

theorem reject03562 : Rejected (base 0 49 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 34) _ validLayout0196) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind03562_0) certificate0213

private theorem bind03563_0 : Agrees (spec (fastBase 0 49 35) layout0195) scope0191 := by decide

theorem reject03563 : Rejected (base 0 49 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 35) _ validLayout0195) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03563_0) certificate0194

private theorem bind03564_0 : Agrees (spec (fastBase 0 49 36) layout0195) scope0196 := by decide

theorem reject03564 : Rejected (base 0 49 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 36) _ validLayout0195) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind03564_0) certificate0199

private theorem bind03565_0 : Agrees (spec (fastBase 0 49 37) layout0195) scope0201 := by decide

theorem reject03565 : Rejected (base 0 49 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 37) _ validLayout0195) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind03565_0) certificate0204

private theorem bind03566_0 : Agrees (spec (fastBase 0 49 38) layout0195) scope0191 := by decide

theorem reject03566 : Rejected (base 0 49 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 38) _ validLayout0195) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03566_0) certificate0194

private theorem bind03567_0 : Agrees (spec (fastBase 0 49 39) layout0198) scope0440 := by decide

private theorem bind03567_1 : Agrees (spec (fastBase 0 49 39) layout0197) scope0213 := by decide

theorem reject03567 : Rejected (base 0 49 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0198 layout0197 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 39) _ validLayout0198) (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 39) _ validLayout0197) (by decide) (by decide) scope0440 scope0213 (by rw [← fastBase_exact]; exact bind03567_0) (by rw [← fastBase_exact]; exact bind03567_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0469 certificate0216 (by decide)

private theorem bind03568_0 : Agrees (spec (fastBase 0 49 40) layout0195) scope0176 := by decide

theorem reject03568 : Rejected (base 0 49 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 40) _ validLayout0195) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03568_0) certificate0179

private theorem bind03569_0 : Agrees (spec (fastBase 0 49 41) layout0195) scope0200 := by decide

theorem reject03569 : Rejected (base 0 49 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 41) _ validLayout0195) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind03569_0) certificate0203

private theorem bind03570_0 : Agrees (spec (fastBase 0 49 42) layout0195) scope0202 := by decide

theorem reject03570 : Rejected (base 0 49 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 42) _ validLayout0195) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind03570_0) certificate0205

private theorem bind03571_0 : Agrees (spec (fastBase 0 49 43) layout0196) scope0209 := by decide

theorem reject03571 : Rejected (base 0 49 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 43) _ validLayout0196) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind03571_0) certificate0212

private theorem bind03572_0 : Agrees (spec (fastBase 0 49 44) layout0195) scope0186 := by decide

theorem reject03572 : Rejected (base 0 49 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 44) _ validLayout0195) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03572_0) certificate0189

private theorem bind03573_0 : Agrees (spec (fastBase 0 49 45) layout0196) scope0219 := by decide

theorem reject03573 : Rejected (base 0 49 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 45) _ validLayout0196) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind03573_0) certificate0222

private theorem bind03574_0 : Agrees (spec (fastBase 0 49 46) layout0195) scope0199 := by decide

theorem reject03574 : Rejected (base 0 49 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 46) _ validLayout0195) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind03574_0) certificate0202

private theorem bind03575_0 : Agrees (spec (fastBase 0 49 47) layout0195) scope0193 := by decide

theorem reject03575 : Rejected (base 0 49 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 47) _ validLayout0195) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind03575_0) certificate0196

private theorem bind03576_0 : Agrees (spec (fastBase 0 49 48) layout0199) scope0434 := by decide

theorem reject03576 : Rejected (base 0 49 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 48) _ validLayout0199) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind03576_0) certificate0461

private theorem bind03577_0 : Agrees (spec (fastBase 0 49 49) layout0195) scope0186 := by decide

theorem reject03577 : Rejected (base 0 49 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 49) _ validLayout0195) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03577_0) certificate0189

private theorem bind03578_0 : Agrees (spec (fastBase 0 49 50) layout0195) scope0192 := by decide

theorem reject03578 : Rejected (base 0 49 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 50) _ validLayout0195) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind03578_0) certificate0195

private theorem bind03579_0 : Agrees (spec (fastBase 0 49 51) layout0195) scope0177 := by decide

theorem reject03579 : Rejected (base 0 49 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 51) _ validLayout0195) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03579_0) certificate0180

private theorem bind03580_0 : Agrees (spec (fastBase 0 49 52) layout0195) scope0184 := by decide

theorem reject03580 : Rejected (base 0 49 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 52) _ validLayout0195) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03580_0) certificate0187

private theorem bind03581_0 : Agrees (spec (fastBase 0 49 53) layout0195) scope0184 := by decide

theorem reject03581 : Rejected (base 0 49 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 53) _ validLayout0195) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03581_0) certificate0187

private theorem bind03582_0 : Agrees (spec (fastBase 0 49 54) layout0195) scope0184 := by decide

theorem reject03582 : Rejected (base 0 49 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 54) _ validLayout0195) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03582_0) certificate0187

private theorem bind03583_0 : Agrees (spec (fastBase 0 49 55) layout0195) scope0184 := by decide

theorem reject03583 : Rejected (base 0 49 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 55) _ validLayout0195) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03583_0) certificate0187

private theorem bind03584_0 : Agrees (spec (fastBase 0 49 56) layout0195) scope0184 := by decide

theorem reject03584 : Rejected (base 0 49 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 56) _ validLayout0195) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03584_0) certificate0187

private theorem bind03585_0 : Agrees (spec (fastBase 0 49 57) layout0195) scope0196 := by decide

theorem reject03585 : Rejected (base 0 49 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 57) _ validLayout0195) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind03585_0) certificate0199

private theorem bind03586_0 : Agrees (spec (fastBase 0 49 58) layout0199) scope0236 := by decide

theorem reject03586 : Rejected (base 0 49 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 58) _ validLayout0199) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind03586_0) certificate0239

private theorem bind03587_0 : Agrees (spec (fastBase 0 49 59) layout0195) scope0176 := by decide

theorem reject03587 : Rejected (base 0 49 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 59) _ validLayout0195) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03587_0) certificate0179

private theorem bind03588_0 : Agrees (spec (fastBase 0 49 60) layout0195) scope0194 := by decide

theorem reject03588 : Rejected (base 0 49 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 60) _ validLayout0195) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind03588_0) certificate0197

private theorem bind03589_0 : Agrees (spec (fastBase 0 49 61) layout0196) scope0222 := by decide

theorem reject03589 : Rejected (base 0 49 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 61) _ validLayout0196) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind03589_0) certificate0225

private theorem bind03590_0 : Agrees (spec (fastBase 0 49 62) layout0195) scope0199 := by decide

theorem reject03590 : Rejected (base 0 49 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 62) _ validLayout0195) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind03590_0) certificate0202

private theorem bind03591_0 : Agrees (spec (fastBase 0 49 63) layout0195) scope0194 := by decide

theorem reject03591 : Rejected (base 0 49 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 63) _ validLayout0195) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind03591_0) certificate0197

private theorem bind03592_0 : Agrees (spec (fastBase 0 49 64) layout0196) scope0221 := by decide

theorem reject03592 : Rejected (base 0 49 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 64) _ validLayout0196) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind03592_0) certificate0224

private theorem bind03593_0 : Agrees (spec (fastBase 0 49 65) layout0195) scope0177 := by decide

theorem reject03593 : Rejected (base 0 49 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 65) _ validLayout0195) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03593_0) certificate0180

private theorem bind03594_0 : Agrees (spec (fastBase 0 49 66) layout0196) scope0220 := by decide

theorem reject03594 : Rejected (base 0 49 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0196 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 66) _ validLayout0196) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind03594_0) certificate0223

private theorem bind03595_0 : Agrees (spec (fastBase 0 49 67) layout0199) scope0433 := by decide

theorem reject03595 : Rejected (base 0 49 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0199 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 67) _ validLayout0199) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind03595_0) certificate0460

private theorem bind03596_0 : Agrees (spec (fastBase 0 49 68) layout0195) scope0200 := by decide

theorem reject03596 : Rejected (base 0 49 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 68) _ validLayout0195) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind03596_0) certificate0203

private theorem bind03597_0 : Agrees (spec (fastBase 0 49 69) layout0195) scope0192 := by decide

theorem reject03597 : Rejected (base 0 49 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 69) _ validLayout0195) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind03597_0) certificate0195

private theorem bind03598_0 : Agrees (spec (fastBase 0 49 70) layout0195) scope0176 := by decide

theorem reject03598 : Rejected (base 0 49 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 70) _ validLayout0195) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03598_0) certificate0179

private theorem bind03599_0 : Agrees (spec (fastBase 0 49 71) layout0195) scope0177 := by decide

theorem reject03599 : Rejected (base 0 49 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0195 (layoutValid_of_refines _ _ (base_refines_skeleton 0 49 71) _ validLayout0195) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03599_0) certificate0180

theorem allCases049 : ∀ y : Fin 72, Rejected (base 0 49 y) := by
  intro y
  fin_cases y

  · exact reject03528

  · exact reject03529

  · exact reject03530

  · exact reject03531

  · exact reject03532

  · exact reject03533

  · exact reject03534

  · exact reject03535

  · exact reject03536

  · exact reject03537

  · exact reject03538

  · exact reject03539

  · exact reject03540

  · exact reject03541

  · exact reject03542

  · exact reject03543

  · exact reject03544

  · exact reject03545

  · exact reject03546

  · exact reject03547

  · exact reject03548

  · exact reject03549

  · exact reject03550

  · exact reject03551

  · exact reject03552

  · exact reject03553

  · exact reject03554

  · exact reject03555

  · exact reject03556

  · exact reject03557

  · exact reject03558

  · exact reject03559

  · exact reject03560

  · exact reject03561

  · exact reject03562

  · exact reject03563

  · exact reject03564

  · exact reject03565

  · exact reject03566

  · exact reject03567

  · exact reject03568

  · exact reject03569

  · exact reject03570

  · exact reject03571

  · exact reject03572

  · exact reject03573

  · exact reject03574

  · exact reject03575

  · exact reject03576

  · exact reject03577

  · exact reject03578

  · exact reject03579

  · exact reject03580

  · exact reject03581

  · exact reject03582

  · exact reject03583

  · exact reject03584

  · exact reject03585

  · exact reject03586

  · exact reject03587

  · exact reject03588

  · exact reject03589

  · exact reject03590

  · exact reject03591

  · exact reject03592

  · exact reject03593

  · exact reject03594

  · exact reject03595

  · exact reject03596

  · exact reject03597

  · exact reject03598

  · exact reject03599

end PricingIntegration.RemainingGWitnesses
