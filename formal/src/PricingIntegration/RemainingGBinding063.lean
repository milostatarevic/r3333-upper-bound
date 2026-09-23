import PricingIntegration.RemainingGLayouts030

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks019

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks031


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind04536_0 : Agrees (spec (fastBase 0 63 0) layout0241) scope0144 := by decide

theorem reject04536 : Rejected (base 0 63 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 0) _ validLayout0241) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04536_0) certificate0147

private theorem bind04537_0 : Agrees (spec (fastBase 0 63 1) layout0241) scope0155 := by decide

theorem reject04537 : Rejected (base 0 63 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 1) _ validLayout0241) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04537_0) certificate0158

private theorem bind04538_0 : Agrees (spec (fastBase 0 63 2) layout0241) scope0150 := by decide

theorem reject04538 : Rejected (base 0 63 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 2) _ validLayout0241) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04538_0) certificate0153

private theorem bind04539_0 : Agrees (spec (fastBase 0 63 3) layout0242) scope0295 := by decide

theorem reject04539 : Rejected (base 0 63 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 3) _ validLayout0242) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind04539_0) certificate0300

private theorem bind04540_0 : Agrees (spec (fastBase 0 63 4) layout0242) scope0296 := by decide

theorem reject04540 : Rejected (base 0 63 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 4) _ validLayout0242) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind04540_0) certificate0301

private theorem bind04541_0 : Agrees (spec (fastBase 0 63 5) layout0241) scope0141 := by decide

theorem reject04541 : Rejected (base 0 63 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 5) _ validLayout0241) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04541_0) certificate0144

private theorem bind04542_0 : Agrees (spec (fastBase 0 63 6) layout0242) scope0322 := by decide

private theorem bind04542_1 : Agrees (spec (fastBase 0 63 6) layout0243) scope0301 := by decide

theorem reject04542 : Rejected (base 0 63 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0242 layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 6) _ validLayout0242) (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 6) _ validLayout0243) (by decide) (by decide) scope0322 scope0301 (by rw [← fastBase_exact]; exact bind04542_0) (by rw [← fastBase_exact]; exact bind04542_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0328 certificate0329 (by decide)

private theorem bind04543_0 : Agrees (spec (fastBase 0 63 7) layout0241) scope0140 := by decide

theorem reject04543 : Rejected (base 0 63 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 7) _ validLayout0241) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04543_0) certificate0143

private theorem bind04544_0 : Agrees (spec (fastBase 0 63 8) layout0241) scope0145 := by decide

theorem reject04544 : Rejected (base 0 63 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 8) _ validLayout0241) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04544_0) certificate0148

private theorem bind04545_0 : Agrees (spec (fastBase 0 63 9) layout0242) scope0302 := by decide

theorem reject04545 : Rejected (base 0 63 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 9) _ validLayout0242) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind04545_0) certificate0307

private theorem bind04546_0 : Agrees (spec (fastBase 0 63 10) layout0242) scope0303 := by decide

theorem reject04546 : Rejected (base 0 63 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 10) _ validLayout0242) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind04546_0) certificate0308

private theorem bind04547_0 : Agrees (spec (fastBase 0 63 11) layout0242) scope0300 := by decide

private theorem bind04547_1 : Agrees (spec (fastBase 0 63 11) layout0243) scope0306 := by decide

theorem reject04547 : Rejected (base 0 63 11) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0242 layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 11) _ validLayout0242) (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 11) _ validLayout0243) (by decide) (by decide) scope0300 scope0306 (by rw [← fastBase_exact]; exact bind04547_0) (by rw [← fastBase_exact]; exact bind04547_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0322 (by decide)

private theorem bind04548_0 : Agrees (spec (fastBase 0 63 12) layout0241) scope0144 := by decide

theorem reject04548 : Rejected (base 0 63 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 12) _ validLayout0241) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04548_0) certificate0147

private theorem bind04549_0 : Agrees (spec (fastBase 0 63 13) layout0241) scope0144 := by decide

theorem reject04549 : Rejected (base 0 63 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 13) _ validLayout0241) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04549_0) certificate0147

private theorem bind04550_0 : Agrees (spec (fastBase 0 63 14) layout0241) scope0144 := by decide

theorem reject04550 : Rejected (base 0 63 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 14) _ validLayout0241) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04550_0) certificate0147

private theorem bind04551_0 : Agrees (spec (fastBase 0 63 15) layout0241) scope0144 := by decide

theorem reject04551 : Rejected (base 0 63 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 15) _ validLayout0241) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04551_0) certificate0147

private theorem bind04552_0 : Agrees (spec (fastBase 0 63 16) layout0241) scope0144 := by decide

theorem reject04552 : Rejected (base 0 63 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 16) _ validLayout0241) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04552_0) certificate0147

private theorem bind04553_0 : Agrees (spec (fastBase 0 63 17) layout0241) scope0155 := by decide

theorem reject04553 : Rejected (base 0 63 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 17) _ validLayout0241) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04553_0) certificate0158

private theorem bind04554_0 : Agrees (spec (fastBase 0 63 18) layout0242) scope0297 := by decide

theorem reject04554 : Rejected (base 0 63 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 18) _ validLayout0242) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind04554_0) certificate0302

private theorem bind04555_0 : Agrees (spec (fastBase 0 63 19) layout0241) scope0171 := by decide

theorem reject04555 : Rejected (base 0 63 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 19) _ validLayout0241) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind04555_0) certificate0174

private theorem bind04556_0 : Agrees (spec (fastBase 0 63 20) layout0243) scope0414 := by decide

theorem reject04556 : Rejected (base 0 63 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 20) _ validLayout0243) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind04556_0) certificate0436

private theorem bind04557_0 : Agrees (spec (fastBase 0 63 21) layout0241) scope0160 := by decide

theorem reject04557 : Rejected (base 0 63 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 21) _ validLayout0241) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind04557_0) certificate0163

private theorem bind04558_0 : Agrees (spec (fastBase 0 63 22) layout0241) scope0150 := by decide

theorem reject04558 : Rejected (base 0 63 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 22) _ validLayout0241) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04558_0) certificate0153

private theorem bind04559_0 : Agrees (spec (fastBase 0 63 23) layout0242) scope0296 := by decide

theorem reject04559 : Rejected (base 0 63 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 23) _ validLayout0242) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind04559_0) certificate0301

private theorem bind04560_0 : Agrees (spec (fastBase 0 63 24) layout0242) scope0295 := by decide

theorem reject04560 : Rejected (base 0 63 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 24) _ validLayout0242) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind04560_0) certificate0300

private theorem bind04561_0 : Agrees (spec (fastBase 0 63 25) layout0241) scope0171 := by decide

theorem reject04561 : Rejected (base 0 63 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 25) _ validLayout0241) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind04561_0) certificate0174

private theorem bind04562_0 : Agrees (spec (fastBase 0 63 26) layout0241) scope0163 := by decide

theorem reject04562 : Rejected (base 0 63 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 26) _ validLayout0241) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind04562_0) certificate0166

private theorem bind04563_0 : Agrees (spec (fastBase 0 63 27) layout0241) scope0155 := by decide

theorem reject04563 : Rejected (base 0 63 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 27) _ validLayout0241) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04563_0) certificate0158

private theorem bind04564_0 : Agrees (spec (fastBase 0 63 28) layout0241) scope0150 := by decide

theorem reject04564 : Rejected (base 0 63 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 28) _ validLayout0241) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04564_0) certificate0153

private theorem bind04565_0 : Agrees (spec (fastBase 0 63 29) layout0241) scope0168 := by decide

theorem reject04565 : Rejected (base 0 63 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 29) _ validLayout0241) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind04565_0) certificate0171

private theorem bind04566_0 : Agrees (spec (fastBase 0 63 30) layout0241) scope0167 := by decide

theorem reject04566 : Rejected (base 0 63 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 30) _ validLayout0241) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind04566_0) certificate0170

private theorem bind04567_0 : Agrees (spec (fastBase 0 63 31) layout0243) scope0315 := by decide

theorem reject04567 : Rejected (base 0 63 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 31) _ validLayout0243) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind04567_0) certificate0320

private theorem bind04568_0 : Agrees (spec (fastBase 0 63 32) layout0241) scope0168 := by decide

theorem reject04568 : Rejected (base 0 63 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 32) _ validLayout0241) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind04568_0) certificate0171

private theorem bind04569_0 : Agrees (spec (fastBase 0 63 33) layout0241) scope0150 := by decide

theorem reject04569 : Rejected (base 0 63 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 33) _ validLayout0241) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04569_0) certificate0153

private theorem bind04570_0 : Agrees (spec (fastBase 0 63 34) layout0241) scope0141 := by decide

theorem reject04570 : Rejected (base 0 63 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 34) _ validLayout0241) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04570_0) certificate0144

private theorem bind04571_0 : Agrees (spec (fastBase 0 63 35) layout0241) scope0157 := by decide

theorem reject04571 : Rejected (base 0 63 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 35) _ validLayout0241) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind04571_0) certificate0160

private theorem bind04572_0 : Agrees (spec (fastBase 0 63 36) layout0242) scope0300 := by decide

private theorem bind04572_1 : Agrees (spec (fastBase 0 63 36) layout0243) scope0469 := by decide

theorem reject04572 : Rejected (base 0 63 36) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0242 layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 36) _ validLayout0242) (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 36) _ validLayout0243) (by decide) (by decide) scope0300 scope0469 (by rw [← fastBase_exact]; exact bind04572_0) (by rw [← fastBase_exact]; exact bind04572_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0505 certificate0506 (by decide)

private theorem bind04573_0 : Agrees (spec (fastBase 0 63 37) layout0241) scope0141 := by decide

theorem reject04573 : Rejected (base 0 63 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 37) _ validLayout0241) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04573_0) certificate0144

private theorem bind04574_0 : Agrees (spec (fastBase 0 63 38) layout0242) scope0294 := by decide

theorem reject04574 : Rejected (base 0 63 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 38) _ validLayout0242) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind04574_0) certificate0299

private theorem bind04575_0 : Agrees (spec (fastBase 0 63 39) layout0241) scope0163 := by decide

theorem reject04575 : Rejected (base 0 63 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 39) _ validLayout0241) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind04575_0) certificate0166

private theorem bind04576_0 : Agrees (spec (fastBase 0 63 40) layout0241) scope0162 := by decide

theorem reject04576 : Rejected (base 0 63 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 40) _ validLayout0241) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind04576_0) certificate0165

private theorem bind04577_0 : Agrees (spec (fastBase 0 63 41) layout0242) scope0303 := by decide

theorem reject04577 : Rejected (base 0 63 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 41) _ validLayout0242) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind04577_0) certificate0308

private theorem bind04578_0 : Agrees (spec (fastBase 0 63 42) layout0241) scope0155 := by decide

theorem reject04578 : Rejected (base 0 63 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 42) _ validLayout0241) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04578_0) certificate0158

private theorem bind04579_0 : Agrees (spec (fastBase 0 63 43) layout0241) scope0167 := by decide

theorem reject04579 : Rejected (base 0 63 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 43) _ validLayout0241) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind04579_0) certificate0170

private theorem bind04580_0 : Agrees (spec (fastBase 0 63 44) layout0241) scope0165 := by decide

theorem reject04580 : Rejected (base 0 63 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 44) _ validLayout0241) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind04580_0) certificate0168

private theorem bind04581_0 : Agrees (spec (fastBase 0 63 45) layout0241) scope0140 := by decide

theorem reject04581 : Rejected (base 0 63 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 45) _ validLayout0241) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04581_0) certificate0143

private theorem bind04582_0 : Agrees (spec (fastBase 0 63 46) layout0244) scope0470 := by decide

private theorem bind04582_1 : Agrees (spec (fastBase 0 63 46) layout0245) scope0307 := by decide

theorem reject04582 : Rejected (base 0 63 46) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0244 layout0245 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 46) _ validLayout0244) (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 46) _ validLayout0245) (by decide) (by decide) scope0470 scope0307 (by rw [← fastBase_exact]; exact bind04582_0) (by rw [← fastBase_exact]; exact bind04582_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0507 certificate0508 (by decide)

private theorem bind04583_0 : Agrees (spec (fastBase 0 63 47) layout0241) scope0140 := by decide

theorem reject04583 : Rejected (base 0 63 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 47) _ validLayout0241) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04583_0) certificate0143

private theorem bind04584_0 : Agrees (spec (fastBase 0 63 48) layout0241) scope0160 := by decide

theorem reject04584 : Rejected (base 0 63 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 48) _ validLayout0241) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind04584_0) certificate0163

private theorem bind04585_0 : Agrees (spec (fastBase 0 63 49) layout0242) scope0304 := by decide

theorem reject04585 : Rejected (base 0 63 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 49) _ validLayout0242) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind04585_0) certificate0309

private theorem bind04586_0 : Agrees (spec (fastBase 0 63 50) layout0242) scope0302 := by decide

theorem reject04586 : Rejected (base 0 63 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 50) _ validLayout0242) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind04586_0) certificate0307

private theorem bind04587_0 : Agrees (spec (fastBase 0 63 51) layout0241) scope0158 := by decide

theorem reject04587 : Rejected (base 0 63 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 51) _ validLayout0241) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind04587_0) certificate0161

private theorem bind04588_0 : Agrees (spec (fastBase 0 63 52) layout0241) scope0145 := by decide

theorem reject04588 : Rejected (base 0 63 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 52) _ validLayout0241) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04588_0) certificate0148

private theorem bind04589_0 : Agrees (spec (fastBase 0 63 53) layout0241) scope0162 := by decide

theorem reject04589 : Rejected (base 0 63 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 53) _ validLayout0241) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind04589_0) certificate0165

private theorem bind04590_0 : Agrees (spec (fastBase 0 63 54) layout0241) scope0158 := by decide

theorem reject04590 : Rejected (base 0 63 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 54) _ validLayout0241) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind04590_0) certificate0161

private theorem bind04591_0 : Agrees (spec (fastBase 0 63 55) layout0242) scope0302 := by decide

theorem reject04591 : Rejected (base 0 63 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 55) _ validLayout0242) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind04591_0) certificate0307

private theorem bind04592_0 : Agrees (spec (fastBase 0 63 56) layout0242) scope0305 := by decide

theorem reject04592 : Rejected (base 0 63 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 56) _ validLayout0242) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind04592_0) certificate0310

private theorem bind04593_0 : Agrees (spec (fastBase 0 63 57) layout0241) scope0165 := by decide

theorem reject04593 : Rejected (base 0 63 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 57) _ validLayout0241) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind04593_0) certificate0168

private theorem bind04594_0 : Agrees (spec (fastBase 0 63 58) layout0241) scope0156 := by decide

theorem reject04594 : Rejected (base 0 63 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 58) _ validLayout0241) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind04594_0) certificate0159

private theorem bind04595_0 : Agrees (spec (fastBase 0 63 59) layout0241) scope0145 := by decide

theorem reject04595 : Rejected (base 0 63 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 59) _ validLayout0241) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04595_0) certificate0148

private theorem bind04596_0 : Agrees (spec (fastBase 0 63 60) layout0241) scope0140 := by decide

theorem reject04596 : Rejected (base 0 63 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 60) _ validLayout0241) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04596_0) certificate0143

private theorem bind04597_0 : Agrees (spec (fastBase 0 63 61) layout0242) scope0302 := by decide

theorem reject04597 : Rejected (base 0 63 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 61) _ validLayout0242) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind04597_0) certificate0307

private theorem bind04598_0 : Agrees (spec (fastBase 0 63 62) layout0241) scope0157 := by decide

theorem reject04598 : Rejected (base 0 63 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 62) _ validLayout0241) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind04598_0) certificate0160

private theorem bind04599_0 : Agrees (spec (fastBase 0 63 63) layout0241) scope0141 := by decide

theorem reject04599 : Rejected (base 0 63 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 63) _ validLayout0241) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04599_0) certificate0144

private theorem bind04600_0 : Agrees (spec (fastBase 0 63 64) layout0241) scope0156 := by decide

theorem reject04600 : Rejected (base 0 63 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 64) _ validLayout0241) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind04600_0) certificate0159

private theorem bind04601_0 : Agrees (spec (fastBase 0 63 65) layout0241) scope0145 := by decide

theorem reject04601 : Rejected (base 0 63 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0241 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 65) _ validLayout0241) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04601_0) certificate0148

private theorem bind04602_0 : Agrees (spec (fastBase 0 63 66) layout0242) scope0303 := by decide

theorem reject04602 : Rejected (base 0 63 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 66) _ validLayout0242) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind04602_0) certificate0308

private theorem bind04603_0 : Agrees (spec (fastBase 0 63 67) layout0242) scope0295 := by decide

theorem reject04603 : Rejected (base 0 63 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 67) _ validLayout0242) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind04603_0) certificate0300

private theorem bind04604_0 : Agrees (spec (fastBase 0 63 68) layout0242) scope0296 := by decide

theorem reject04604 : Rejected (base 0 63 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0242 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 68) _ validLayout0242) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind04604_0) certificate0301

private theorem bind04605_0 : Agrees (spec (fastBase 0 63 69) layout0242) scope0300 := by decide

private theorem bind04605_1 : Agrees (spec (fastBase 0 63 69) layout0243) scope0301 := by decide

theorem reject04605 : Rejected (base 0 63 69) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0242 layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 69) _ validLayout0242) (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 69) _ validLayout0243) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind04605_0) (by rw [← fastBase_exact]; exact bind04605_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind04606_0 : Agrees (spec (fastBase 0 63 70) layout0243) scope0415 := by decide

theorem reject04606 : Rejected (base 0 63 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 70) _ validLayout0243) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind04606_0) certificate0438

private theorem bind04607_0 : Agrees (spec (fastBase 0 63 71) layout0243) scope0471 := by decide

theorem reject04607 : Rejected (base 0 63 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0243 (layoutValid_of_refines _ _ (base_refines_skeleton 0 63 71) _ validLayout0243) (by decide) scope0471 (by rw [← fastBase_exact]; exact bind04607_0) certificate0509

theorem allCases063 : ∀ y : Fin 72, Rejected (base 0 63 y) := by
  intro y
  fin_cases y

  · exact reject04536

  · exact reject04537

  · exact reject04538

  · exact reject04539

  · exact reject04540

  · exact reject04541

  · exact reject04542

  · exact reject04543

  · exact reject04544

  · exact reject04545

  · exact reject04546

  · exact reject04547

  · exact reject04548

  · exact reject04549

  · exact reject04550

  · exact reject04551

  · exact reject04552

  · exact reject04553

  · exact reject04554

  · exact reject04555

  · exact reject04556

  · exact reject04557

  · exact reject04558

  · exact reject04559

  · exact reject04560

  · exact reject04561

  · exact reject04562

  · exact reject04563

  · exact reject04564

  · exact reject04565

  · exact reject04566

  · exact reject04567

  · exact reject04568

  · exact reject04569

  · exact reject04570

  · exact reject04571

  · exact reject04572

  · exact reject04573

  · exact reject04574

  · exact reject04575

  · exact reject04576

  · exact reject04577

  · exact reject04578

  · exact reject04579

  · exact reject04580

  · exact reject04581

  · exact reject04582

  · exact reject04583

  · exact reject04584

  · exact reject04585

  · exact reject04586

  · exact reject04587

  · exact reject04588

  · exact reject04589

  · exact reject04590

  · exact reject04591

  · exact reject04592

  · exact reject04593

  · exact reject04594

  · exact reject04595

  · exact reject04596

  · exact reject04597

  · exact reject04598

  · exact reject04599

  · exact reject04600

  · exact reject04601

  · exact reject04602

  · exact reject04603

  · exact reject04604

  · exact reject04605

  · exact reject04606

  · exact reject04607

end PricingIntegration.RemainingGWitnesses
