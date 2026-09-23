import PricingIntegration.RemainingGLayouts005

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks015

import PricingIntegration.RemainingGScopeChecks016


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00576_0 : Agrees (spec (fastBase 0 8 0) layout0041) scope0239 := by decide

theorem reject00576 : Rejected (base 0 8 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 0) _ validLayout0041) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind00576_0) certificate0242

private theorem bind00577_0 : Agrees (spec (fastBase 0 8 1) layout0041) scope0240 := by decide

theorem reject00577 : Rejected (base 0 8 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 1) _ validLayout0041) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind00577_0) certificate0243

private theorem bind00578_0 : Agrees (spec (fastBase 0 8 2) layout0041) scope0241 := by decide

theorem reject00578 : Rejected (base 0 8 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 2) _ validLayout0041) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind00578_0) certificate0244

private theorem bind00579_0 : Agrees (spec (fastBase 0 8 3) layout0041) scope0242 := by decide

theorem reject00579 : Rejected (base 0 8 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 3) _ validLayout0041) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind00579_0) certificate0245

private theorem bind00580_0 : Agrees (spec (fastBase 0 8 4) layout0041) scope0243 := by decide

theorem reject00580 : Rejected (base 0 8 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 4) _ validLayout0041) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind00580_0) certificate0246

private theorem bind00581_0 : Agrees (spec (fastBase 0 8 5) layout0042) scope0244 := by decide

private theorem bind00581_1 : Agrees (spec (fastBase 0 8 5) layout0043) scope0245 := by decide

theorem reject00581 : Rejected (base 0 8 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0042 layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 5) _ validLayout0042) (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 5) _ validLayout0043) (by decide) (by decide) scope0244 scope0245 (by rw [← fastBase_exact]; exact bind00581_0) (by rw [← fastBase_exact]; exact bind00581_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0247 certificate0248 (by decide)

private theorem bind00582_0 : Agrees (spec (fastBase 0 8 6) layout0041) scope0246 := by decide

theorem reject00582 : Rejected (base 0 8 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 6) _ validLayout0041) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind00582_0) certificate0249

private theorem bind00583_0 : Agrees (spec (fastBase 0 8 7) layout0041) scope0247 := by decide

theorem reject00583 : Rejected (base 0 8 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 7) _ validLayout0041) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind00583_0) certificate0250

private theorem bind00584_0 : Agrees (spec (fastBase 0 8 8) layout0041) scope0248 := by decide

theorem reject00584 : Rejected (base 0 8 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 8) _ validLayout0041) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind00584_0) certificate0251

private theorem bind00585_0 : Agrees (spec (fastBase 0 8 9) layout0042) scope0249 := by decide

private theorem bind00585_1 : Agrees (spec (fastBase 0 8 9) layout0043) scope0250 := by decide

theorem reject00585 : Rejected (base 0 8 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0042 layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 9) _ validLayout0042) (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 9) _ validLayout0043) (by decide) (by decide) scope0249 scope0250 (by rw [← fastBase_exact]; exact bind00585_0) (by rw [← fastBase_exact]; exact bind00585_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0252 certificate0253 (by decide)

private theorem bind00586_0 : Agrees (spec (fastBase 0 8 10) layout0041) scope0251 := by decide

theorem reject00586 : Rejected (base 0 8 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 10) _ validLayout0041) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind00586_0) certificate0254

private theorem bind00587_0 : Agrees (spec (fastBase 0 8 11) layout0041) scope0252 := by decide

theorem reject00587 : Rejected (base 0 8 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 11) _ validLayout0041) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind00587_0) certificate0255

private theorem bind00588_0 : Agrees (spec (fastBase 0 8 12) layout0041) scope0253 := by decide

theorem reject00588 : Rejected (base 0 8 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 12) _ validLayout0041) (by decide) scope0253 (by rw [← fastBase_exact]; exact bind00588_0) certificate0256

private theorem bind00589_0 : Agrees (spec (fastBase 0 8 13) layout0041) scope0241 := by decide

theorem reject00589 : Rejected (base 0 8 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 13) _ validLayout0041) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind00589_0) certificate0244

private theorem bind00590_0 : Agrees (spec (fastBase 0 8 14) layout0041) scope0239 := by decide

theorem reject00590 : Rejected (base 0 8 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 14) _ validLayout0041) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind00590_0) certificate0242

private theorem bind00591_0 : Agrees (spec (fastBase 0 8 15) layout0041) scope0254 := by decide

theorem reject00591 : Rejected (base 0 8 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 15) _ validLayout0041) (by decide) scope0254 (by rw [← fastBase_exact]; exact bind00591_0) certificate0257

private theorem bind00592_0 : Agrees (spec (fastBase 0 8 16) layout0041) scope0248 := by decide

theorem reject00592 : Rejected (base 0 8 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 16) _ validLayout0041) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind00592_0) certificate0251

private theorem bind00593_0 : Agrees (spec (fastBase 0 8 17) layout0041) scope0255 := by decide

theorem reject00593 : Rejected (base 0 8 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 17) _ validLayout0041) (by decide) scope0255 (by rw [← fastBase_exact]; exact bind00593_0) certificate0258

private theorem bind00594_0 : Agrees (spec (fastBase 0 8 18) layout0041) scope0242 := by decide

theorem reject00594 : Rejected (base 0 8 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 18) _ validLayout0041) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind00594_0) certificate0245

private theorem bind00595_0 : Agrees (spec (fastBase 0 8 19) layout0041) scope0243 := by decide

theorem reject00595 : Rejected (base 0 8 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 19) _ validLayout0041) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind00595_0) certificate0246

private theorem bind00596_0 : Agrees (spec (fastBase 0 8 20) layout0041) scope0240 := by decide

theorem reject00596 : Rejected (base 0 8 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 20) _ validLayout0041) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind00596_0) certificate0243

private theorem bind00597_0 : Agrees (spec (fastBase 0 8 21) layout0042) scope0256 := by decide

theorem reject00597 : Rejected (base 0 8 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0042 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 21) _ validLayout0042) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind00597_0) certificate0259

private theorem bind00598_0 : Agrees (spec (fastBase 0 8 22) layout0041) scope0239 := by decide

theorem reject00598 : Rejected (base 0 8 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 22) _ validLayout0041) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind00598_0) certificate0242

private theorem bind00599_0 : Agrees (spec (fastBase 0 8 23) layout0041) scope0243 := by decide

theorem reject00599 : Rejected (base 0 8 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 23) _ validLayout0041) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind00599_0) certificate0246

private theorem bind00600_0 : Agrees (spec (fastBase 0 8 24) layout0041) scope0255 := by decide

theorem reject00600 : Rejected (base 0 8 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 24) _ validLayout0041) (by decide) scope0255 (by rw [← fastBase_exact]; exact bind00600_0) certificate0258

private theorem bind00601_0 : Agrees (spec (fastBase 0 8 25) layout0041) scope0241 := by decide

theorem reject00601 : Rejected (base 0 8 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 25) _ validLayout0041) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind00601_0) certificate0244

private theorem bind00602_0 : Agrees (spec (fastBase 0 8 26) layout0041) scope0257 := by decide

theorem reject00602 : Rejected (base 0 8 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 26) _ validLayout0041) (by decide) scope0257 (by rw [← fastBase_exact]; exact bind00602_0) certificate0260

private theorem bind00603_0 : Agrees (spec (fastBase 0 8 27) layout0041) scope0240 := by decide

theorem reject00603 : Rejected (base 0 8 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 27) _ validLayout0041) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind00603_0) certificate0243

private theorem bind00604_0 : Agrees (spec (fastBase 0 8 28) layout0041) scope0258 := by decide

theorem reject00604 : Rejected (base 0 8 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 28) _ validLayout0041) (by decide) scope0258 (by rw [← fastBase_exact]; exact bind00604_0) certificate0261

private theorem bind00605_0 : Agrees (spec (fastBase 0 8 29) layout0041) scope0242 := by decide

theorem reject00605 : Rejected (base 0 8 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 29) _ validLayout0041) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind00605_0) certificate0245

private theorem bind00606_0 : Agrees (spec (fastBase 0 8 30) layout0041) scope0256 := by decide

theorem reject00606 : Rejected (base 0 8 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 30) _ validLayout0041) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind00606_0) certificate0259

private theorem bind00607_0 : Agrees (spec (fastBase 0 8 31) layout0041) scope0252 := by decide

theorem reject00607 : Rejected (base 0 8 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 31) _ validLayout0041) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind00607_0) certificate0255

private theorem bind00608_0 : Agrees (spec (fastBase 0 8 32) layout0041) scope0240 := by decide

theorem reject00608 : Rejected (base 0 8 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 32) _ validLayout0041) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind00608_0) certificate0243

private theorem bind00609_0 : Agrees (spec (fastBase 0 8 33) layout0041) scope0241 := by decide

theorem reject00609 : Rejected (base 0 8 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 33) _ validLayout0041) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind00609_0) certificate0244

private theorem bind00610_0 : Agrees (spec (fastBase 0 8 34) layout0041) scope0243 := by decide

theorem reject00610 : Rejected (base 0 8 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 34) _ validLayout0041) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind00610_0) certificate0246

private theorem bind00611_0 : Agrees (spec (fastBase 0 8 35) layout0041) scope0253 := by decide

theorem reject00611 : Rejected (base 0 8 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 35) _ validLayout0041) (by decide) scope0253 (by rw [← fastBase_exact]; exact bind00611_0) certificate0256

private theorem bind00612_0 : Agrees (spec (fastBase 0 8 36) layout0041) scope0258 := by decide

theorem reject00612 : Rejected (base 0 8 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 36) _ validLayout0041) (by decide) scope0258 (by rw [← fastBase_exact]; exact bind00612_0) certificate0261

private theorem bind00613_0 : Agrees (spec (fastBase 0 8 37) layout0042) scope0239 := by decide

theorem reject00613 : Rejected (base 0 8 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0042 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 37) _ validLayout0042) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind00613_0) certificate0242

private theorem bind00614_0 : Agrees (spec (fastBase 0 8 38) layout0042) scope0243 := by decide

theorem reject00614 : Rejected (base 0 8 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0042 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 38) _ validLayout0042) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind00614_0) certificate0246

private theorem bind00615_0 : Agrees (spec (fastBase 0 8 39) layout0042) scope0244 := by decide

private theorem bind00615_1 : Agrees (spec (fastBase 0 8 39) layout0043) scope0245 := by decide

theorem reject00615 : Rejected (base 0 8 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0042 layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 39) _ validLayout0042) (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 39) _ validLayout0043) (by decide) (by decide) scope0244 scope0245 (by rw [← fastBase_exact]; exact bind00615_0) (by rw [← fastBase_exact]; exact bind00615_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0247 certificate0248 (by decide)

private theorem bind00616_0 : Agrees (spec (fastBase 0 8 40) layout0042) scope0244 := by decide

private theorem bind00616_1 : Agrees (spec (fastBase 0 8 40) layout0043) scope0250 := by decide

theorem reject00616 : Rejected (base 0 8 40) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0042 layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 40) _ validLayout0042) (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 40) _ validLayout0043) (by decide) (by decide) scope0244 scope0250 (by rw [← fastBase_exact]; exact bind00616_0) (by rw [← fastBase_exact]; exact bind00616_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0247 certificate0253 (by decide)

private theorem bind00617_0 : Agrees (spec (fastBase 0 8 41) layout0043) scope0259 := by decide

theorem reject00617 : Rejected (base 0 8 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 41) _ validLayout0043) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind00617_0) certificate0262

private theorem bind00618_0 : Agrees (spec (fastBase 0 8 42) layout0041) scope0246 := by decide

theorem reject00618 : Rejected (base 0 8 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 42) _ validLayout0041) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind00618_0) certificate0249

private theorem bind00619_0 : Agrees (spec (fastBase 0 8 43) layout0041) scope0246 := by decide

theorem reject00619 : Rejected (base 0 8 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 43) _ validLayout0041) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind00619_0) certificate0249

private theorem bind00620_0 : Agrees (spec (fastBase 0 8 44) layout0041) scope0246 := by decide

theorem reject00620 : Rejected (base 0 8 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 44) _ validLayout0041) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind00620_0) certificate0249

private theorem bind00621_0 : Agrees (spec (fastBase 0 8 45) layout0041) scope0246 := by decide

theorem reject00621 : Rejected (base 0 8 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 45) _ validLayout0041) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind00621_0) certificate0249

private theorem bind00622_0 : Agrees (spec (fastBase 0 8 46) layout0041) scope0246 := by decide

theorem reject00622 : Rejected (base 0 8 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 46) _ validLayout0041) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind00622_0) certificate0249

private theorem bind00623_0 : Agrees (spec (fastBase 0 8 47) layout0043) scope0260 := by decide

theorem reject00623 : Rejected (base 0 8 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 47) _ validLayout0043) (by decide) scope0260 (by rw [← fastBase_exact]; exact bind00623_0) certificate0263

private theorem bind00624_0 : Agrees (spec (fastBase 0 8 48) layout0041) scope0261 := by decide

theorem reject00624 : Rejected (base 0 8 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 48) _ validLayout0041) (by decide) scope0261 (by rw [← fastBase_exact]; exact bind00624_0) certificate0264

private theorem bind00625_0 : Agrees (spec (fastBase 0 8 49) layout0041) scope0247 := by decide

theorem reject00625 : Rejected (base 0 8 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 49) _ validLayout0041) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind00625_0) certificate0250

private theorem bind00626_0 : Agrees (spec (fastBase 0 8 50) layout0042) scope0249 := by decide

private theorem bind00626_1 : Agrees (spec (fastBase 0 8 50) layout0043) scope0250 := by decide

theorem reject00626 : Rejected (base 0 8 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0042 layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 50) _ validLayout0042) (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 50) _ validLayout0043) (by decide) (by decide) scope0249 scope0250 (by rw [← fastBase_exact]; exact bind00626_0) (by rw [← fastBase_exact]; exact bind00626_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0252 certificate0253 (by decide)

private theorem bind00627_0 : Agrees (spec (fastBase 0 8 51) layout0041) scope0251 := by decide

theorem reject00627 : Rejected (base 0 8 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 51) _ validLayout0041) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind00627_0) certificate0254

private theorem bind00628_0 : Agrees (spec (fastBase 0 8 52) layout0041) scope0239 := by decide

theorem reject00628 : Rejected (base 0 8 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 52) _ validLayout0041) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind00628_0) certificate0242

private theorem bind00629_0 : Agrees (spec (fastBase 0 8 53) layout0041) scope0257 := by decide

theorem reject00629 : Rejected (base 0 8 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 53) _ validLayout0041) (by decide) scope0257 (by rw [← fastBase_exact]; exact bind00629_0) certificate0260

private theorem bind00630_0 : Agrees (spec (fastBase 0 8 54) layout0041) scope0248 := by decide

theorem reject00630 : Rejected (base 0 8 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 54) _ validLayout0041) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind00630_0) certificate0251

private theorem bind00631_0 : Agrees (spec (fastBase 0 8 55) layout0042) scope0262 := by decide

theorem reject00631 : Rejected (base 0 8 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0042 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 55) _ validLayout0042) (by decide) scope0262 (by rw [← fastBase_exact]; exact bind00631_0) certificate0265

private theorem bind00632_0 : Agrees (spec (fastBase 0 8 56) layout0041) scope0251 := by decide

theorem reject00632 : Rejected (base 0 8 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 56) _ validLayout0041) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind00632_0) certificate0254

private theorem bind00633_0 : Agrees (spec (fastBase 0 8 57) layout0041) scope0256 := by decide

theorem reject00633 : Rejected (base 0 8 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 57) _ validLayout0041) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind00633_0) certificate0259

private theorem bind00634_0 : Agrees (spec (fastBase 0 8 58) layout0042) scope0249 := by decide

private theorem bind00634_1 : Agrees (spec (fastBase 0 8 58) layout0043) scope0245 := by decide

theorem reject00634 : Rejected (base 0 8 58) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0042 layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 58) _ validLayout0042) (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 58) _ validLayout0043) (by decide) (by decide) scope0249 scope0245 (by rw [← fastBase_exact]; exact bind00634_0) (by rw [← fastBase_exact]; exact bind00634_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0252 certificate0248 (by decide)

private theorem bind00635_0 : Agrees (spec (fastBase 0 8 59) layout0041) scope0262 := by decide

theorem reject00635 : Rejected (base 0 8 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 59) _ validLayout0041) (by decide) scope0262 (by rw [← fastBase_exact]; exact bind00635_0) certificate0265

private theorem bind00636_0 : Agrees (spec (fastBase 0 8 60) layout0041) scope0247 := by decide

theorem reject00636 : Rejected (base 0 8 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 60) _ validLayout0041) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind00636_0) certificate0250

private theorem bind00637_0 : Agrees (spec (fastBase 0 8 61) layout0041) scope0252 := by decide

theorem reject00637 : Rejected (base 0 8 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 61) _ validLayout0041) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind00637_0) certificate0255

private theorem bind00638_0 : Agrees (spec (fastBase 0 8 62) layout0041) scope0254 := by decide

theorem reject00638 : Rejected (base 0 8 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 62) _ validLayout0041) (by decide) scope0254 (by rw [← fastBase_exact]; exact bind00638_0) certificate0257

private theorem bind00639_0 : Agrees (spec (fastBase 0 8 63) layout0041) scope0251 := by decide

theorem reject00639 : Rejected (base 0 8 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 63) _ validLayout0041) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind00639_0) certificate0254

private theorem bind00640_0 : Agrees (spec (fastBase 0 8 64) layout0041) scope0247 := by decide

theorem reject00640 : Rejected (base 0 8 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 64) _ validLayout0041) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind00640_0) certificate0250

private theorem bind00641_0 : Agrees (spec (fastBase 0 8 65) layout0041) scope0248 := by decide

theorem reject00641 : Rejected (base 0 8 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 65) _ validLayout0041) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind00641_0) certificate0251

private theorem bind00642_0 : Agrees (spec (fastBase 0 8 66) layout0041) scope0262 := by decide

theorem reject00642 : Rejected (base 0 8 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 66) _ validLayout0041) (by decide) scope0262 (by rw [← fastBase_exact]; exact bind00642_0) certificate0265

private theorem bind00643_0 : Agrees (spec (fastBase 0 8 67) layout0041) scope0242 := by decide

theorem reject00643 : Rejected (base 0 8 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 67) _ validLayout0041) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind00643_0) certificate0245

private theorem bind00644_0 : Agrees (spec (fastBase 0 8 68) layout0043) scope0263 := by decide

theorem reject00644 : Rejected (base 0 8 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 68) _ validLayout0043) (by decide) scope0263 (by rw [← fastBase_exact]; exact bind00644_0) certificate0266

private theorem bind00645_0 : Agrees (spec (fastBase 0 8 69) layout0041) scope0252 := by decide

theorem reject00645 : Rejected (base 0 8 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 69) _ validLayout0041) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind00645_0) certificate0255

private theorem bind00646_0 : Agrees (spec (fastBase 0 8 70) layout0043) scope0264 := by decide

theorem reject00646 : Rejected (base 0 8 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0043 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 70) _ validLayout0043) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind00646_0) certificate0267

private theorem bind00647_0 : Agrees (spec (fastBase 0 8 71) layout0041) scope0261 := by decide

theorem reject00647 : Rejected (base 0 8 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0041 (layoutValid_of_refines _ _ (base_refines_skeleton 0 8 71) _ validLayout0041) (by decide) scope0261 (by rw [← fastBase_exact]; exact bind00647_0) certificate0264

theorem allCases008 : ∀ y : Fin 72, Rejected (base 0 8 y) := by
  intro y
  fin_cases y

  · exact reject00576

  · exact reject00577

  · exact reject00578

  · exact reject00579

  · exact reject00580

  · exact reject00581

  · exact reject00582

  · exact reject00583

  · exact reject00584

  · exact reject00585

  · exact reject00586

  · exact reject00587

  · exact reject00588

  · exact reject00589

  · exact reject00590

  · exact reject00591

  · exact reject00592

  · exact reject00593

  · exact reject00594

  · exact reject00595

  · exact reject00596

  · exact reject00597

  · exact reject00598

  · exact reject00599

  · exact reject00600

  · exact reject00601

  · exact reject00602

  · exact reject00603

  · exact reject00604

  · exact reject00605

  · exact reject00606

  · exact reject00607

  · exact reject00608

  · exact reject00609

  · exact reject00610

  · exact reject00611

  · exact reject00612

  · exact reject00613

  · exact reject00614

  · exact reject00615

  · exact reject00616

  · exact reject00617

  · exact reject00618

  · exact reject00619

  · exact reject00620

  · exact reject00621

  · exact reject00622

  · exact reject00623

  · exact reject00624

  · exact reject00625

  · exact reject00626

  · exact reject00627

  · exact reject00628

  · exact reject00629

  · exact reject00630

  · exact reject00631

  · exact reject00632

  · exact reject00633

  · exact reject00634

  · exact reject00635

  · exact reject00636

  · exact reject00637

  · exact reject00638

  · exact reject00639

  · exact reject00640

  · exact reject00641

  · exact reject00642

  · exact reject00643

  · exact reject00644

  · exact reject00645

  · exact reject00646

  · exact reject00647

end PricingIntegration.RemainingGWitnesses
