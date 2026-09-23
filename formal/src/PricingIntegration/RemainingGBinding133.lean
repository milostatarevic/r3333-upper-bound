import PricingIntegration.RemainingGLayouts029

import PricingIntegration.RemainingGLayouts035

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks017

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks030

import PricingIntegration.RemainingGScopeChecks031

import PricingIntegration.RemainingGScopeChecks038

import PricingIntegration.RemainingGScopeChecks039


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind09576_0 : Agrees (spec (fastBase 1 61 0) layout0237) scope0291 := by decide

theorem reject09576 : Rejected (base 1 61 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 0) _ validLayout0237) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind09576_0) certificate0294

private theorem bind09577_0 : Agrees (spec (fastBase 1 61 1) layout0237) scope0459 := by decide

theorem reject09577 : Rejected (base 1 61 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 1) _ validLayout0237) (by decide) scope0459 (by rw [← fastBase_exact]; exact bind09577_0) certificate0495

private theorem bind09578_0 : Agrees (spec (fastBase 1 61 2) layout0237) scope0464 := by decide

theorem reject09578 : Rejected (base 1 61 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 2) _ validLayout0237) (by decide) scope0464 (by rw [← fastBase_exact]; exact bind09578_0) certificate0500

private theorem bind09579_0 : Agrees (spec (fastBase 1 61 3) layout0237) scope0577 := by decide

theorem reject09579 : Rejected (base 1 61 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 3) _ validLayout0237) (by decide) scope0577 (by rw [← fastBase_exact]; exact bind09579_0) certificate0620

private theorem bind09580_0 : Agrees (spec (fastBase 1 61 4) layout0237) scope0575 := by decide

theorem reject09580 : Rejected (base 1 61 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 4) _ validLayout0237) (by decide) scope0575 (by rw [← fastBase_exact]; exact bind09580_0) certificate0618

private theorem bind09581_0 : Agrees (spec (fastBase 1 61 5) layout0236) scope0265 := by decide

theorem reject09581 : Rejected (base 1 61 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 5) _ validLayout0236) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind09581_0) certificate0268

private theorem bind09582_0 : Agrees (spec (fastBase 1 61 6) layout0237) scope0574 := by decide

theorem reject09582 : Rejected (base 1 61 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 6) _ validLayout0237) (by decide) scope0574 (by rw [← fastBase_exact]; exact bind09582_0) certificate0617

private theorem bind09583_0 : Agrees (spec (fastBase 1 61 7) layout0237) scope0460 := by decide

theorem reject09583 : Rejected (base 1 61 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 7) _ validLayout0237) (by decide) scope0460 (by rw [← fastBase_exact]; exact bind09583_0) certificate0496

private theorem bind09584_0 : Agrees (spec (fastBase 1 61 8) layout0237) scope0288 := by decide

theorem reject09584 : Rejected (base 1 61 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 8) _ validLayout0237) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09584_0) certificate0291

private theorem bind09585_0 : Agrees (spec (fastBase 1 61 9) layout0236) scope0272 := by decide

private theorem bind09585_1 : Agrees (spec (fastBase 1 61 9) layout0286) scope0273 := by decide

theorem reject09585 : Rejected (base 1 61 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0236 layout0286 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 9) _ validLayout0236) (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 9) _ validLayout0286) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind09585_0) (by rw [← fastBase_exact]; exact bind09585_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind09586_0 : Agrees (spec (fastBase 1 61 10) layout0237) scope0576 := by decide

theorem reject09586 : Rejected (base 1 61 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 10) _ validLayout0237) (by decide) scope0576 (by rw [← fastBase_exact]; exact bind09586_0) certificate0619

private theorem bind09587_0 : Agrees (spec (fastBase 1 61 11) layout0237) scope0289 := by decide

theorem reject09587 : Rejected (base 1 61 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 11) _ validLayout0237) (by decide) scope0289 (by rw [← fastBase_exact]; exact bind09587_0) certificate0292

private theorem bind09588_0 : Agrees (spec (fastBase 1 61 12) layout0237) scope0459 := by decide

theorem reject09588 : Rejected (base 1 61 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 12) _ validLayout0237) (by decide) scope0459 (by rw [← fastBase_exact]; exact bind09588_0) certificate0495

private theorem bind09589_0 : Agrees (spec (fastBase 1 61 13) layout0237) scope0291 := by decide

theorem reject09589 : Rejected (base 1 61 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 13) _ validLayout0237) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind09589_0) certificate0294

private theorem bind09590_0 : Agrees (spec (fastBase 1 61 14) layout0236) scope0270 := by decide

theorem reject09590 : Rejected (base 1 61 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 14) _ validLayout0236) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind09590_0) certificate0273

private theorem bind09591_0 : Agrees (spec (fastBase 1 61 15) layout0236) scope0281 := by decide

theorem reject09591 : Rejected (base 1 61 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 15) _ validLayout0236) (by decide) scope0281 (by rw [← fastBase_exact]; exact bind09591_0) certificate0284

private theorem bind09592_0 : Agrees (spec (fastBase 1 61 16) layout0237) scope0580 := by decide

theorem reject09592 : Rejected (base 1 61 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 16) _ validLayout0237) (by decide) scope0580 (by rw [← fastBase_exact]; exact bind09592_0) certificate0623

private theorem bind09593_0 : Agrees (spec (fastBase 1 61 17) layout0237) scope0291 := by decide

theorem reject09593 : Rejected (base 1 61 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 17) _ validLayout0237) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind09593_0) certificate0294

private theorem bind09594_0 : Agrees (spec (fastBase 1 61 18) layout0237) scope0577 := by decide

theorem reject09594 : Rejected (base 1 61 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 18) _ validLayout0237) (by decide) scope0577 (by rw [← fastBase_exact]; exact bind09594_0) certificate0620

private theorem bind09595_0 : Agrees (spec (fastBase 1 61 19) layout0237) scope0463 := by decide

theorem reject09595 : Rejected (base 1 61 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 19) _ validLayout0237) (by decide) scope0463 (by rw [← fastBase_exact]; exact bind09595_0) certificate0499

private theorem bind09596_0 : Agrees (spec (fastBase 1 61 20) layout0237) scope0462 := by decide

theorem reject09596 : Rejected (base 1 61 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 20) _ validLayout0237) (by decide) scope0462 (by rw [← fastBase_exact]; exact bind09596_0) certificate0498

private theorem bind09597_0 : Agrees (spec (fastBase 1 61 21) layout0237) scope0459 := by decide

theorem reject09597 : Rejected (base 1 61 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 21) _ validLayout0237) (by decide) scope0459 (by rw [← fastBase_exact]; exact bind09597_0) certificate0495

private theorem bind09598_0 : Agrees (spec (fastBase 1 61 22) layout0237) scope0464 := by decide

theorem reject09598 : Rejected (base 1 61 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 22) _ validLayout0237) (by decide) scope0464 (by rw [← fastBase_exact]; exact bind09598_0) certificate0500

private theorem bind09599_0 : Agrees (spec (fastBase 1 61 23) layout0237) scope0464 := by decide

theorem reject09599 : Rejected (base 1 61 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 23) _ validLayout0237) (by decide) scope0464 (by rw [← fastBase_exact]; exact bind09599_0) certificate0500

private theorem bind09600_0 : Agrees (spec (fastBase 1 61 24) layout0237) scope0464 := by decide

theorem reject09600 : Rejected (base 1 61 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 24) _ validLayout0237) (by decide) scope0464 (by rw [← fastBase_exact]; exact bind09600_0) certificate0500

private theorem bind09601_0 : Agrees (spec (fastBase 1 61 25) layout0237) scope0464 := by decide

theorem reject09601 : Rejected (base 1 61 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 25) _ validLayout0237) (by decide) scope0464 (by rw [← fastBase_exact]; exact bind09601_0) certificate0500

private theorem bind09602_0 : Agrees (spec (fastBase 1 61 26) layout0237) scope0464 := by decide

theorem reject09602 : Rejected (base 1 61 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 26) _ validLayout0237) (by decide) scope0464 (by rw [← fastBase_exact]; exact bind09602_0) certificate0500

private theorem bind09603_0 : Agrees (spec (fastBase 1 61 27) layout0237) scope0459 := by decide

theorem reject09603 : Rejected (base 1 61 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 27) _ validLayout0237) (by decide) scope0459 (by rw [← fastBase_exact]; exact bind09603_0) certificate0495

private theorem bind09604_0 : Agrees (spec (fastBase 1 61 28) layout0237) scope0577 := by decide

theorem reject09604 : Rejected (base 1 61 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 28) _ validLayout0237) (by decide) scope0577 (by rw [← fastBase_exact]; exact bind09604_0) certificate0620

private theorem bind09605_0 : Agrees (spec (fastBase 1 61 29) layout0236) scope0281 := by decide

theorem reject09605 : Rejected (base 1 61 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 29) _ validLayout0236) (by decide) scope0281 (by rw [← fastBase_exact]; exact bind09605_0) certificate0284

private theorem bind09606_0 : Agrees (spec (fastBase 1 61 30) layout0237) scope0460 := by decide

theorem reject09606 : Rejected (base 1 61 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 30) _ validLayout0237) (by decide) scope0460 (by rw [← fastBase_exact]; exact bind09606_0) certificate0496

private theorem bind09607_0 : Agrees (spec (fastBase 1 61 31) layout0237) scope0579 := by decide

theorem reject09607 : Rejected (base 1 61 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 31) _ validLayout0237) (by decide) scope0579 (by rw [← fastBase_exact]; exact bind09607_0) certificate0622

private theorem bind09608_0 : Agrees (spec (fastBase 1 61 32) layout0237) scope0580 := by decide

theorem reject09608 : Rejected (base 1 61 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 32) _ validLayout0237) (by decide) scope0580 (by rw [← fastBase_exact]; exact bind09608_0) certificate0623

private theorem bind09609_0 : Agrees (spec (fastBase 1 61 33) layout0237) scope0575 := by decide

theorem reject09609 : Rejected (base 1 61 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 33) _ validLayout0237) (by decide) scope0575 (by rw [← fastBase_exact]; exact bind09609_0) certificate0618

private theorem bind09610_0 : Agrees (spec (fastBase 1 61 34) layout0236) scope0265 := by decide

theorem reject09610 : Rejected (base 1 61 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 34) _ validLayout0236) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind09610_0) certificate0268

private theorem bind09611_0 : Agrees (spec (fastBase 1 61 35) layout0237) scope0288 := by decide

theorem reject09611 : Rejected (base 1 61 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 35) _ validLayout0237) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09611_0) certificate0291

private theorem bind09612_0 : Agrees (spec (fastBase 1 61 36) layout0236) scope0283 := by decide

theorem reject09612 : Rejected (base 1 61 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 36) _ validLayout0236) (by decide) scope0283 (by rw [← fastBase_exact]; exact bind09612_0) certificate0286

private theorem bind09613_0 : Agrees (spec (fastBase 1 61 37) layout0237) scope0291 := by decide

theorem reject09613 : Rejected (base 1 61 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 37) _ validLayout0237) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind09613_0) certificate0294

private theorem bind09614_0 : Agrees (spec (fastBase 1 61 38) layout0237) scope0575 := by decide

theorem reject09614 : Rejected (base 1 61 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 38) _ validLayout0237) (by decide) scope0575 (by rw [← fastBase_exact]; exact bind09614_0) certificate0618

private theorem bind09615_0 : Agrees (spec (fastBase 1 61 39) layout0237) scope0463 := by decide

theorem reject09615 : Rejected (base 1 61 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 39) _ validLayout0237) (by decide) scope0463 (by rw [← fastBase_exact]; exact bind09615_0) certificate0499

private theorem bind09616_0 : Agrees (spec (fastBase 1 61 40) layout0236) scope0265 := by decide

theorem reject09616 : Rejected (base 1 61 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 40) _ validLayout0236) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind09616_0) certificate0268

private theorem bind09617_0 : Agrees (spec (fastBase 1 61 41) layout0237) scope0285 := by decide

theorem reject09617 : Rejected (base 1 61 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 41) _ validLayout0237) (by decide) scope0285 (by rw [← fastBase_exact]; exact bind09617_0) certificate0288

private theorem bind09618_0 : Agrees (spec (fastBase 1 61 42) layout0237) scope0579 := by decide

theorem reject09618 : Rejected (base 1 61 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 42) _ validLayout0237) (by decide) scope0579 (by rw [← fastBase_exact]; exact bind09618_0) certificate0622

private theorem bind09619_0 : Agrees (spec (fastBase 1 61 43) layout0237) scope0574 := by decide

theorem reject09619 : Rejected (base 1 61 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 43) _ validLayout0237) (by decide) scope0574 (by rw [← fastBase_exact]; exact bind09619_0) certificate0617

private theorem bind09620_0 : Agrees (spec (fastBase 1 61 44) layout0237) scope0461 := by decide

theorem reject09620 : Rejected (base 1 61 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 44) _ validLayout0237) (by decide) scope0461 (by rw [← fastBase_exact]; exact bind09620_0) certificate0497

private theorem bind09621_0 : Agrees (spec (fastBase 1 61 45) layout0237) scope0460 := by decide

theorem reject09621 : Rejected (base 1 61 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 45) _ validLayout0237) (by decide) scope0460 (by rw [← fastBase_exact]; exact bind09621_0) certificate0496

private theorem bind09622_0 : Agrees (spec (fastBase 1 61 46) layout0237) scope0289 := by decide

theorem reject09622 : Rejected (base 1 61 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 46) _ validLayout0237) (by decide) scope0289 (by rw [← fastBase_exact]; exact bind09622_0) certificate0292

private theorem bind09623_0 : Agrees (spec (fastBase 1 61 47) layout0237) scope0462 := by decide

theorem reject09623 : Rejected (base 1 61 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 47) _ validLayout0237) (by decide) scope0462 (by rw [← fastBase_exact]; exact bind09623_0) certificate0498

private theorem bind09624_0 : Agrees (spec (fastBase 1 61 48) layout0237) scope0577 := by decide

theorem reject09624 : Rejected (base 1 61 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 48) _ validLayout0237) (by decide) scope0577 (by rw [← fastBase_exact]; exact bind09624_0) certificate0620

private theorem bind09625_0 : Agrees (spec (fastBase 1 61 49) layout0237) scope0574 := by decide

theorem reject09625 : Rejected (base 1 61 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 49) _ validLayout0237) (by decide) scope0574 (by rw [← fastBase_exact]; exact bind09625_0) certificate0617

private theorem bind09626_0 : Agrees (spec (fastBase 1 61 50) layout0237) scope0460 := by decide

theorem reject09626 : Rejected (base 1 61 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 50) _ validLayout0237) (by decide) scope0460 (by rw [← fastBase_exact]; exact bind09626_0) certificate0496

private theorem bind09627_0 : Agrees (spec (fastBase 1 61 51) layout0237) scope0581 := by decide

theorem reject09627 : Rejected (base 1 61 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 51) _ validLayout0237) (by decide) scope0581 (by rw [← fastBase_exact]; exact bind09627_0) certificate0624

private theorem bind09628_0 : Agrees (spec (fastBase 1 61 52) layout0237) scope0285 := by decide

theorem reject09628 : Rejected (base 1 61 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 52) _ validLayout0237) (by decide) scope0285 (by rw [← fastBase_exact]; exact bind09628_0) certificate0288

private theorem bind09629_0 : Agrees (spec (fastBase 1 61 53) layout0237) scope0575 := by decide

theorem reject09629 : Rejected (base 1 61 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 53) _ validLayout0237) (by decide) scope0575 (by rw [← fastBase_exact]; exact bind09629_0) certificate0618

private theorem bind09630_0 : Agrees (spec (fastBase 1 61 54) layout0237) scope0578 := by decide

theorem reject09630 : Rejected (base 1 61 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 54) _ validLayout0237) (by decide) scope0578 (by rw [← fastBase_exact]; exact bind09630_0) certificate0621

private theorem bind09631_0 : Agrees (spec (fastBase 1 61 55) layout0237) scope0288 := by decide

theorem reject09631 : Rejected (base 1 61 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 55) _ validLayout0237) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09631_0) certificate0291

private theorem bind09632_0 : Agrees (spec (fastBase 1 61 56) layout0237) scope0576 := by decide

theorem reject09632 : Rejected (base 1 61 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 56) _ validLayout0237) (by decide) scope0576 (by rw [← fastBase_exact]; exact bind09632_0) certificate0619

private theorem bind09633_0 : Agrees (spec (fastBase 1 61 57) layout0286) scope0289 := by decide

theorem reject09633 : Rejected (base 1 61 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0286 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 57) _ validLayout0286) (by decide) scope0289 (by rw [← fastBase_exact]; exact bind09633_0) certificate0292

private theorem bind09634_0 : Agrees (spec (fastBase 1 61 58) layout0286) scope0288 := by decide

theorem reject09634 : Rejected (base 1 61 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0286 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 58) _ validLayout0286) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09634_0) certificate0291

private theorem bind09635_0 : Agrees (spec (fastBase 1 61 59) layout0236) scope0290 := by decide

private theorem bind09635_1 : Agrees (spec (fastBase 1 61 59) layout0286) scope0273 := by decide

theorem reject09635 : Rejected (base 1 61 59) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0236 layout0286 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 59) _ validLayout0236) (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 59) _ validLayout0286) (by decide) (by decide) scope0290 scope0273 (by rw [← fastBase_exact]; exact bind09635_0) (by rw [← fastBase_exact]; exact bind09635_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0293 certificate0276 (by decide)

private theorem bind09636_0 : Agrees (spec (fastBase 1 61 60) layout0236) scope0272 := by decide

private theorem bind09636_1 : Agrees (spec (fastBase 1 61 60) layout0286) scope0273 := by decide

theorem reject09636 : Rejected (base 1 61 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0236 layout0286 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 60) _ validLayout0236) (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 60) _ validLayout0286) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind09636_0) (by rw [← fastBase_exact]; exact bind09636_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind09637_0 : Agrees (spec (fastBase 1 61 61) layout0236) scope0271 := by decide

theorem reject09637 : Rejected (base 1 61 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 61) _ validLayout0236) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind09637_0) certificate0274

private theorem bind09638_0 : Agrees (spec (fastBase 1 61 62) layout0237) scope0576 := by decide

theorem reject09638 : Rejected (base 1 61 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 62) _ validLayout0237) (by decide) scope0576 (by rw [← fastBase_exact]; exact bind09638_0) certificate0619

private theorem bind09639_0 : Agrees (spec (fastBase 1 61 63) layout0236) scope0280 := by decide

theorem reject09639 : Rejected (base 1 61 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0236 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 63) _ validLayout0236) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind09639_0) certificate0283

private theorem bind09640_0 : Agrees (spec (fastBase 1 61 64) layout0237) scope0461 := by decide

theorem reject09640 : Rejected (base 1 61 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 64) _ validLayout0237) (by decide) scope0461 (by rw [← fastBase_exact]; exact bind09640_0) certificate0497

private theorem bind09641_0 : Agrees (spec (fastBase 1 61 65) layout0237) scope0288 := by decide

theorem reject09641 : Rejected (base 1 61 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 65) _ validLayout0237) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09641_0) certificate0291

private theorem bind09642_0 : Agrees (spec (fastBase 1 61 66) layout0237) scope0289 := by decide

theorem reject09642 : Rejected (base 1 61 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 66) _ validLayout0237) (by decide) scope0289 (by rw [← fastBase_exact]; exact bind09642_0) certificate0292

private theorem bind09643_0 : Agrees (spec (fastBase 1 61 67) layout0237) scope0581 := by decide

theorem reject09643 : Rejected (base 1 61 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 67) _ validLayout0237) (by decide) scope0581 (by rw [← fastBase_exact]; exact bind09643_0) certificate0624

private theorem bind09644_0 : Agrees (spec (fastBase 1 61 68) layout0237) scope0578 := by decide

theorem reject09644 : Rejected (base 1 61 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 68) _ validLayout0237) (by decide) scope0578 (by rw [← fastBase_exact]; exact bind09644_0) certificate0621

private theorem bind09645_0 : Agrees (spec (fastBase 1 61 69) layout0237) scope0574 := by decide

theorem reject09645 : Rejected (base 1 61 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 69) _ validLayout0237) (by decide) scope0574 (by rw [← fastBase_exact]; exact bind09645_0) certificate0617

private theorem bind09646_0 : Agrees (spec (fastBase 1 61 70) layout0237) scope0289 := by decide

theorem reject09646 : Rejected (base 1 61 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 70) _ validLayout0237) (by decide) scope0289 (by rw [← fastBase_exact]; exact bind09646_0) certificate0292

private theorem bind09647_0 : Agrees (spec (fastBase 1 61 71) layout0237) scope0576 := by decide

theorem reject09647 : Rejected (base 1 61 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0237 (layoutValid_of_refines _ _ (base_refines_skeleton 1 61 71) _ validLayout0237) (by decide) scope0576 (by rw [← fastBase_exact]; exact bind09647_0) certificate0619

theorem allCases133 : ∀ y : Fin 72, Rejected (base 1 61 y) := by
  intro y
  fin_cases y

  · exact reject09576

  · exact reject09577

  · exact reject09578

  · exact reject09579

  · exact reject09580

  · exact reject09581

  · exact reject09582

  · exact reject09583

  · exact reject09584

  · exact reject09585

  · exact reject09586

  · exact reject09587

  · exact reject09588

  · exact reject09589

  · exact reject09590

  · exact reject09591

  · exact reject09592

  · exact reject09593

  · exact reject09594

  · exact reject09595

  · exact reject09596

  · exact reject09597

  · exact reject09598

  · exact reject09599

  · exact reject09600

  · exact reject09601

  · exact reject09602

  · exact reject09603

  · exact reject09604

  · exact reject09605

  · exact reject09606

  · exact reject09607

  · exact reject09608

  · exact reject09609

  · exact reject09610

  · exact reject09611

  · exact reject09612

  · exact reject09613

  · exact reject09614

  · exact reject09615

  · exact reject09616

  · exact reject09617

  · exact reject09618

  · exact reject09619

  · exact reject09620

  · exact reject09621

  · exact reject09622

  · exact reject09623

  · exact reject09624

  · exact reject09625

  · exact reject09626

  · exact reject09627

  · exact reject09628

  · exact reject09629

  · exact reject09630

  · exact reject09631

  · exact reject09632

  · exact reject09633

  · exact reject09634

  · exact reject09635

  · exact reject09636

  · exact reject09637

  · exact reject09638

  · exact reject09639

  · exact reject09640

  · exact reject09641

  · exact reject09642

  · exact reject09643

  · exact reject09644

  · exact reject09645

  · exact reject09646

  · exact reject09647

end PricingIntegration.RemainingGWitnesses
