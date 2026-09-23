import PricingIntegration.RemainingGLayouts022

import PricingIntegration.RemainingGLayouts023

import PricingIntegration.RemainingGLayouts034

import PricingIntegration.RemainingGLayouts035

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks037

import PricingIntegration.RemainingGScopeChecks039


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind08424_0 : Agrees (spec (fastBase 1 45 0) layout0180) scope0423 := by decide

theorem reject08424 : Rejected (base 1 45 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 0) _ validLayout0180) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind08424_0) certificate0447

private theorem bind08425_0 : Agrees (spec (fastBase 1 45 1) layout0182) scope0586 := by decide

theorem reject08425 : Rejected (base 1 45 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 1) _ validLayout0182) (by decide) scope0586 (by rw [← fastBase_exact]; exact bind08425_0) certificate0631

private theorem bind08426_0 : Agrees (spec (fastBase 1 45 2) layout0182) scope0198 := by decide

theorem reject08426 : Rejected (base 1 45 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 2) _ validLayout0182) (by decide) scope0198 (by rw [← fastBase_exact]; exact bind08426_0) certificate0201

private theorem bind08427_0 : Agrees (spec (fastBase 1 45 3) layout0183) scope0182 := by decide

private theorem bind08427_1 : Agrees (spec (fastBase 1 45 3) layout0279) scope0179 := by decide

theorem reject08427 : Rejected (base 1 45 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0183 layout0279 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 3) _ validLayout0183) (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 3) _ validLayout0279) (by decide) (by decide) scope0182 scope0179 (by rw [← fastBase_exact]; exact bind08427_0) (by rw [← fastBase_exact]; exact bind08427_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0182 (by decide)

private theorem bind08428_0 : Agrees (spec (fastBase 1 45 4) layout0180) scope0208 := by decide

theorem reject08428 : Rejected (base 1 45 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 4) _ validLayout0180) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind08428_0) certificate0211

private theorem bind08429_0 : Agrees (spec (fastBase 1 45 5) layout0183) scope0178 := by decide

private theorem bind08429_1 : Agrees (spec (fastBase 1 45 5) layout0279) scope0183 := by decide

theorem reject08429 : Rejected (base 1 45 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0183 layout0279 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 5) _ validLayout0183) (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 5) _ validLayout0279) (by decide) (by decide) scope0178 scope0183 (by rw [← fastBase_exact]; exact bind08429_0) (by rw [← fastBase_exact]; exact bind08429_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0181 certificate0186 (by decide)

private theorem bind08430_0 : Agrees (spec (fastBase 1 45 6) layout0180) scope0205 := by decide

theorem reject08430 : Rejected (base 1 45 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 6) _ validLayout0180) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind08430_0) certificate0208

private theorem bind08431_0 : Agrees (spec (fastBase 1 45 7) layout0182) scope0204 := by decide

theorem reject08431 : Rejected (base 1 45 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 7) _ validLayout0182) (by decide) scope0204 (by rw [← fastBase_exact]; exact bind08431_0) certificate0207

private theorem bind08432_0 : Agrees (spec (fastBase 1 45 8) layout0180) scope0553 := by decide

theorem reject08432 : Rejected (base 1 45 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 8) _ validLayout0180) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind08432_0) certificate0596

private theorem bind08433_0 : Agrees (spec (fastBase 1 45 9) layout0180) scope0195 := by decide

theorem reject08433 : Rejected (base 1 45 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 9) _ validLayout0180) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind08433_0) certificate0198

private theorem bind08434_0 : Agrees (spec (fastBase 1 45 10) layout0180) scope0197 := by decide

theorem reject08434 : Rejected (base 1 45 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 10) _ validLayout0180) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind08434_0) certificate0200

private theorem bind08435_0 : Agrees (spec (fastBase 1 45 11) layout0182) scope0587 := by decide

theorem reject08435 : Rejected (base 1 45 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 11) _ validLayout0182) (by decide) scope0587 (by rw [← fastBase_exact]; exact bind08435_0) certificate0632

private theorem bind08436_0 : Agrees (spec (fastBase 1 45 12) layout0182) scope0588 := by decide

theorem reject08436 : Rejected (base 1 45 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 12) _ validLayout0182) (by decide) scope0588 (by rw [← fastBase_exact]; exact bind08436_0) certificate0633

private theorem bind08437_0 : Agrees (spec (fastBase 1 45 13) layout0184) scope0197 := by decide

theorem reject08437 : Rejected (base 1 45 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0184 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 13) _ validLayout0184) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind08437_0) certificate0200

private theorem bind08438_0 : Agrees (spec (fastBase 1 45 14) layout0180) scope0559 := by decide

theorem reject08438 : Rejected (base 1 45 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 14) _ validLayout0180) (by decide) scope0559 (by rw [← fastBase_exact]; exact bind08438_0) certificate0602

private theorem bind08439_0 : Agrees (spec (fastBase 1 45 15) layout0180) scope0421 := by decide

theorem reject08439 : Rejected (base 1 45 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 15) _ validLayout0180) (by decide) scope0421 (by rw [← fastBase_exact]; exact bind08439_0) certificate0444

private theorem bind08440_0 : Agrees (spec (fastBase 1 45 16) layout0180) scope0423 := by decide

theorem reject08440 : Rejected (base 1 45 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 16) _ validLayout0180) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind08440_0) certificate0447

private theorem bind08441_0 : Agrees (spec (fastBase 1 45 17) layout0180) scope0423 := by decide

theorem reject08441 : Rejected (base 1 45 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 17) _ validLayout0180) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind08441_0) certificate0447

private theorem bind08442_0 : Agrees (spec (fastBase 1 45 18) layout0280) scope0587 := by decide

theorem reject08442 : Rejected (base 1 45 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0280 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 18) _ validLayout0280) (by decide) scope0587 (by rw [← fastBase_exact]; exact bind08442_0) certificate0632

private theorem bind08443_0 : Agrees (spec (fastBase 1 45 19) layout0180) scope0208 := by decide

theorem reject08443 : Rejected (base 1 45 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 19) _ validLayout0180) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind08443_0) certificate0211

private theorem bind08444_0 : Agrees (spec (fastBase 1 45 20) layout0180) scope0424 := by decide

theorem reject08444 : Rejected (base 1 45 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 20) _ validLayout0180) (by decide) scope0424 (by rw [← fastBase_exact]; exact bind08444_0) certificate0448

private theorem bind08445_0 : Agrees (spec (fastBase 1 45 21) layout0180) scope0558 := by decide

theorem reject08445 : Rejected (base 1 45 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 21) _ validLayout0180) (by decide) scope0558 (by rw [← fastBase_exact]; exact bind08445_0) certificate0601

private theorem bind08446_0 : Agrees (spec (fastBase 1 45 22) layout0180) scope0423 := by decide

theorem reject08446 : Rejected (base 1 45 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 22) _ validLayout0180) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind08446_0) certificate0447

private theorem bind08447_0 : Agrees (spec (fastBase 1 45 23) layout0180) scope0424 := by decide

theorem reject08447 : Rejected (base 1 45 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 23) _ validLayout0180) (by decide) scope0424 (by rw [← fastBase_exact]; exact bind08447_0) certificate0448

private theorem bind08448_0 : Agrees (spec (fastBase 1 45 24) layout0182) scope0588 := by decide

theorem reject08448 : Rejected (base 1 45 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 24) _ validLayout0182) (by decide) scope0588 (by rw [← fastBase_exact]; exact bind08448_0) certificate0633

private theorem bind08449_0 : Agrees (spec (fastBase 1 45 25) layout0180) scope0205 := by decide

theorem reject08449 : Rejected (base 1 45 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 25) _ validLayout0180) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind08449_0) certificate0208

private theorem bind08450_0 : Agrees (spec (fastBase 1 45 26) layout0180) scope0420 := by decide

theorem reject08450 : Rejected (base 1 45 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 26) _ validLayout0180) (by decide) scope0420 (by rw [← fastBase_exact]; exact bind08450_0) certificate0443

private theorem bind08451_0 : Agrees (spec (fastBase 1 45 27) layout0182) scope0586 := by decide

theorem reject08451 : Rejected (base 1 45 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 27) _ validLayout0182) (by decide) scope0586 (by rw [← fastBase_exact]; exact bind08451_0) certificate0631

private theorem bind08452_0 : Agrees (spec (fastBase 1 45 28) layout0182) scope0589 := by decide

theorem reject08452 : Rejected (base 1 45 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 28) _ validLayout0182) (by decide) scope0589 (by rw [← fastBase_exact]; exact bind08452_0) certificate0634

private theorem bind08453_0 : Agrees (spec (fastBase 1 45 29) layout0183) scope0182 := by decide

private theorem bind08453_1 : Agrees (spec (fastBase 1 45 29) layout0279) scope0183 := by decide

theorem reject08453 : Rejected (base 1 45 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0183 layout0279 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 29) _ validLayout0183) (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 29) _ validLayout0279) (by decide) (by decide) scope0182 scope0183 (by rw [← fastBase_exact]; exact bind08453_0) (by rw [← fastBase_exact]; exact bind08453_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0186 (by decide)

private theorem bind08454_0 : Agrees (spec (fastBase 1 45 30) layout0182) scope0590 := by decide

theorem reject08454 : Rejected (base 1 45 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 30) _ validLayout0182) (by decide) scope0590 (by rw [← fastBase_exact]; exact bind08454_0) certificate0635

private theorem bind08455_0 : Agrees (spec (fastBase 1 45 31) layout0281) scope0591 := by decide

theorem reject08455 : Rejected (base 1 45 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0281 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 31) _ validLayout0281) (by decide) scope0591 (by rw [← fastBase_exact]; exact bind08455_0) certificate0636

private theorem bind08456_0 : Agrees (spec (fastBase 1 45 32) layout0183) scope0176 := by decide

theorem reject08456 : Rejected (base 1 45 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 32) _ validLayout0183) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind08456_0) certificate0179

private theorem bind08457_0 : Agrees (spec (fastBase 1 45 33) layout0180) scope0559 := by decide

theorem reject08457 : Rejected (base 1 45 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 33) _ validLayout0180) (by decide) scope0559 (by rw [← fastBase_exact]; exact bind08457_0) certificate0602

private theorem bind08458_0 : Agrees (spec (fastBase 1 45 34) layout0184) scope0195 := by decide

theorem reject08458 : Rejected (base 1 45 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0184 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 34) _ validLayout0184) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind08458_0) certificate0198

private theorem bind08459_0 : Agrees (spec (fastBase 1 45 35) layout0180) scope0208 := by decide

theorem reject08459 : Rejected (base 1 45 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 35) _ validLayout0180) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind08459_0) certificate0211

private theorem bind08460_0 : Agrees (spec (fastBase 1 45 36) layout0180) scope0555 := by decide

theorem reject08460 : Rejected (base 1 45 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 36) _ validLayout0180) (by decide) scope0555 (by rw [← fastBase_exact]; exact bind08460_0) certificate0598

private theorem bind08461_0 : Agrees (spec (fastBase 1 45 37) layout0180) scope0558 := by decide

theorem reject08461 : Rejected (base 1 45 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 37) _ validLayout0180) (by decide) scope0558 (by rw [← fastBase_exact]; exact bind08461_0) certificate0601

private theorem bind08462_0 : Agrees (spec (fastBase 1 45 38) layout0180) scope0208 := by decide

theorem reject08462 : Rejected (base 1 45 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 38) _ validLayout0180) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind08462_0) certificate0211

private theorem bind08463_0 : Agrees (spec (fastBase 1 45 39) layout0183) scope0178 := by decide

private theorem bind08463_1 : Agrees (spec (fastBase 1 45 39) layout0279) scope0179 := by decide

theorem reject08463 : Rejected (base 1 45 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0183 layout0279 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 39) _ validLayout0183) (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 39) _ validLayout0279) (by decide) (by decide) scope0178 scope0179 (by rw [← fastBase_exact]; exact bind08463_0) (by rw [← fastBase_exact]; exact bind08463_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0181 certificate0182 (by decide)

private theorem bind08464_0 : Agrees (spec (fastBase 1 45 40) layout0180) scope0195 := by decide

theorem reject08464 : Rejected (base 1 45 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 40) _ validLayout0180) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind08464_0) certificate0198

private theorem bind08465_0 : Agrees (spec (fastBase 1 45 41) layout0180) scope0557 := by decide

theorem reject08465 : Rejected (base 1 45 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 41) _ validLayout0180) (by decide) scope0557 (by rw [← fastBase_exact]; exact bind08465_0) certificate0600

private theorem bind08466_0 : Agrees (spec (fastBase 1 45 42) layout0180) scope0421 := by decide

theorem reject08466 : Rejected (base 1 45 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 42) _ validLayout0180) (by decide) scope0421 (by rw [← fastBase_exact]; exact bind08466_0) certificate0444

private theorem bind08467_0 : Agrees (spec (fastBase 1 45 43) layout0183) scope0186 := by decide

theorem reject08467 : Rejected (base 1 45 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 43) _ validLayout0183) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind08467_0) certificate0189

private theorem bind08468_0 : Agrees (spec (fastBase 1 45 44) layout0180) scope0205 := by decide

theorem reject08468 : Rejected (base 1 45 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 44) _ validLayout0180) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind08468_0) certificate0208

private theorem bind08469_0 : Agrees (spec (fastBase 1 45 45) layout0184) scope0205 := by decide

theorem reject08469 : Rejected (base 1 45 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0184 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 45) _ validLayout0184) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind08469_0) certificate0208

private theorem bind08470_0 : Agrees (spec (fastBase 1 45 46) layout0180) scope0556 := by decide

theorem reject08470 : Rejected (base 1 45 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 46) _ validLayout0180) (by decide) scope0556 (by rw [← fastBase_exact]; exact bind08470_0) certificate0599

private theorem bind08471_0 : Agrees (spec (fastBase 1 45 47) layout0180) scope0420 := by decide

theorem reject08471 : Rejected (base 1 45 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 47) _ validLayout0180) (by decide) scope0420 (by rw [← fastBase_exact]; exact bind08471_0) certificate0443

private theorem bind08472_0 : Agrees (spec (fastBase 1 45 48) layout0182) scope0592 := by decide

theorem reject08472 : Rejected (base 1 45 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 48) _ validLayout0182) (by decide) scope0592 (by rw [← fastBase_exact]; exact bind08472_0) certificate0637

private theorem bind08473_0 : Agrees (spec (fastBase 1 45 49) layout0180) scope0205 := by decide

theorem reject08473 : Rejected (base 1 45 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 49) _ validLayout0180) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind08473_0) certificate0208

private theorem bind08474_0 : Agrees (spec (fastBase 1 45 50) layout0180) scope0554 := by decide

theorem reject08474 : Rejected (base 1 45 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 50) _ validLayout0180) (by decide) scope0554 (by rw [← fastBase_exact]; exact bind08474_0) certificate0597

private theorem bind08475_0 : Agrees (spec (fastBase 1 45 51) layout0180) scope0197 := by decide

theorem reject08475 : Rejected (base 1 45 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 51) _ validLayout0180) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind08475_0) certificate0200

private theorem bind08476_0 : Agrees (spec (fastBase 1 45 52) layout0180) scope0553 := by decide

theorem reject08476 : Rejected (base 1 45 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 52) _ validLayout0180) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind08476_0) certificate0596

private theorem bind08477_0 : Agrees (spec (fastBase 1 45 53) layout0180) scope0553 := by decide

theorem reject08477 : Rejected (base 1 45 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 53) _ validLayout0180) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind08477_0) certificate0596

private theorem bind08478_0 : Agrees (spec (fastBase 1 45 54) layout0180) scope0553 := by decide

theorem reject08478 : Rejected (base 1 45 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 54) _ validLayout0180) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind08478_0) certificate0596

private theorem bind08479_0 : Agrees (spec (fastBase 1 45 55) layout0180) scope0553 := by decide

theorem reject08479 : Rejected (base 1 45 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 55) _ validLayout0180) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind08479_0) certificate0596

private theorem bind08480_0 : Agrees (spec (fastBase 1 45 56) layout0180) scope0553 := by decide

theorem reject08480 : Rejected (base 1 45 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 56) _ validLayout0180) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind08480_0) certificate0596

private theorem bind08481_0 : Agrees (spec (fastBase 1 45 57) layout0180) scope0555 := by decide

theorem reject08481 : Rejected (base 1 45 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 57) _ validLayout0180) (by decide) scope0555 (by rw [← fastBase_exact]; exact bind08481_0) certificate0598

private theorem bind08482_0 : Agrees (spec (fastBase 1 45 58) layout0183) scope0191 := by decide

theorem reject08482 : Rejected (base 1 45 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 58) _ validLayout0183) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind08482_0) certificate0194

private theorem bind08483_0 : Agrees (spec (fastBase 1 45 59) layout0180) scope0195 := by decide

theorem reject08483 : Rejected (base 1 45 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 59) _ validLayout0180) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind08483_0) certificate0198

private theorem bind08484_0 : Agrees (spec (fastBase 1 45 60) layout0180) scope0418 := by decide

theorem reject08484 : Rejected (base 1 45 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 60) _ validLayout0180) (by decide) scope0418 (by rw [← fastBase_exact]; exact bind08484_0) certificate0441

private theorem bind08485_0 : Agrees (spec (fastBase 1 45 61) layout0184) scope0208 := by decide

theorem reject08485 : Rejected (base 1 45 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0184 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 61) _ validLayout0184) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind08485_0) certificate0211

private theorem bind08486_0 : Agrees (spec (fastBase 1 45 62) layout0180) scope0556 := by decide

theorem reject08486 : Rejected (base 1 45 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 62) _ validLayout0180) (by decide) scope0556 (by rw [← fastBase_exact]; exact bind08486_0) certificate0599

private theorem bind08487_0 : Agrees (spec (fastBase 1 45 63) layout0180) scope0418 := by decide

theorem reject08487 : Rejected (base 1 45 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 63) _ validLayout0180) (by decide) scope0418 (by rw [← fastBase_exact]; exact bind08487_0) certificate0441

private theorem bind08488_0 : Agrees (spec (fastBase 1 45 64) layout0183) scope0185 := by decide

theorem reject08488 : Rejected (base 1 45 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0183 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 64) _ validLayout0183) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind08488_0) certificate0188

private theorem bind08489_0 : Agrees (spec (fastBase 1 45 65) layout0180) scope0197 := by decide

theorem reject08489 : Rejected (base 1 45 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 65) _ validLayout0180) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind08489_0) certificate0200

private theorem bind08490_0 : Agrees (spec (fastBase 1 45 66) layout0182) scope0592 := by decide

theorem reject08490 : Rejected (base 1 45 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 66) _ validLayout0182) (by decide) scope0592 (by rw [← fastBase_exact]; exact bind08490_0) certificate0637

private theorem bind08491_0 : Agrees (spec (fastBase 1 45 67) layout0182) scope0587 := by decide

theorem reject08491 : Rejected (base 1 45 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0182 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 67) _ validLayout0182) (by decide) scope0587 (by rw [← fastBase_exact]; exact bind08491_0) certificate0632

private theorem bind08492_0 : Agrees (spec (fastBase 1 45 68) layout0180) scope0557 := by decide

theorem reject08492 : Rejected (base 1 45 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 68) _ validLayout0180) (by decide) scope0557 (by rw [← fastBase_exact]; exact bind08492_0) certificate0600

private theorem bind08493_0 : Agrees (spec (fastBase 1 45 69) layout0180) scope0554 := by decide

theorem reject08493 : Rejected (base 1 45 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 69) _ validLayout0180) (by decide) scope0554 (by rw [← fastBase_exact]; exact bind08493_0) certificate0597

private theorem bind08494_0 : Agrees (spec (fastBase 1 45 70) layout0180) scope0195 := by decide

theorem reject08494 : Rejected (base 1 45 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 70) _ validLayout0180) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind08494_0) certificate0198

private theorem bind08495_0 : Agrees (spec (fastBase 1 45 71) layout0180) scope0197 := by decide

theorem reject08495 : Rejected (base 1 45 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0180 (layoutValid_of_refines _ _ (base_refines_skeleton 1 45 71) _ validLayout0180) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind08495_0) certificate0200

theorem allCases117 : ∀ y : Fin 72, Rejected (base 1 45 y) := by
  intro y
  fin_cases y

  · exact reject08424

  · exact reject08425

  · exact reject08426

  · exact reject08427

  · exact reject08428

  · exact reject08429

  · exact reject08430

  · exact reject08431

  · exact reject08432

  · exact reject08433

  · exact reject08434

  · exact reject08435

  · exact reject08436

  · exact reject08437

  · exact reject08438

  · exact reject08439

  · exact reject08440

  · exact reject08441

  · exact reject08442

  · exact reject08443

  · exact reject08444

  · exact reject08445

  · exact reject08446

  · exact reject08447

  · exact reject08448

  · exact reject08449

  · exact reject08450

  · exact reject08451

  · exact reject08452

  · exact reject08453

  · exact reject08454

  · exact reject08455

  · exact reject08456

  · exact reject08457

  · exact reject08458

  · exact reject08459

  · exact reject08460

  · exact reject08461

  · exact reject08462

  · exact reject08463

  · exact reject08464

  · exact reject08465

  · exact reject08466

  · exact reject08467

  · exact reject08468

  · exact reject08469

  · exact reject08470

  · exact reject08471

  · exact reject08472

  · exact reject08473

  · exact reject08474

  · exact reject08475

  · exact reject08476

  · exact reject08477

  · exact reject08478

  · exact reject08479

  · exact reject08480

  · exact reject08481

  · exact reject08482

  · exact reject08483

  · exact reject08484

  · exact reject08485

  · exact reject08486

  · exact reject08487

  · exact reject08488

  · exact reject08489

  · exact reject08490

  · exact reject08491

  · exact reject08492

  · exact reject08493

  · exact reject08494

  · exact reject08495

end PricingIntegration.RemainingGWitnesses
