import PricingIntegration.RemainingGLayouts002

import PricingIntegration.RemainingGLayouts003

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks007

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks026

import PricingIntegration.RemainingGScopeChecks036


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05544_0 : Agrees (spec (fastBase 1 5 0) layout0025) scope0534 := by decide

theorem reject05544 : Rejected (base 1 5 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 0) _ validLayout0025) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind05544_0) certificate0576

private theorem bind05545_0 : Agrees (spec (fastBase 1 5 1) layout0025) scope0393 := by decide

theorem reject05545 : Rejected (base 1 5 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 1) _ validLayout0025) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind05545_0) certificate0406

private theorem bind05546_0 : Agrees (spec (fastBase 1 5 2) layout0025) scope0535 := by decide

theorem reject05546 : Rejected (base 1 5 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 2) _ validLayout0025) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind05546_0) certificate0577

private theorem bind05547_0 : Agrees (spec (fastBase 1 5 3) layout0025) scope0536 := by decide

theorem reject05547 : Rejected (base 1 5 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 3) _ validLayout0025) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind05547_0) certificate0578

private theorem bind05548_0 : Agrees (spec (fastBase 1 5 4) layout0025) scope0392 := by decide

theorem reject05548 : Rejected (base 1 5 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 4) _ validLayout0025) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind05548_0) certificate0405

private theorem bind05549_0 : Agrees (spec (fastBase 1 5 5) layout0025) scope0537 := by decide

theorem reject05549 : Rejected (base 1 5 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 5) _ validLayout0025) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind05549_0) certificate0579

private theorem bind05550_0 : Agrees (spec (fastBase 1 5 6) layout0023) scope0405 := by decide

private theorem bind05550_1 : Agrees (spec (fastBase 1 5 6) layout0028) scope0538 := by decide

theorem reject05550 : Rejected (base 1 5 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 6) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 6) _ validLayout0028) (by decide) (by decide) scope0405 scope0538 (by rw [← fastBase_exact]; exact bind05550_0) (by rw [← fastBase_exact]; exact bind05550_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0420 certificate0580 (by decide)

private theorem bind05551_0 : Agrees (spec (fastBase 1 5 7) layout0023) scope0148 := by decide

private theorem bind05551_1 : Agrees (spec (fastBase 1 5 7) layout0028) scope0539 := by decide

theorem reject05551 : Rejected (base 1 5 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 7) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 7) _ validLayout0028) (by decide) (by decide) scope0148 scope0539 (by rw [← fastBase_exact]; exact bind05551_0) (by rw [← fastBase_exact]; exact bind05551_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0581 (by decide)

private theorem bind05552_0 : Agrees (spec (fastBase 1 5 8) layout0025) scope0399 := by decide

theorem reject05552 : Rejected (base 1 5 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 8) _ validLayout0025) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind05552_0) certificate0412

private theorem bind05553_0 : Agrees (spec (fastBase 1 5 9) layout0025) scope0400 := by decide

theorem reject05553 : Rejected (base 1 5 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 9) _ validLayout0025) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind05553_0) certificate0413

private theorem bind05554_0 : Agrees (spec (fastBase 1 5 10) layout0025) scope0133 := by decide

theorem reject05554 : Rejected (base 1 5 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 10) _ validLayout0025) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind05554_0) certificate0136

private theorem bind05555_0 : Agrees (spec (fastBase 1 5 11) layout0025) scope0137 := by decide

theorem reject05555 : Rejected (base 1 5 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 11) _ validLayout0025) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind05555_0) certificate0140

private theorem bind05556_0 : Agrees (spec (fastBase 1 5 12) layout0025) scope0540 := by decide

theorem reject05556 : Rejected (base 1 5 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 12) _ validLayout0025) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind05556_0) certificate0582

private theorem bind05557_0 : Agrees (spec (fastBase 1 5 13) layout0025) scope0535 := by decide

theorem reject05557 : Rejected (base 1 5 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 13) _ validLayout0025) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind05557_0) certificate0577

private theorem bind05558_0 : Agrees (spec (fastBase 1 5 14) layout0025) scope0537 := by decide

theorem reject05558 : Rejected (base 1 5 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 14) _ validLayout0025) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind05558_0) certificate0579

private theorem bind05559_0 : Agrees (spec (fastBase 1 5 15) layout0025) scope0534 := by decide

theorem reject05559 : Rejected (base 1 5 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 15) _ validLayout0025) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind05559_0) certificate0576

private theorem bind05560_0 : Agrees (spec (fastBase 1 5 16) layout0025) scope0541 := by decide

theorem reject05560 : Rejected (base 1 5 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 16) _ validLayout0025) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind05560_0) certificate0583

private theorem bind05561_0 : Agrees (spec (fastBase 1 5 17) layout0025) scope0542 := by decide

theorem reject05561 : Rejected (base 1 5 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 17) _ validLayout0025) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind05561_0) certificate0584

private theorem bind05562_0 : Agrees (spec (fastBase 1 5 18) layout0025) scope0536 := by decide

theorem reject05562 : Rejected (base 1 5 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 18) _ validLayout0025) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind05562_0) certificate0578

private theorem bind05563_0 : Agrees (spec (fastBase 1 5 19) layout0025) scope0393 := by decide

theorem reject05563 : Rejected (base 1 5 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 19) _ validLayout0025) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind05563_0) certificate0406

private theorem bind05564_0 : Agrees (spec (fastBase 1 5 20) layout0023) scope0160 := by decide

theorem reject05564 : Rejected (base 1 5 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 20) _ validLayout0023) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind05564_0) certificate0163

private theorem bind05565_0 : Agrees (spec (fastBase 1 5 21) layout0025) scope0400 := by decide

theorem reject05565 : Rejected (base 1 5 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 21) _ validLayout0025) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind05565_0) certificate0413

private theorem bind05566_0 : Agrees (spec (fastBase 1 5 22) layout0025) scope0534 := by decide

theorem reject05566 : Rejected (base 1 5 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 22) _ validLayout0025) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind05566_0) certificate0576

private theorem bind05567_0 : Agrees (spec (fastBase 1 5 23) layout0025) scope0535 := by decide

theorem reject05567 : Rejected (base 1 5 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 23) _ validLayout0025) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind05567_0) certificate0577

private theorem bind05568_0 : Agrees (spec (fastBase 1 5 24) layout0025) scope0395 := by decide

theorem reject05568 : Rejected (base 1 5 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 24) _ validLayout0025) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind05568_0) certificate0408

private theorem bind05569_0 : Agrees (spec (fastBase 1 5 25) layout0023) scope0163 := by decide

theorem reject05569 : Rejected (base 1 5 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 25) _ validLayout0023) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind05569_0) certificate0166

private theorem bind05570_0 : Agrees (spec (fastBase 1 5 26) layout0025) scope0133 := by decide

theorem reject05570 : Rejected (base 1 5 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 26) _ validLayout0025) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind05570_0) certificate0136

private theorem bind05571_0 : Agrees (spec (fastBase 1 5 27) layout0025) scope0393 := by decide

theorem reject05571 : Rejected (base 1 5 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 27) _ validLayout0025) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind05571_0) certificate0406

private theorem bind05572_0 : Agrees (spec (fastBase 1 5 28) layout0025) scope0540 := by decide

theorem reject05572 : Rejected (base 1 5 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 28) _ validLayout0025) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind05572_0) certificate0582

private theorem bind05573_0 : Agrees (spec (fastBase 1 5 29) layout0025) scope0537 := by decide

theorem reject05573 : Rejected (base 1 5 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 29) _ validLayout0025) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind05573_0) certificate0579

private theorem bind05574_0 : Agrees (spec (fastBase 1 5 30) layout0025) scope0536 := by decide

theorem reject05574 : Rejected (base 1 5 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 30) _ validLayout0025) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind05574_0) certificate0578

private theorem bind05575_0 : Agrees (spec (fastBase 1 5 31) layout0025) scope0543 := by decide

theorem reject05575 : Rejected (base 1 5 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 31) _ validLayout0025) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind05575_0) certificate0585

private theorem bind05576_0 : Agrees (spec (fastBase 1 5 32) layout0025) scope0392 := by decide

theorem reject05576 : Rejected (base 1 5 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 32) _ validLayout0025) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind05576_0) certificate0405

private theorem bind05577_0 : Agrees (spec (fastBase 1 5 33) layout0025) scope0392 := by decide

theorem reject05577 : Rejected (base 1 5 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 33) _ validLayout0025) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind05577_0) certificate0405

private theorem bind05578_0 : Agrees (spec (fastBase 1 5 34) layout0025) scope0392 := by decide

theorem reject05578 : Rejected (base 1 5 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 34) _ validLayout0025) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind05578_0) certificate0405

private theorem bind05579_0 : Agrees (spec (fastBase 1 5 35) layout0025) scope0392 := by decide

theorem reject05579 : Rejected (base 1 5 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 35) _ validLayout0025) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind05579_0) certificate0405

private theorem bind05580_0 : Agrees (spec (fastBase 1 5 36) layout0025) scope0392 := by decide

theorem reject05580 : Rejected (base 1 5 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 36) _ validLayout0025) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind05580_0) certificate0405

private theorem bind05581_0 : Agrees (spec (fastBase 1 5 37) layout0025) scope0534 := by decide

theorem reject05581 : Rejected (base 1 5 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 37) _ validLayout0025) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind05581_0) certificate0576

private theorem bind05582_0 : Agrees (spec (fastBase 1 5 38) layout0025) scope0537 := by decide

theorem reject05582 : Rejected (base 1 5 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 38) _ validLayout0025) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind05582_0) certificate0579

private theorem bind05583_0 : Agrees (spec (fastBase 1 5 39) layout0025) scope0536 := by decide

theorem reject05583 : Rejected (base 1 5 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 39) _ validLayout0025) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind05583_0) certificate0578

private theorem bind05584_0 : Agrees (spec (fastBase 1 5 40) layout0025) scope0542 := by decide

theorem reject05584 : Rejected (base 1 5 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 40) _ validLayout0025) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind05584_0) certificate0584

private theorem bind05585_0 : Agrees (spec (fastBase 1 5 41) layout0025) scope0395 := by decide

theorem reject05585 : Rejected (base 1 5 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 41) _ validLayout0025) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind05585_0) certificate0408

private theorem bind05586_0 : Agrees (spec (fastBase 1 5 42) layout0025) scope0396 := by decide

theorem reject05586 : Rejected (base 1 5 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 42) _ validLayout0025) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind05586_0) certificate0409

private theorem bind05587_0 : Agrees (spec (fastBase 1 5 43) layout0025) scope0544 := by decide

theorem reject05587 : Rejected (base 1 5 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 43) _ validLayout0025) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind05587_0) certificate0586

private theorem bind05588_0 : Agrees (spec (fastBase 1 5 44) layout0025) scope0399 := by decide

theorem reject05588 : Rejected (base 1 5 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 44) _ validLayout0025) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind05588_0) certificate0412

private theorem bind05589_0 : Agrees (spec (fastBase 1 5 45) layout0023) scope0148 := by decide

private theorem bind05589_1 : Agrees (spec (fastBase 1 5 45) layout0028) scope0538 := by decide

theorem reject05589 : Rejected (base 1 5 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 45) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 45) _ validLayout0028) (by decide) (by decide) scope0148 scope0538 (by rw [← fastBase_exact]; exact bind05589_0) (by rw [← fastBase_exact]; exact bind05589_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0580 (by decide)

private theorem bind05590_0 : Agrees (spec (fastBase 1 5 46) layout0025) scope0137 := by decide

theorem reject05590 : Rejected (base 1 5 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 46) _ validLayout0025) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind05590_0) certificate0140

private theorem bind05591_0 : Agrees (spec (fastBase 1 5 47) layout0028) scope0545 := by decide

theorem reject05591 : Rejected (base 1 5 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 47) _ validLayout0028) (by decide) scope0545 (by rw [← fastBase_exact]; exact bind05591_0) certificate0587

private theorem bind05592_0 : Agrees (spec (fastBase 1 5 48) layout0028) scope0546 := by decide

theorem reject05592 : Rejected (base 1 5 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 48) _ validLayout0028) (by decide) scope0546 (by rw [← fastBase_exact]; exact bind05592_0) certificate0588

private theorem bind05593_0 : Agrees (spec (fastBase 1 5 49) layout0023) scope0405 := by decide

private theorem bind05593_1 : Agrees (spec (fastBase 1 5 49) layout0028) scope0539 := by decide

theorem reject05593 : Rejected (base 1 5 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 49) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 49) _ validLayout0028) (by decide) (by decide) scope0405 scope0539 (by rw [← fastBase_exact]; exact bind05593_0) (by rw [← fastBase_exact]; exact bind05593_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0420 certificate0581 (by decide)

private theorem bind05594_0 : Agrees (spec (fastBase 1 5 50) layout0027) scope0121 := by decide

theorem reject05594 : Rejected (base 1 5 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0027 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 50) _ validLayout0027) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind05594_0) certificate0124

private theorem bind05595_0 : Agrees (spec (fastBase 1 5 51) layout0027) scope0118 := by decide

theorem reject05595 : Rejected (base 1 5 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0027 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 51) _ validLayout0027) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind05595_0) certificate0121

private theorem bind05596_0 : Agrees (spec (fastBase 1 5 52) layout0023) scope0157 := by decide

theorem reject05596 : Rejected (base 1 5 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 52) _ validLayout0023) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind05596_0) certificate0160

private theorem bind05597_0 : Agrees (spec (fastBase 1 5 53) layout0025) scope0399 := by decide

theorem reject05597 : Rejected (base 1 5 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 53) _ validLayout0025) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind05597_0) certificate0412

private theorem bind05598_0 : Agrees (spec (fastBase 1 5 54) layout0026) scope0170 := by decide

theorem reject05598 : Rejected (base 1 5 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0026 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 54) _ validLayout0026) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind05598_0) certificate0173

private theorem bind05599_0 : Agrees (spec (fastBase 1 5 55) layout0025) scope0394 := by decide

theorem reject05599 : Rejected (base 1 5 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 55) _ validLayout0025) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind05599_0) certificate0407

private theorem bind05600_0 : Agrees (spec (fastBase 1 5 56) layout0025) scope0133 := by decide

theorem reject05600 : Rejected (base 1 5 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 56) _ validLayout0025) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind05600_0) certificate0136

private theorem bind05601_0 : Agrees (spec (fastBase 1 5 57) layout0025) scope0393 := by decide

theorem reject05601 : Rejected (base 1 5 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 57) _ validLayout0025) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind05601_0) certificate0406

private theorem bind05602_0 : Agrees (spec (fastBase 1 5 58) layout0025) scope0543 := by decide

theorem reject05602 : Rejected (base 1 5 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 58) _ validLayout0025) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind05602_0) certificate0585

private theorem bind05603_0 : Agrees (spec (fastBase 1 5 59) layout0025) scope0396 := by decide

theorem reject05603 : Rejected (base 1 5 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 59) _ validLayout0025) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind05603_0) certificate0409

private theorem bind05604_0 : Agrees (spec (fastBase 1 5 60) layout0025) scope0400 := by decide

theorem reject05604 : Rejected (base 1 5 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 60) _ validLayout0025) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind05604_0) certificate0413

private theorem bind05605_0 : Agrees (spec (fastBase 1 5 61) layout0025) scope0137 := by decide

theorem reject05605 : Rejected (base 1 5 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 61) _ validLayout0025) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind05605_0) certificate0140

private theorem bind05606_0 : Agrees (spec (fastBase 1 5 62) layout0025) scope0535 := by decide

theorem reject05606 : Rejected (base 1 5 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 62) _ validLayout0025) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind05606_0) certificate0577

private theorem bind05607_0 : Agrees (spec (fastBase 1 5 63) layout0025) scope0541 := by decide

theorem reject05607 : Rejected (base 1 5 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 63) _ validLayout0025) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind05607_0) certificate0583

private theorem bind05608_0 : Agrees (spec (fastBase 1 5 64) layout0025) scope0133 := by decide

theorem reject05608 : Rejected (base 1 5 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 64) _ validLayout0025) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind05608_0) certificate0136

private theorem bind05609_0 : Agrees (spec (fastBase 1 5 65) layout0025) scope0399 := by decide

theorem reject05609 : Rejected (base 1 5 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 65) _ validLayout0025) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind05609_0) certificate0412

private theorem bind05610_0 : Agrees (spec (fastBase 1 5 66) layout0025) scope0544 := by decide

theorem reject05610 : Rejected (base 1 5 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 66) _ validLayout0025) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind05610_0) certificate0586

private theorem bind05611_0 : Agrees (spec (fastBase 1 5 67) layout0023) scope0165 := by decide

theorem reject05611 : Rejected (base 1 5 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 67) _ validLayout0023) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind05611_0) certificate0168

private theorem bind05612_0 : Agrees (spec (fastBase 1 5 68) layout0025) scope0137 := by decide

theorem reject05612 : Rejected (base 1 5 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 68) _ validLayout0025) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind05612_0) certificate0140

private theorem bind05613_0 : Agrees (spec (fastBase 1 5 69) layout0023) scope0155 := by decide

theorem reject05613 : Rejected (base 1 5 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 69) _ validLayout0023) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind05613_0) certificate0158

private theorem bind05614_0 : Agrees (spec (fastBase 1 5 70) layout0025) scope0400 := by decide

theorem reject05614 : Rejected (base 1 5 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 70) _ validLayout0025) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind05614_0) certificate0413

private theorem bind05615_0 : Agrees (spec (fastBase 1 5 71) layout0025) scope0394 := by decide

theorem reject05615 : Rejected (base 1 5 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 1 5 71) _ validLayout0025) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind05615_0) certificate0407

theorem allCases077 : ∀ y : Fin 72, Rejected (base 1 5 y) := by
  intro y
  fin_cases y

  · exact reject05544

  · exact reject05545

  · exact reject05546

  · exact reject05547

  · exact reject05548

  · exact reject05549

  · exact reject05550

  · exact reject05551

  · exact reject05552

  · exact reject05553

  · exact reject05554

  · exact reject05555

  · exact reject05556

  · exact reject05557

  · exact reject05558

  · exact reject05559

  · exact reject05560

  · exact reject05561

  · exact reject05562

  · exact reject05563

  · exact reject05564

  · exact reject05565

  · exact reject05566

  · exact reject05567

  · exact reject05568

  · exact reject05569

  · exact reject05570

  · exact reject05571

  · exact reject05572

  · exact reject05573

  · exact reject05574

  · exact reject05575

  · exact reject05576

  · exact reject05577

  · exact reject05578

  · exact reject05579

  · exact reject05580

  · exact reject05581

  · exact reject05582

  · exact reject05583

  · exact reject05584

  · exact reject05585

  · exact reject05586

  · exact reject05587

  · exact reject05588

  · exact reject05589

  · exact reject05590

  · exact reject05591

  · exact reject05592

  · exact reject05593

  · exact reject05594

  · exact reject05595

  · exact reject05596

  · exact reject05597

  · exact reject05598

  · exact reject05599

  · exact reject05600

  · exact reject05601

  · exact reject05602

  · exact reject05603

  · exact reject05604

  · exact reject05605

  · exact reject05606

  · exact reject05607

  · exact reject05608

  · exact reject05609

  · exact reject05610

  · exact reject05611

  · exact reject05612

  · exact reject05613

  · exact reject05614

  · exact reject05615

end PricingIntegration.RemainingGWitnesses
