import PricingIntegration.RemainingGLayouts002

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks007

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks026

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks035


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05472_0 : Agrees (spec (fastBase 1 4 0) layout0019) scope0411 := by decide

theorem reject05472 : Rejected (base 1 4 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 0) _ validLayout0019) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind05472_0) certificate0431

private theorem bind05473_0 : Agrees (spec (fastBase 1 4 1) layout0020) scope0109 := by decide

theorem reject05473 : Rejected (base 1 4 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 1) _ validLayout0020) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind05473_0) certificate0112

private theorem bind05474_0 : Agrees (spec (fastBase 1 4 2) layout0020) scope0110 := by decide

theorem reject05474 : Rejected (base 1 4 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 2) _ validLayout0020) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind05474_0) certificate0113

private theorem bind05475_0 : Agrees (spec (fastBase 1 4 3) layout0019) scope0524 := by decide

theorem reject05475 : Rejected (base 1 4 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 3) _ validLayout0019) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind05475_0) certificate0566

private theorem bind05476_0 : Agrees (spec (fastBase 1 4 4) layout0019) scope0166 := by decide

theorem reject05476 : Rejected (base 1 4 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 4) _ validLayout0019) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind05476_0) certificate0169

private theorem bind05477_0 : Agrees (spec (fastBase 1 4 5) layout0019) scope0525 := by decide

theorem reject05477 : Rejected (base 1 4 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 5) _ validLayout0019) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind05477_0) certificate0567

private theorem bind05478_0 : Agrees (spec (fastBase 1 4 6) layout0020) scope0114 := by decide

private theorem bind05478_1 : Agrees (spec (fastBase 1 4 6) layout0021) scope0526 := by decide

theorem reject05478 : Rejected (base 1 4 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 6) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 6) _ validLayout0021) (by decide) (by decide) scope0114 scope0526 (by rw [← fastBase_exact]; exact bind05478_0) (by rw [← fastBase_exact]; exact bind05478_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0568 (by decide)

private theorem bind05479_0 : Agrees (spec (fastBase 1 4 7) layout0020) scope0116 := by decide

private theorem bind05479_1 : Agrees (spec (fastBase 1 4 7) layout0021) scope0527 := by decide

theorem reject05479 : Rejected (base 1 4 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 7) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 7) _ validLayout0021) (by decide) (by decide) scope0116 scope0527 (by rw [← fastBase_exact]; exact bind05479_0) (by rw [← fastBase_exact]; exact bind05479_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0569 (by decide)

private theorem bind05480_0 : Agrees (spec (fastBase 1 4 8) layout0020) scope0118 := by decide

theorem reject05480 : Rejected (base 1 4 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 8) _ validLayout0020) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind05480_0) certificate0121

private theorem bind05481_0 : Agrees (spec (fastBase 1 4 9) layout0019) scope0406 := by decide

theorem reject05481 : Rejected (base 1 4 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 9) _ validLayout0019) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind05481_0) certificate0423

private theorem bind05482_0 : Agrees (spec (fastBase 1 4 10) layout0019) scope0170 := by decide

theorem reject05482 : Rejected (base 1 4 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 10) _ validLayout0019) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind05482_0) certificate0173

private theorem bind05483_0 : Agrees (spec (fastBase 1 4 11) layout0020) scope0121 := by decide

theorem reject05483 : Rejected (base 1 4 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 11) _ validLayout0020) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind05483_0) certificate0124

private theorem bind05484_0 : Agrees (spec (fastBase 1 4 12) layout0019) scope0408 := by decide

theorem reject05484 : Rejected (base 1 4 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 12) _ validLayout0019) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind05484_0) certificate0428

private theorem bind05485_0 : Agrees (spec (fastBase 1 4 13) layout0020) scope0110 := by decide

theorem reject05485 : Rejected (base 1 4 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 13) _ validLayout0020) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind05485_0) certificate0113

private theorem bind05486_0 : Agrees (spec (fastBase 1 4 14) layout0019) scope0411 := by decide

theorem reject05486 : Rejected (base 1 4 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 14) _ validLayout0019) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind05486_0) certificate0431

private theorem bind05487_0 : Agrees (spec (fastBase 1 4 15) layout0019) scope0528 := by decide

theorem reject05487 : Rejected (base 1 4 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 15) _ validLayout0019) (by decide) scope0528 (by rw [← fastBase_exact]; exact bind05487_0) certificate0570

private theorem bind05488_0 : Agrees (spec (fastBase 1 4 16) layout0020) scope0108 := by decide

theorem reject05488 : Rejected (base 1 4 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 16) _ validLayout0020) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind05488_0) certificate0111

private theorem bind05489_0 : Agrees (spec (fastBase 1 4 17) layout0019) scope0529 := by decide

theorem reject05489 : Rejected (base 1 4 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 17) _ validLayout0019) (by decide) scope0529 (by rw [← fastBase_exact]; exact bind05489_0) certificate0571

private theorem bind05490_0 : Agrees (spec (fastBase 1 4 18) layout0019) scope0524 := by decide

theorem reject05490 : Rejected (base 1 4 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 18) _ validLayout0019) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind05490_0) certificate0566

private theorem bind05491_0 : Agrees (spec (fastBase 1 4 19) layout0019) scope0166 := by decide

theorem reject05491 : Rejected (base 1 4 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 19) _ validLayout0019) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind05491_0) certificate0169

private theorem bind05492_0 : Agrees (spec (fastBase 1 4 20) layout0020) scope0109 := by decide

theorem reject05492 : Rejected (base 1 4 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 20) _ validLayout0020) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind05492_0) certificate0112

private theorem bind05493_0 : Agrees (spec (fastBase 1 4 21) layout0019) scope0416 := by decide

theorem reject05493 : Rejected (base 1 4 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 21) _ validLayout0019) (by decide) scope0416 (by rw [← fastBase_exact]; exact bind05493_0) certificate0439

private theorem bind05494_0 : Agrees (spec (fastBase 1 4 22) layout0019) scope0411 := by decide

theorem reject05494 : Rejected (base 1 4 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 22) _ validLayout0019) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind05494_0) certificate0431

private theorem bind05495_0 : Agrees (spec (fastBase 1 4 23) layout0019) scope0166 := by decide

theorem reject05495 : Rejected (base 1 4 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 23) _ validLayout0019) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind05495_0) certificate0169

private theorem bind05496_0 : Agrees (spec (fastBase 1 4 24) layout0019) scope0529 := by decide

theorem reject05496 : Rejected (base 1 4 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 24) _ validLayout0019) (by decide) scope0529 (by rw [← fastBase_exact]; exact bind05496_0) certificate0571

private theorem bind05497_0 : Agrees (spec (fastBase 1 4 25) layout0020) scope0110 := by decide

theorem reject05497 : Rejected (base 1 4 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 25) _ validLayout0020) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind05497_0) certificate0113

private theorem bind05498_0 : Agrees (spec (fastBase 1 4 26) layout0019) scope0530 := by decide

theorem reject05498 : Rejected (base 1 4 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 26) _ validLayout0019) (by decide) scope0530 (by rw [← fastBase_exact]; exact bind05498_0) certificate0572

private theorem bind05499_0 : Agrees (spec (fastBase 1 4 27) layout0020) scope0109 := by decide

theorem reject05499 : Rejected (base 1 4 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 27) _ validLayout0020) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind05499_0) certificate0112

private theorem bind05500_0 : Agrees (spec (fastBase 1 4 28) layout0019) scope0531 := by decide

theorem reject05500 : Rejected (base 1 4 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 28) _ validLayout0019) (by decide) scope0531 (by rw [← fastBase_exact]; exact bind05500_0) certificate0573

private theorem bind05501_0 : Agrees (spec (fastBase 1 4 29) layout0019) scope0524 := by decide

theorem reject05501 : Rejected (base 1 4 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 29) _ validLayout0019) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind05501_0) certificate0566

private theorem bind05502_0 : Agrees (spec (fastBase 1 4 30) layout0019) scope0410 := by decide

theorem reject05502 : Rejected (base 1 4 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 30) _ validLayout0019) (by decide) scope0410 (by rw [← fastBase_exact]; exact bind05502_0) certificate0430

private theorem bind05503_0 : Agrees (spec (fastBase 1 4 31) layout0020) scope0111 := by decide

theorem reject05503 : Rejected (base 1 4 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 31) _ validLayout0020) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind05503_0) certificate0114

private theorem bind05504_0 : Agrees (spec (fastBase 1 4 32) layout0020) scope0112 := by decide

theorem reject05504 : Rejected (base 1 4 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 32) _ validLayout0020) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind05504_0) certificate0115

private theorem bind05505_0 : Agrees (spec (fastBase 1 4 33) layout0020) scope0110 := by decide

theorem reject05505 : Rejected (base 1 4 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 33) _ validLayout0020) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind05505_0) certificate0113

private theorem bind05506_0 : Agrees (spec (fastBase 1 4 34) layout0019) scope0166 := by decide

theorem reject05506 : Rejected (base 1 4 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 34) _ validLayout0019) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind05506_0) certificate0169

private theorem bind05507_0 : Agrees (spec (fastBase 1 4 35) layout0019) scope0408 := by decide

theorem reject05507 : Rejected (base 1 4 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 35) _ validLayout0019) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind05507_0) certificate0428

private theorem bind05508_0 : Agrees (spec (fastBase 1 4 36) layout0019) scope0531 := by decide

theorem reject05508 : Rejected (base 1 4 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 36) _ validLayout0019) (by decide) scope0531 (by rw [← fastBase_exact]; exact bind05508_0) certificate0573

private theorem bind05509_0 : Agrees (spec (fastBase 1 4 37) layout0019) scope0525 := by decide

theorem reject05509 : Rejected (base 1 4 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 37) _ validLayout0019) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind05509_0) certificate0567

private theorem bind05510_0 : Agrees (spec (fastBase 1 4 38) layout0019) scope0525 := by decide

theorem reject05510 : Rejected (base 1 4 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 38) _ validLayout0019) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind05510_0) certificate0567

private theorem bind05511_0 : Agrees (spec (fastBase 1 4 39) layout0019) scope0525 := by decide

theorem reject05511 : Rejected (base 1 4 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 39) _ validLayout0019) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind05511_0) certificate0567

private theorem bind05512_0 : Agrees (spec (fastBase 1 4 40) layout0019) scope0525 := by decide

theorem reject05512 : Rejected (base 1 4 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 40) _ validLayout0019) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind05512_0) certificate0567

private theorem bind05513_0 : Agrees (spec (fastBase 1 4 41) layout0019) scope0525 := by decide

theorem reject05513 : Rejected (base 1 4 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 41) _ validLayout0019) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind05513_0) certificate0567

private theorem bind05514_0 : Agrees (spec (fastBase 1 4 42) layout0020) scope0114 := by decide

private theorem bind05514_1 : Agrees (spec (fastBase 1 4 42) layout0021) scope0532 := by decide

theorem reject05514 : Rejected (base 1 4 42) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 42) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 42) _ validLayout0021) (by decide) (by decide) scope0114 scope0532 (by rw [← fastBase_exact]; exact bind05514_0) (by rw [← fastBase_exact]; exact bind05514_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0574 (by decide)

private theorem bind05515_0 : Agrees (spec (fastBase 1 4 43) layout0020) scope0114 := by decide

private theorem bind05515_1 : Agrees (spec (fastBase 1 4 43) layout0021) scope0533 := by decide

theorem reject05515 : Rejected (base 1 4 43) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 43) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 43) _ validLayout0021) (by decide) (by decide) scope0114 scope0533 (by rw [← fastBase_exact]; exact bind05515_0) (by rw [← fastBase_exact]; exact bind05515_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0575 (by decide)

private theorem bind05516_0 : Agrees (spec (fastBase 1 4 44) layout0022) scope0133 := by decide

theorem reject05516 : Rejected (base 1 4 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 44) _ validLayout0022) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind05516_0) certificate0136

private theorem bind05517_0 : Agrees (spec (fastBase 1 4 45) layout0020) scope0116 := by decide

private theorem bind05517_1 : Agrees (spec (fastBase 1 4 45) layout0021) scope0526 := by decide

theorem reject05517 : Rejected (base 1 4 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 45) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 45) _ validLayout0021) (by decide) (by decide) scope0116 scope0526 (by rw [← fastBase_exact]; exact bind05517_0) (by rw [← fastBase_exact]; exact bind05517_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0568 (by decide)

private theorem bind05518_0 : Agrees (spec (fastBase 1 4 46) layout0020) scope0121 := by decide

theorem reject05518 : Rejected (base 1 4 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 46) _ validLayout0020) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind05518_0) certificate0124

private theorem bind05519_0 : Agrees (spec (fastBase 1 4 47) layout0019) scope0413 := by decide

theorem reject05519 : Rejected (base 1 4 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 47) _ validLayout0019) (by decide) scope0413 (by rw [← fastBase_exact]; exact bind05519_0) certificate0435

private theorem bind05520_0 : Agrees (spec (fastBase 1 4 48) layout0019) scope0417 := by decide

theorem reject05520 : Rejected (base 1 4 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 48) _ validLayout0019) (by decide) scope0417 (by rw [← fastBase_exact]; exact bind05520_0) certificate0440

private theorem bind05521_0 : Agrees (spec (fastBase 1 4 49) layout0020) scope0114 := by decide

private theorem bind05521_1 : Agrees (spec (fastBase 1 4 49) layout0021) scope0527 := by decide

theorem reject05521 : Rejected (base 1 4 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0020 layout0021 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 49) _ validLayout0020) (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 49) _ validLayout0021) (by decide) (by decide) scope0114 scope0527 (by rw [← fastBase_exact]; exact bind05521_0) (by rw [← fastBase_exact]; exact bind05521_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0569 (by decide)

private theorem bind05522_0 : Agrees (spec (fastBase 1 4 50) layout0019) scope0406 := by decide

theorem reject05522 : Rejected (base 1 4 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 50) _ validLayout0019) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind05522_0) certificate0423

private theorem bind05523_0 : Agrees (spec (fastBase 1 4 51) layout0019) scope0170 := by decide

theorem reject05523 : Rejected (base 1 4 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 51) _ validLayout0019) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind05523_0) certificate0173

private theorem bind05524_0 : Agrees (spec (fastBase 1 4 52) layout0019) scope0411 := by decide

theorem reject05524 : Rejected (base 1 4 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 52) _ validLayout0019) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind05524_0) certificate0431

private theorem bind05525_0 : Agrees (spec (fastBase 1 4 53) layout0019) scope0530 := by decide

theorem reject05525 : Rejected (base 1 4 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 53) _ validLayout0019) (by decide) scope0530 (by rw [← fastBase_exact]; exact bind05525_0) certificate0572

private theorem bind05526_0 : Agrees (spec (fastBase 1 4 54) layout0020) scope0118 := by decide

theorem reject05526 : Rejected (base 1 4 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 54) _ validLayout0020) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind05526_0) certificate0121

private theorem bind05527_0 : Agrees (spec (fastBase 1 4 55) layout0019) scope0413 := by decide

theorem reject05527 : Rejected (base 1 4 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 55) _ validLayout0019) (by decide) scope0413 (by rw [← fastBase_exact]; exact bind05527_0) certificate0435

private theorem bind05528_0 : Agrees (spec (fastBase 1 4 56) layout0019) scope0170 := by decide

theorem reject05528 : Rejected (base 1 4 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 56) _ validLayout0019) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind05528_0) certificate0173

private theorem bind05529_0 : Agrees (spec (fastBase 1 4 57) layout0019) scope0410 := by decide

theorem reject05529 : Rejected (base 1 4 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 57) _ validLayout0019) (by decide) scope0410 (by rw [← fastBase_exact]; exact bind05529_0) certificate0430

private theorem bind05530_0 : Agrees (spec (fastBase 1 4 58) layout0019) scope0406 := by decide

theorem reject05530 : Rejected (base 1 4 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 58) _ validLayout0019) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind05530_0) certificate0423

private theorem bind05531_0 : Agrees (spec (fastBase 1 4 59) layout0019) scope0412 := by decide

theorem reject05531 : Rejected (base 1 4 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 59) _ validLayout0019) (by decide) scope0412 (by rw [← fastBase_exact]; exact bind05531_0) certificate0432

private theorem bind05532_0 : Agrees (spec (fastBase 1 4 60) layout0022) scope0137 := by decide

theorem reject05532 : Rejected (base 1 4 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 60) _ validLayout0022) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind05532_0) certificate0140

private theorem bind05533_0 : Agrees (spec (fastBase 1 4 61) layout0020) scope0121 := by decide

theorem reject05533 : Rejected (base 1 4 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 61) _ validLayout0020) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind05533_0) certificate0124

private theorem bind05534_0 : Agrees (spec (fastBase 1 4 62) layout0019) scope0528 := by decide

theorem reject05534 : Rejected (base 1 4 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 62) _ validLayout0019) (by decide) scope0528 (by rw [← fastBase_exact]; exact bind05534_0) certificate0570

private theorem bind05535_0 : Agrees (spec (fastBase 1 4 63) layout0019) scope0170 := by decide

theorem reject05535 : Rejected (base 1 4 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 63) _ validLayout0019) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind05535_0) certificate0173

private theorem bind05536_0 : Agrees (spec (fastBase 1 4 64) layout0020) scope0120 := by decide

theorem reject05536 : Rejected (base 1 4 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 64) _ validLayout0020) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind05536_0) certificate0123

private theorem bind05537_0 : Agrees (spec (fastBase 1 4 65) layout0020) scope0118 := by decide

theorem reject05537 : Rejected (base 1 4 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0020 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 65) _ validLayout0020) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind05537_0) certificate0121

private theorem bind05538_0 : Agrees (spec (fastBase 1 4 66) layout0019) scope0412 := by decide

theorem reject05538 : Rejected (base 1 4 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 66) _ validLayout0019) (by decide) scope0412 (by rw [← fastBase_exact]; exact bind05538_0) certificate0432

private theorem bind05539_0 : Agrees (spec (fastBase 1 4 67) layout0019) scope0524 := by decide

theorem reject05539 : Rejected (base 1 4 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 67) _ validLayout0019) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind05539_0) certificate0566

private theorem bind05540_0 : Agrees (spec (fastBase 1 4 68) layout0019) scope0416 := by decide

theorem reject05540 : Rejected (base 1 4 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 68) _ validLayout0019) (by decide) scope0416 (by rw [← fastBase_exact]; exact bind05540_0) certificate0439

private theorem bind05541_0 : Agrees (spec (fastBase 1 4 69) layout0022) scope0400 := by decide

theorem reject05541 : Rejected (base 1 4 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0022 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 69) _ validLayout0022) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind05541_0) certificate0413

private theorem bind05542_0 : Agrees (spec (fastBase 1 4 70) layout0019) scope0406 := by decide

theorem reject05542 : Rejected (base 1 4 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 70) _ validLayout0019) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind05542_0) certificate0423

private theorem bind05543_0 : Agrees (spec (fastBase 1 4 71) layout0019) scope0417 := by decide

theorem reject05543 : Rejected (base 1 4 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0019 (layoutValid_of_refines _ _ (base_refines_skeleton 1 4 71) _ validLayout0019) (by decide) scope0417 (by rw [← fastBase_exact]; exact bind05543_0) certificate0440

theorem allCases076 : ∀ y : Fin 72, Rejected (base 1 4 y) := by
  intro y
  fin_cases y

  · exact reject05472

  · exact reject05473

  · exact reject05474

  · exact reject05475

  · exact reject05476

  · exact reject05477

  · exact reject05478

  · exact reject05479

  · exact reject05480

  · exact reject05481

  · exact reject05482

  · exact reject05483

  · exact reject05484

  · exact reject05485

  · exact reject05486

  · exact reject05487

  · exact reject05488

  · exact reject05489

  · exact reject05490

  · exact reject05491

  · exact reject05492

  · exact reject05493

  · exact reject05494

  · exact reject05495

  · exact reject05496

  · exact reject05497

  · exact reject05498

  · exact reject05499

  · exact reject05500

  · exact reject05501

  · exact reject05502

  · exact reject05503

  · exact reject05504

  · exact reject05505

  · exact reject05506

  · exact reject05507

  · exact reject05508

  · exact reject05509

  · exact reject05510

  · exact reject05511

  · exact reject05512

  · exact reject05513

  · exact reject05514

  · exact reject05515

  · exact reject05516

  · exact reject05517

  · exact reject05518

  · exact reject05519

  · exact reject05520

  · exact reject05521

  · exact reject05522

  · exact reject05523

  · exact reject05524

  · exact reject05525

  · exact reject05526

  · exact reject05527

  · exact reject05528

  · exact reject05529

  · exact reject05530

  · exact reject05531

  · exact reject05532

  · exact reject05533

  · exact reject05534

  · exact reject05535

  · exact reject05536

  · exact reject05537

  · exact reject05538

  · exact reject05539

  · exact reject05540

  · exact reject05541

  · exact reject05542

  · exact reject05543

end PricingIntegration.RemainingGWitnesses
