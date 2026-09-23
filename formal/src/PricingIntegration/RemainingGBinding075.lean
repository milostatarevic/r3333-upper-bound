import PricingIntegration.RemainingGLayouts001

import PricingIntegration.RemainingGLayouts002

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks005

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks022

import PricingIntegration.RemainingGScopeChecks023

import PricingIntegration.RemainingGScopeChecks034

import PricingIntegration.RemainingGScopeChecks035


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05400_0 : Agrees (spec (fastBase 1 3 0) layout0015) scope0368 := by decide

theorem reject05400 : Rejected (base 1 3 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 0) _ validLayout0015) (by decide) scope0368 (by rw [← fastBase_exact]; exact bind05400_0) certificate0376

private theorem bind05401_0 : Agrees (spec (fastBase 1 3 1) layout0015) scope0364 := by decide

theorem reject05401 : Rejected (base 1 3 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 1) _ validLayout0015) (by decide) scope0364 (by rw [← fastBase_exact]; exact bind05401_0) certificate0371

private theorem bind05402_0 : Agrees (spec (fastBase 1 3 2) layout0016) scope0084 := by decide

theorem reject05402 : Rejected (base 1 3 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 2) _ validLayout0016) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind05402_0) certificate0087

private theorem bind05403_0 : Agrees (spec (fastBase 1 3 3) layout0016) scope0085 := by decide

theorem reject05403 : Rejected (base 1 3 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 3) _ validLayout0016) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind05403_0) certificate0088

private theorem bind05404_0 : Agrees (spec (fastBase 1 3 4) layout0015) scope0369 := by decide

theorem reject05404 : Rejected (base 1 3 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 4) _ validLayout0015) (by decide) scope0369 (by rw [← fastBase_exact]; exact bind05404_0) certificate0377

private theorem bind05405_0 : Agrees (spec (fastBase 1 3 5) layout0015) scope0515 := by decide

theorem reject05405 : Rejected (base 1 3 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 5) _ validLayout0015) (by decide) scope0515 (by rw [← fastBase_exact]; exact bind05405_0) certificate0557

private theorem bind05406_0 : Agrees (spec (fastBase 1 3 6) layout0015) scope0370 := by decide

theorem reject05406 : Rejected (base 1 3 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 6) _ validLayout0015) (by decide) scope0370 (by rw [← fastBase_exact]; exact bind05406_0) certificate0379

private theorem bind05407_0 : Agrees (spec (fastBase 1 3 7) layout0015) scope0516 := by decide

theorem reject05407 : Rejected (base 1 3 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 7) _ validLayout0015) (by decide) scope0516 (by rw [← fastBase_exact]; exact bind05407_0) certificate0558

private theorem bind05408_0 : Agrees (spec (fastBase 1 3 8) layout0015) scope0517 := by decide

theorem reject05408 : Rejected (base 1 3 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 8) _ validLayout0015) (by decide) scope0517 (by rw [← fastBase_exact]; exact bind05408_0) certificate0559

private theorem bind05409_0 : Agrees (spec (fastBase 1 3 9) layout0015) scope0361 := by decide

theorem reject05409 : Rejected (base 1 3 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 9) _ validLayout0015) (by decide) scope0361 (by rw [← fastBase_exact]; exact bind05409_0) certificate0368

private theorem bind05410_0 : Agrees (spec (fastBase 1 3 10) layout0015) scope0049 := by decide

theorem reject05410 : Rejected (base 1 3 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 10) _ validLayout0015) (by decide) scope0049 (by rw [← fastBase_exact]; exact bind05410_0) certificate0049

private theorem bind05411_0 : Agrees (spec (fastBase 1 3 11) layout0015) scope0360 := by decide

theorem reject05411 : Rejected (base 1 3 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 11) _ validLayout0015) (by decide) scope0360 (by rw [← fastBase_exact]; exact bind05411_0) certificate0367

private theorem bind05412_0 : Agrees (spec (fastBase 1 3 12) layout0015) scope0364 := by decide

theorem reject05412 : Rejected (base 1 3 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 12) _ validLayout0015) (by decide) scope0364 (by rw [← fastBase_exact]; exact bind05412_0) certificate0371

private theorem bind05413_0 : Agrees (spec (fastBase 1 3 13) layout0015) scope0368 := by decide

theorem reject05413 : Rejected (base 1 3 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 13) _ validLayout0015) (by decide) scope0368 (by rw [← fastBase_exact]; exact bind05413_0) certificate0376

private theorem bind05414_0 : Agrees (spec (fastBase 1 3 14) layout0015) scope0515 := by decide

theorem reject05414 : Rejected (base 1 3 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 14) _ validLayout0015) (by decide) scope0515 (by rw [← fastBase_exact]; exact bind05414_0) certificate0557

private theorem bind05415_0 : Agrees (spec (fastBase 1 3 15) layout0015) scope0518 := by decide

theorem reject05415 : Rejected (base 1 3 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 15) _ validLayout0015) (by decide) scope0518 (by rw [← fastBase_exact]; exact bind05415_0) certificate0560

private theorem bind05416_0 : Agrees (spec (fastBase 1 3 16) layout0015) scope0519 := by decide

theorem reject05416 : Rejected (base 1 3 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 16) _ validLayout0015) (by decide) scope0519 (by rw [← fastBase_exact]; exact bind05416_0) certificate0561

private theorem bind05417_0 : Agrees (spec (fastBase 1 3 17) layout0015) scope0368 := by decide

theorem reject05417 : Rejected (base 1 3 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 17) _ validLayout0015) (by decide) scope0368 (by rw [← fastBase_exact]; exact bind05417_0) certificate0376

private theorem bind05418_0 : Agrees (spec (fastBase 1 3 18) layout0016) scope0083 := by decide

theorem reject05418 : Rejected (base 1 3 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 18) _ validLayout0016) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind05418_0) certificate0086

private theorem bind05419_0 : Agrees (spec (fastBase 1 3 19) layout0016) scope0098 := by decide

theorem reject05419 : Rejected (base 1 3 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 19) _ validLayout0016) (by decide) scope0098 (by rw [← fastBase_exact]; exact bind05419_0) certificate0101

private theorem bind05420_0 : Agrees (spec (fastBase 1 3 20) layout0015) scope0520 := by decide

theorem reject05420 : Rejected (base 1 3 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 20) _ validLayout0015) (by decide) scope0520 (by rw [← fastBase_exact]; exact bind05420_0) certificate0562

private theorem bind05421_0 : Agrees (spec (fastBase 1 3 21) layout0015) scope0364 := by decide

theorem reject05421 : Rejected (base 1 3 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 21) _ validLayout0015) (by decide) scope0364 (by rw [← fastBase_exact]; exact bind05421_0) certificate0371

private theorem bind05422_0 : Agrees (spec (fastBase 1 3 22) layout0016) scope0084 := by decide

theorem reject05422 : Rejected (base 1 3 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 22) _ validLayout0016) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind05422_0) certificate0087

private theorem bind05423_0 : Agrees (spec (fastBase 1 3 23) layout0016) scope0084 := by decide

theorem reject05423 : Rejected (base 1 3 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 23) _ validLayout0016) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind05423_0) certificate0087

private theorem bind05424_0 : Agrees (spec (fastBase 1 3 24) layout0016) scope0084 := by decide

theorem reject05424 : Rejected (base 1 3 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 24) _ validLayout0016) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind05424_0) certificate0087

private theorem bind05425_0 : Agrees (spec (fastBase 1 3 25) layout0016) scope0088 := by decide

theorem reject05425 : Rejected (base 1 3 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 25) _ validLayout0016) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind05425_0) certificate0091

private theorem bind05426_0 : Agrees (spec (fastBase 1 3 26) layout0016) scope0093 := by decide

theorem reject05426 : Rejected (base 1 3 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 26) _ validLayout0016) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind05426_0) certificate0096

private theorem bind05427_0 : Agrees (spec (fastBase 1 3 27) layout0015) scope0364 := by decide

theorem reject05427 : Rejected (base 1 3 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 27) _ validLayout0015) (by decide) scope0364 (by rw [← fastBase_exact]; exact bind05427_0) certificate0371

private theorem bind05428_0 : Agrees (spec (fastBase 1 3 28) layout0016) scope0085 := by decide

theorem reject05428 : Rejected (base 1 3 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 28) _ validLayout0016) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind05428_0) certificate0088

private theorem bind05429_0 : Agrees (spec (fastBase 1 3 29) layout0015) scope0518 := by decide

theorem reject05429 : Rejected (base 1 3 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 29) _ validLayout0015) (by decide) scope0518 (by rw [← fastBase_exact]; exact bind05429_0) certificate0560

private theorem bind05430_0 : Agrees (spec (fastBase 1 3 30) layout0015) scope0516 := by decide

theorem reject05430 : Rejected (base 1 3 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 30) _ validLayout0015) (by decide) scope0516 (by rw [← fastBase_exact]; exact bind05430_0) certificate0558

private theorem bind05431_0 : Agrees (spec (fastBase 1 3 31) layout0015) scope0053 := by decide

theorem reject05431 : Rejected (base 1 3 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 31) _ validLayout0015) (by decide) scope0053 (by rw [← fastBase_exact]; exact bind05431_0) certificate0055

private theorem bind05432_0 : Agrees (spec (fastBase 1 3 32) layout0015) scope0519 := by decide

theorem reject05432 : Rejected (base 1 3 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 32) _ validLayout0015) (by decide) scope0519 (by rw [← fastBase_exact]; exact bind05432_0) certificate0561

private theorem bind05433_0 : Agrees (spec (fastBase 1 3 33) layout0015) scope0369 := by decide

theorem reject05433 : Rejected (base 1 3 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 33) _ validLayout0015) (by decide) scope0369 (by rw [← fastBase_exact]; exact bind05433_0) certificate0377

private theorem bind05434_0 : Agrees (spec (fastBase 1 3 34) layout0015) scope0515 := by decide

theorem reject05434 : Rejected (base 1 3 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 34) _ validLayout0015) (by decide) scope0515 (by rw [← fastBase_exact]; exact bind05434_0) certificate0557

private theorem bind05435_0 : Agrees (spec (fastBase 1 3 35) layout0015) scope0517 := by decide

theorem reject05435 : Rejected (base 1 3 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 35) _ validLayout0015) (by decide) scope0517 (by rw [← fastBase_exact]; exact bind05435_0) certificate0559

private theorem bind05436_0 : Agrees (spec (fastBase 1 3 36) layout0015) scope0365 := by decide

theorem reject05436 : Rejected (base 1 3 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 36) _ validLayout0015) (by decide) scope0365 (by rw [← fastBase_exact]; exact bind05436_0) certificate0372

private theorem bind05437_0 : Agrees (spec (fastBase 1 3 37) layout0015) scope0368 := by decide

theorem reject05437 : Rejected (base 1 3 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 37) _ validLayout0015) (by decide) scope0368 (by rw [← fastBase_exact]; exact bind05437_0) certificate0376

private theorem bind05438_0 : Agrees (spec (fastBase 1 3 38) layout0015) scope0369 := by decide

theorem reject05438 : Rejected (base 1 3 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 38) _ validLayout0015) (by decide) scope0369 (by rw [← fastBase_exact]; exact bind05438_0) certificate0377

private theorem bind05439_0 : Agrees (spec (fastBase 1 3 39) layout0016) scope0098 := by decide

theorem reject05439 : Rejected (base 1 3 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 39) _ validLayout0016) (by decide) scope0098 (by rw [← fastBase_exact]; exact bind05439_0) certificate0101

private theorem bind05440_0 : Agrees (spec (fastBase 1 3 40) layout0015) scope0515 := by decide

theorem reject05440 : Rejected (base 1 3 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 40) _ validLayout0015) (by decide) scope0515 (by rw [← fastBase_exact]; exact bind05440_0) certificate0557

private theorem bind05441_0 : Agrees (spec (fastBase 1 3 41) layout0015) scope0521 := by decide

theorem reject05441 : Rejected (base 1 3 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 41) _ validLayout0015) (by decide) scope0521 (by rw [← fastBase_exact]; exact bind05441_0) certificate0563

private theorem bind05442_0 : Agrees (spec (fastBase 1 3 42) layout0015) scope0053 := by decide

theorem reject05442 : Rejected (base 1 3 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 42) _ validLayout0015) (by decide) scope0053 (by rw [← fastBase_exact]; exact bind05442_0) certificate0055

private theorem bind05443_0 : Agrees (spec (fastBase 1 3 43) layout0015) scope0370 := by decide

theorem reject05443 : Rejected (base 1 3 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 43) _ validLayout0015) (by decide) scope0370 (by rw [← fastBase_exact]; exact bind05443_0) certificate0379

private theorem bind05444_0 : Agrees (spec (fastBase 1 3 44) layout0015) scope0522 := by decide

theorem reject05444 : Rejected (base 1 3 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 44) _ validLayout0015) (by decide) scope0522 (by rw [← fastBase_exact]; exact bind05444_0) certificate0564

private theorem bind05445_0 : Agrees (spec (fastBase 1 3 45) layout0015) scope0516 := by decide

theorem reject05445 : Rejected (base 1 3 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 45) _ validLayout0015) (by decide) scope0516 (by rw [← fastBase_exact]; exact bind05445_0) certificate0558

private theorem bind05446_0 : Agrees (spec (fastBase 1 3 46) layout0015) scope0360 := by decide

theorem reject05446 : Rejected (base 1 3 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 46) _ validLayout0015) (by decide) scope0360 (by rw [← fastBase_exact]; exact bind05446_0) certificate0367

private theorem bind05447_0 : Agrees (spec (fastBase 1 3 47) layout0015) scope0520 := by decide

theorem reject05447 : Rejected (base 1 3 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 47) _ validLayout0015) (by decide) scope0520 (by rw [← fastBase_exact]; exact bind05447_0) certificate0562

private theorem bind05448_0 : Agrees (spec (fastBase 1 3 48) layout0016) scope0085 := by decide

theorem reject05448 : Rejected (base 1 3 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 48) _ validLayout0016) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind05448_0) certificate0088

private theorem bind05449_0 : Agrees (spec (fastBase 1 3 49) layout0015) scope0370 := by decide

theorem reject05449 : Rejected (base 1 3 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 49) _ validLayout0015) (by decide) scope0370 (by rw [← fastBase_exact]; exact bind05449_0) certificate0379

private theorem bind05450_0 : Agrees (spec (fastBase 1 3 50) layout0015) scope0516 := by decide

theorem reject05450 : Rejected (base 1 3 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 50) _ validLayout0015) (by decide) scope0516 (by rw [← fastBase_exact]; exact bind05450_0) certificate0558

private theorem bind05451_0 : Agrees (spec (fastBase 1 3 51) layout0016) scope0100 := by decide

theorem reject05451 : Rejected (base 1 3 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 51) _ validLayout0016) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind05451_0) certificate0103

private theorem bind05452_0 : Agrees (spec (fastBase 1 3 52) layout0015) scope0521 := by decide

theorem reject05452 : Rejected (base 1 3 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 52) _ validLayout0015) (by decide) scope0521 (by rw [← fastBase_exact]; exact bind05452_0) certificate0563

private theorem bind05453_0 : Agrees (spec (fastBase 1 3 53) layout0015) scope0369 := by decide

theorem reject05453 : Rejected (base 1 3 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 53) _ validLayout0015) (by decide) scope0369 (by rw [← fastBase_exact]; exact bind05453_0) certificate0377

private theorem bind05454_0 : Agrees (spec (fastBase 1 3 54) layout0015) scope0523 := by decide

theorem reject05454 : Rejected (base 1 3 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 54) _ validLayout0015) (by decide) scope0523 (by rw [← fastBase_exact]; exact bind05454_0) certificate0565

private theorem bind05455_0 : Agrees (spec (fastBase 1 3 55) layout0015) scope0517 := by decide

theorem reject05455 : Rejected (base 1 3 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 55) _ validLayout0015) (by decide) scope0517 (by rw [← fastBase_exact]; exact bind05455_0) certificate0559

private theorem bind05456_0 : Agrees (spec (fastBase 1 3 56) layout0015) scope0049 := by decide

theorem reject05456 : Rejected (base 1 3 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 56) _ validLayout0015) (by decide) scope0049 (by rw [← fastBase_exact]; exact bind05456_0) certificate0049

private theorem bind05457_0 : Agrees (spec (fastBase 1 3 57) layout0015) scope0361 := by decide

theorem reject05457 : Rejected (base 1 3 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 57) _ validLayout0015) (by decide) scope0361 (by rw [← fastBase_exact]; exact bind05457_0) certificate0368

private theorem bind05458_0 : Agrees (spec (fastBase 1 3 58) layout0015) scope0361 := by decide

theorem reject05458 : Rejected (base 1 3 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 58) _ validLayout0015) (by decide) scope0361 (by rw [← fastBase_exact]; exact bind05458_0) certificate0368

private theorem bind05459_0 : Agrees (spec (fastBase 1 3 59) layout0015) scope0361 := by decide

theorem reject05459 : Rejected (base 1 3 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 59) _ validLayout0015) (by decide) scope0361 (by rw [← fastBase_exact]; exact bind05459_0) certificate0368

private theorem bind05460_0 : Agrees (spec (fastBase 1 3 60) layout0015) scope0361 := by decide

theorem reject05460 : Rejected (base 1 3 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 60) _ validLayout0015) (by decide) scope0361 (by rw [← fastBase_exact]; exact bind05460_0) certificate0368

private theorem bind05461_0 : Agrees (spec (fastBase 1 3 61) layout0015) scope0361 := by decide

theorem reject05461 : Rejected (base 1 3 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 61) _ validLayout0015) (by decide) scope0361 (by rw [← fastBase_exact]; exact bind05461_0) certificate0368

private theorem bind05462_0 : Agrees (spec (fastBase 1 3 62) layout0015) scope0049 := by decide

theorem reject05462 : Rejected (base 1 3 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 62) _ validLayout0015) (by decide) scope0049 (by rw [← fastBase_exact]; exact bind05462_0) certificate0049

private theorem bind05463_0 : Agrees (spec (fastBase 1 3 63) layout0015) scope0365 := by decide

theorem reject05463 : Rejected (base 1 3 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 63) _ validLayout0015) (by decide) scope0365 (by rw [← fastBase_exact]; exact bind05463_0) certificate0372

private theorem bind05464_0 : Agrees (spec (fastBase 1 3 64) layout0015) scope0522 := by decide

theorem reject05464 : Rejected (base 1 3 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 64) _ validLayout0015) (by decide) scope0522 (by rw [← fastBase_exact]; exact bind05464_0) certificate0564

private theorem bind05465_0 : Agrees (spec (fastBase 1 3 65) layout0015) scope0517 := by decide

theorem reject05465 : Rejected (base 1 3 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 65) _ validLayout0015) (by decide) scope0517 (by rw [← fastBase_exact]; exact bind05465_0) certificate0559

private theorem bind05466_0 : Agrees (spec (fastBase 1 3 66) layout0015) scope0360 := by decide

theorem reject05466 : Rejected (base 1 3 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 66) _ validLayout0015) (by decide) scope0360 (by rw [← fastBase_exact]; exact bind05466_0) certificate0367

private theorem bind05467_0 : Agrees (spec (fastBase 1 3 67) layout0018) scope0503 := by decide

theorem reject05467 : Rejected (base 1 3 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0018 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 67) _ validLayout0018) (by decide) scope0503 (by rw [← fastBase_exact]; exact bind05467_0) certificate0545

private theorem bind05468_0 : Agrees (spec (fastBase 1 3 68) layout0015) scope0523 := by decide

theorem reject05468 : Rejected (base 1 3 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 68) _ validLayout0015) (by decide) scope0523 (by rw [← fastBase_exact]; exact bind05468_0) certificate0565

private theorem bind05469_0 : Agrees (spec (fastBase 1 3 69) layout0015) scope0370 := by decide

theorem reject05469 : Rejected (base 1 3 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 69) _ validLayout0015) (by decide) scope0370 (by rw [← fastBase_exact]; exact bind05469_0) certificate0379

private theorem bind05470_0 : Agrees (spec (fastBase 1 3 70) layout0015) scope0360 := by decide

theorem reject05470 : Rejected (base 1 3 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 70) _ validLayout0015) (by decide) scope0360 (by rw [← fastBase_exact]; exact bind05470_0) certificate0367

private theorem bind05471_0 : Agrees (spec (fastBase 1 3 71) layout0015) scope0049 := by decide

theorem reject05471 : Rejected (base 1 3 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 1 3 71) _ validLayout0015) (by decide) scope0049 (by rw [← fastBase_exact]; exact bind05471_0) certificate0049

theorem allCases075 : ∀ y : Fin 72, Rejected (base 1 3 y) := by
  intro y
  fin_cases y

  · exact reject05400

  · exact reject05401

  · exact reject05402

  · exact reject05403

  · exact reject05404

  · exact reject05405

  · exact reject05406

  · exact reject05407

  · exact reject05408

  · exact reject05409

  · exact reject05410

  · exact reject05411

  · exact reject05412

  · exact reject05413

  · exact reject05414

  · exact reject05415

  · exact reject05416

  · exact reject05417

  · exact reject05418

  · exact reject05419

  · exact reject05420

  · exact reject05421

  · exact reject05422

  · exact reject05423

  · exact reject05424

  · exact reject05425

  · exact reject05426

  · exact reject05427

  · exact reject05428

  · exact reject05429

  · exact reject05430

  · exact reject05431

  · exact reject05432

  · exact reject05433

  · exact reject05434

  · exact reject05435

  · exact reject05436

  · exact reject05437

  · exact reject05438

  · exact reject05439

  · exact reject05440

  · exact reject05441

  · exact reject05442

  · exact reject05443

  · exact reject05444

  · exact reject05445

  · exact reject05446

  · exact reject05447

  · exact reject05448

  · exact reject05449

  · exact reject05450

  · exact reject05451

  · exact reject05452

  · exact reject05453

  · exact reject05454

  · exact reject05455

  · exact reject05456

  · exact reject05457

  · exact reject05458

  · exact reject05459

  · exact reject05460

  · exact reject05461

  · exact reject05462

  · exact reject05463

  · exact reject05464

  · exact reject05465

  · exact reject05466

  · exact reject05467

  · exact reject05468

  · exact reject05469

  · exact reject05470

  · exact reject05471

end PricingIntegration.RemainingGWitnesses
