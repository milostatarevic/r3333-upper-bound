import PricingIntegration.RemainingGLayouts010

import PricingIntegration.RemainingGLayouts011

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks002

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks023


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind01440_0 : Agrees (spec (fastBase 0 20 0) layout0086) scope0026 := by decide

theorem reject01440 : Rejected (base 0 20 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 0) _ validLayout0086) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind01440_0) certificate0026

private theorem bind01441_0 : Agrees (spec (fastBase 0 20 1) layout0087) scope0177 := by decide

theorem reject01441 : Rejected (base 0 20 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 1) _ validLayout0087) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01441_0) certificate0180

private theorem bind01442_0 : Agrees (spec (fastBase 0 20 2) layout0087) scope0186 := by decide

theorem reject01442 : Rejected (base 0 20 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 2) _ validLayout0087) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01442_0) certificate0189

private theorem bind01443_0 : Agrees (spec (fastBase 0 20 3) layout0086) scope0029 := by decide

theorem reject01443 : Rejected (base 0 20 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 3) _ validLayout0086) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind01443_0) certificate0029

private theorem bind01444_0 : Agrees (spec (fastBase 0 20 4) layout0087) scope0184 := by decide

theorem reject01444 : Rejected (base 0 20 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 4) _ validLayout0087) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01444_0) certificate0187

private theorem bind01445_0 : Agrees (spec (fastBase 0 20 5) layout0087) scope0191 := by decide

theorem reject01445 : Rejected (base 0 20 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 5) _ validLayout0087) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01445_0) certificate0194

private theorem bind01446_0 : Agrees (spec (fastBase 0 20 6) layout0086) scope0032 := by decide

private theorem bind01446_1 : Agrees (spec (fastBase 0 20 6) layout0088) scope0034 := by decide

theorem reject01446 : Rejected (base 0 20 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 6) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 6) _ validLayout0088) (by decide) (by decide) scope0032 scope0034 (by rw [← fastBase_exact]; exact bind01446_0) (by rw [← fastBase_exact]; exact bind01446_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0050 certificate0051 (by decide)

private theorem bind01447_0 : Agrees (spec (fastBase 0 20 7) layout0086) scope0048 := by decide

private theorem bind01447_1 : Agrees (spec (fastBase 0 20 7) layout0088) scope0033 := by decide

theorem reject01447 : Rejected (base 0 20 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 7) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 7) _ validLayout0088) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind01447_0) (by rw [← fastBase_exact]; exact bind01447_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind01448_0 : Agrees (spec (fastBase 0 20 8) layout0087) scope0176 := by decide

theorem reject01448 : Rejected (base 0 20 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 8) _ validLayout0087) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01448_0) certificate0179

private theorem bind01449_0 : Agrees (spec (fastBase 0 20 9) layout0086) scope0037 := by decide

theorem reject01449 : Rejected (base 0 20 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 9) _ validLayout0086) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind01449_0) certificate0037

private theorem bind01450_0 : Agrees (spec (fastBase 0 20 10) layout0086) scope0038 := by decide

theorem reject01450 : Rejected (base 0 20 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 10) _ validLayout0086) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind01450_0) certificate0038

private theorem bind01451_0 : Agrees (spec (fastBase 0 20 11) layout0087) scope0185 := by decide

theorem reject01451 : Rejected (base 0 20 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 11) _ validLayout0087) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01451_0) certificate0188

private theorem bind01452_0 : Agrees (spec (fastBase 0 20 12) layout0087) scope0177 := by decide

theorem reject01452 : Rejected (base 0 20 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 12) _ validLayout0087) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01452_0) certificate0180

private theorem bind01453_0 : Agrees (spec (fastBase 0 20 13) layout0087) scope0192 := by decide

theorem reject01453 : Rejected (base 0 20 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 13) _ validLayout0087) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind01453_0) certificate0195

private theorem bind01454_0 : Agrees (spec (fastBase 0 20 14) layout0087) scope0200 := by decide

theorem reject01454 : Rejected (base 0 20 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 14) _ validLayout0087) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind01454_0) certificate0203

private theorem bind01455_0 : Agrees (spec (fastBase 0 20 15) layout0086) scope0026 := by decide

theorem reject01455 : Rejected (base 0 20 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 15) _ validLayout0086) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind01455_0) certificate0026

private theorem bind01456_0 : Agrees (spec (fastBase 0 20 16) layout0087) scope0176 := by decide

theorem reject01456 : Rejected (base 0 20 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 16) _ validLayout0087) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01456_0) certificate0179

private theorem bind01457_0 : Agrees (spec (fastBase 0 20 17) layout0086) scope0026 := by decide

theorem reject01457 : Rejected (base 0 20 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 17) _ validLayout0086) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind01457_0) certificate0026

private theorem bind01458_0 : Agrees (spec (fastBase 0 20 18) layout0087) scope0199 := by decide

theorem reject01458 : Rejected (base 0 20 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 18) _ validLayout0087) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind01458_0) certificate0202

private theorem bind01459_0 : Agrees (spec (fastBase 0 20 19) layout0087) scope0177 := by decide

theorem reject01459 : Rejected (base 0 20 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 19) _ validLayout0087) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01459_0) certificate0180

private theorem bind01460_0 : Agrees (spec (fastBase 0 20 20) layout0086) scope0027 := by decide

theorem reject01460 : Rejected (base 0 20 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 20) _ validLayout0086) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind01460_0) certificate0027

private theorem bind01461_0 : Agrees (spec (fastBase 0 20 21) layout0087) scope0194 := by decide

theorem reject01461 : Rejected (base 0 20 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 21) _ validLayout0087) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind01461_0) certificate0197

private theorem bind01462_0 : Agrees (spec (fastBase 0 20 22) layout0087) scope0199 := by decide

theorem reject01462 : Rejected (base 0 20 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 22) _ validLayout0087) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind01462_0) certificate0202

private theorem bind01463_0 : Agrees (spec (fastBase 0 20 23) layout0087) scope0186 := by decide

theorem reject01463 : Rejected (base 0 20 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 23) _ validLayout0087) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01463_0) certificate0189

private theorem bind01464_0 : Agrees (spec (fastBase 0 20 24) layout0086) scope0029 := by decide

theorem reject01464 : Rejected (base 0 20 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 24) _ validLayout0086) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind01464_0) certificate0029

private theorem bind01465_0 : Agrees (spec (fastBase 0 20 25) layout0086) scope0032 := by decide

private theorem bind01465_1 : Agrees (spec (fastBase 0 20 25) layout0088) scope0034 := by decide

theorem reject01465 : Rejected (base 0 20 25) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 25) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 25) _ validLayout0088) (by decide) (by decide) scope0032 scope0034 (by rw [← fastBase_exact]; exact bind01465_0) (by rw [← fastBase_exact]; exact bind01465_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0050 certificate0051 (by decide)

private theorem bind01466_0 : Agrees (spec (fastBase 0 20 26) layout0087) scope0202 := by decide

theorem reject01466 : Rejected (base 0 20 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 26) _ validLayout0087) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind01466_0) certificate0205

private theorem bind01467_0 : Agrees (spec (fastBase 0 20 27) layout0087) scope0193 := by decide

theorem reject01467 : Rejected (base 0 20 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 27) _ validLayout0087) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind01467_0) certificate0196

private theorem bind01468_0 : Agrees (spec (fastBase 0 20 28) layout0087) scope0186 := by decide

theorem reject01468 : Rejected (base 0 20 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 28) _ validLayout0087) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01468_0) certificate0189

private theorem bind01469_0 : Agrees (spec (fastBase 0 20 29) layout0087) scope0207 := by decide

theorem reject01469 : Rejected (base 0 20 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 29) _ validLayout0087) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind01469_0) certificate0210

private theorem bind01470_0 : Agrees (spec (fastBase 0 20 30) layout0086) scope0048 := by decide

private theorem bind01470_1 : Agrees (spec (fastBase 0 20 30) layout0088) scope0033 := by decide

theorem reject01470 : Rejected (base 0 20 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 30) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 30) _ validLayout0088) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind01470_0) (by rw [← fastBase_exact]; exact bind01470_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind01471_0 : Agrees (spec (fastBase 0 20 31) layout0087) scope0185 := by decide

theorem reject01471 : Rejected (base 0 20 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 31) _ validLayout0087) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01471_0) certificate0188

private theorem bind01472_0 : Agrees (spec (fastBase 0 20 32) layout0087) scope0184 := by decide

theorem reject01472 : Rejected (base 0 20 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 32) _ validLayout0087) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01472_0) certificate0187

private theorem bind01473_0 : Agrees (spec (fastBase 0 20 33) layout0087) scope0184 := by decide

theorem reject01473 : Rejected (base 0 20 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 33) _ validLayout0087) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01473_0) certificate0187

private theorem bind01474_0 : Agrees (spec (fastBase 0 20 34) layout0087) scope0184 := by decide

theorem reject01474 : Rejected (base 0 20 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 34) _ validLayout0087) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01474_0) certificate0187

private theorem bind01475_0 : Agrees (spec (fastBase 0 20 35) layout0087) scope0184 := by decide

theorem reject01475 : Rejected (base 0 20 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 35) _ validLayout0087) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01475_0) certificate0187

private theorem bind01476_0 : Agrees (spec (fastBase 0 20 36) layout0087) scope0184 := by decide

theorem reject01476 : Rejected (base 0 20 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 36) _ validLayout0087) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind01476_0) certificate0187

private theorem bind01477_0 : Agrees (spec (fastBase 0 20 37) layout0087) scope0196 := by decide

theorem reject01477 : Rejected (base 0 20 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 37) _ validLayout0087) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind01477_0) certificate0199

private theorem bind01478_0 : Agrees (spec (fastBase 0 20 38) layout0087) scope0191 := by decide

theorem reject01478 : Rejected (base 0 20 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 38) _ validLayout0087) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01478_0) certificate0194

private theorem bind01479_0 : Agrees (spec (fastBase 0 20 39) layout0087) scope0203 := by decide

theorem reject01479 : Rejected (base 0 20 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 39) _ validLayout0087) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind01479_0) certificate0206

private theorem bind01480_0 : Agrees (spec (fastBase 0 20 40) layout0086) scope0037 := by decide

theorem reject01480 : Rejected (base 0 20 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 40) _ validLayout0086) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind01480_0) certificate0037

private theorem bind01481_0 : Agrees (spec (fastBase 0 20 41) layout0086) scope0031 := by decide

theorem reject01481 : Rejected (base 0 20 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 41) _ validLayout0086) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind01481_0) certificate0031

private theorem bind01482_0 : Agrees (spec (fastBase 0 20 42) layout0087) scope0177 := by decide

theorem reject01482 : Rejected (base 0 20 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 42) _ validLayout0087) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind01482_0) certificate0180

private theorem bind01483_0 : Agrees (spec (fastBase 0 20 43) layout0087) scope0186 := by decide

theorem reject01483 : Rejected (base 0 20 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 43) _ validLayout0087) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind01483_0) certificate0189

private theorem bind01484_0 : Agrees (spec (fastBase 0 20 44) layout0087) scope0192 := by decide

theorem reject01484 : Rejected (base 0 20 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 44) _ validLayout0087) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind01484_0) certificate0195

private theorem bind01485_0 : Agrees (spec (fastBase 0 20 45) layout0089) scope0367 := by decide

private theorem bind01485_1 : Agrees (spec (fastBase 0 20 45) layout0090) scope0035 := by decide

theorem reject01485 : Rejected (base 0 20 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0089 layout0090 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 45) _ validLayout0089) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 45) _ validLayout0090) (by decide) (by decide) scope0367 scope0035 (by rw [← fastBase_exact]; exact bind01485_0) (by rw [← fastBase_exact]; exact bind01485_1) 3 8 2 7 (by decide) (by decide) 3 2 (by decide) certificate0374 certificate0375 (by decide)

private theorem bind01486_0 : Agrees (spec (fastBase 0 20 46) layout0087) scope0193 := by decide

theorem reject01486 : Rejected (base 0 20 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 46) _ validLayout0087) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind01486_0) certificate0196

private theorem bind01487_0 : Agrees (spec (fastBase 0 20 47) layout0086) scope0048 := by decide

private theorem bind01487_1 : Agrees (spec (fastBase 0 20 47) layout0088) scope0033 := by decide

theorem reject01487 : Rejected (base 0 20 47) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 47) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 47) _ validLayout0088) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind01487_0) (by rw [← fastBase_exact]; exact bind01487_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind01488_0 : Agrees (spec (fastBase 0 20 48) layout0086) scope0029 := by decide

theorem reject01488 : Rejected (base 0 20 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 48) _ validLayout0086) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind01488_0) certificate0029

private theorem bind01489_0 : Agrees (spec (fastBase 0 20 49) layout0086) scope0032 := by decide

private theorem bind01489_1 : Agrees (spec (fastBase 0 20 49) layout0088) scope0033 := by decide

theorem reject01489 : Rejected (base 0 20 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 49) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 49) _ validLayout0088) (by decide) (by decide) scope0032 scope0033 (by rw [← fastBase_exact]; exact bind01489_0) (by rw [← fastBase_exact]; exact bind01489_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0032 certificate0033 (by decide)

private theorem bind01490_0 : Agrees (spec (fastBase 0 20 50) layout0086) scope0042 := by decide

theorem reject01490 : Rejected (base 0 20 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 50) _ validLayout0086) (by decide) scope0042 (by rw [← fastBase_exact]; exact bind01490_0) certificate0042

private theorem bind01491_0 : Agrees (spec (fastBase 0 20 51) layout0086) scope0043 := by decide

theorem reject01491 : Rejected (base 0 20 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 51) _ validLayout0086) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind01491_0) certificate0043

private theorem bind01492_0 : Agrees (spec (fastBase 0 20 52) layout0088) scope0368 := by decide

theorem reject01492 : Rejected (base 0 20 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 52) _ validLayout0088) (by decide) scope0368 (by rw [← fastBase_exact]; exact bind01492_0) certificate0376

private theorem bind01493_0 : Agrees (spec (fastBase 0 20 53) layout0087) scope0176 := by decide

theorem reject01493 : Rejected (base 0 20 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 53) _ validLayout0087) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01493_0) certificate0179

private theorem bind01494_0 : Agrees (spec (fastBase 0 20 54) layout0087) scope0194 := by decide

theorem reject01494 : Rejected (base 0 20 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 54) _ validLayout0087) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind01494_0) certificate0197

private theorem bind01495_0 : Agrees (spec (fastBase 0 20 55) layout0086) scope0037 := by decide

theorem reject01495 : Rejected (base 0 20 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 55) _ validLayout0086) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind01495_0) certificate0037

private theorem bind01496_0 : Agrees (spec (fastBase 0 20 56) layout0087) scope0196 := by decide

theorem reject01496 : Rejected (base 0 20 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 56) _ validLayout0087) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind01496_0) certificate0199

private theorem bind01497_0 : Agrees (spec (fastBase 0 20 57) layout0087) scope0200 := by decide

theorem reject01497 : Rejected (base 0 20 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 57) _ validLayout0087) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind01497_0) certificate0203

private theorem bind01498_0 : Agrees (spec (fastBase 0 20 58) layout0087) scope0191 := by decide

theorem reject01498 : Rejected (base 0 20 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 58) _ validLayout0087) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01498_0) certificate0194

private theorem bind01499_0 : Agrees (spec (fastBase 0 20 59) layout0087) scope0176 := by decide

theorem reject01499 : Rejected (base 0 20 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 59) _ validLayout0087) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind01499_0) certificate0179

private theorem bind01500_0 : Agrees (spec (fastBase 0 20 60) layout0088) scope0369 := by decide

theorem reject01500 : Rejected (base 0 20 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 60) _ validLayout0088) (by decide) scope0369 (by rw [← fastBase_exact]; exact bind01500_0) certificate0377

private theorem bind01501_0 : Agrees (spec (fastBase 0 20 61) layout0087) scope0201 := by decide

theorem reject01501 : Rejected (base 0 20 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 61) _ validLayout0087) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind01501_0) certificate0204

private theorem bind01502_0 : Agrees (spec (fastBase 0 20 62) layout0087) scope0207 := by decide

theorem reject01502 : Rejected (base 0 20 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 62) _ validLayout0087) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind01502_0) certificate0210

private theorem bind01503_0 : Agrees (spec (fastBase 0 20 63) layout0087) scope0191 := by decide

theorem reject01503 : Rejected (base 0 20 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 63) _ validLayout0087) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind01503_0) certificate0194

private theorem bind01504_0 : Agrees (spec (fastBase 0 20 64) layout0086) scope0351 := by decide

private theorem bind01504_1 : Agrees (spec (fastBase 0 20 64) layout0088) scope0033 := by decide

theorem reject01504 : Rejected (base 0 20 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 64) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 64) _ validLayout0088) (by decide) (by decide) scope0351 scope0033 (by rw [← fastBase_exact]; exact bind01504_0) (by rw [← fastBase_exact]; exact bind01504_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0378 certificate0033 (by decide)

private theorem bind01505_0 : Agrees (spec (fastBase 0 20 65) layout0087) scope0201 := by decide

theorem reject01505 : Rejected (base 0 20 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 65) _ validLayout0087) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind01505_0) certificate0204

private theorem bind01506_0 : Agrees (spec (fastBase 0 20 66) layout0087) scope0185 := by decide

theorem reject01506 : Rejected (base 0 20 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 66) _ validLayout0087) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01506_0) certificate0188

private theorem bind01507_0 : Agrees (spec (fastBase 0 20 67) layout0088) scope0370 := by decide

theorem reject01507 : Rejected (base 0 20 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 67) _ validLayout0088) (by decide) scope0370 (by rw [← fastBase_exact]; exact bind01507_0) certificate0379

private theorem bind01508_0 : Agrees (spec (fastBase 0 20 68) layout0087) scope0185 := by decide

theorem reject01508 : Rejected (base 0 20 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 68) _ validLayout0087) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind01508_0) certificate0188

private theorem bind01509_0 : Agrees (spec (fastBase 0 20 69) layout0087) scope0202 := by decide

theorem reject01509 : Rejected (base 0 20 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 69) _ validLayout0087) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind01509_0) certificate0205

private theorem bind01510_0 : Agrees (spec (fastBase 0 20 70) layout0087) scope0203 := by decide

theorem reject01510 : Rejected (base 0 20 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 70) _ validLayout0087) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind01510_0) certificate0206

private theorem bind01511_0 : Agrees (spec (fastBase 0 20 71) layout0086) scope0038 := by decide

theorem reject01511 : Rejected (base 0 20 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 0 20 71) _ validLayout0086) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind01511_0) certificate0038

theorem allCases020 : ∀ y : Fin 72, Rejected (base 0 20 y) := by
  intro y
  fin_cases y

  · exact reject01440

  · exact reject01441

  · exact reject01442

  · exact reject01443

  · exact reject01444

  · exact reject01445

  · exact reject01446

  · exact reject01447

  · exact reject01448

  · exact reject01449

  · exact reject01450

  · exact reject01451

  · exact reject01452

  · exact reject01453

  · exact reject01454

  · exact reject01455

  · exact reject01456

  · exact reject01457

  · exact reject01458

  · exact reject01459

  · exact reject01460

  · exact reject01461

  · exact reject01462

  · exact reject01463

  · exact reject01464

  · exact reject01465

  · exact reject01466

  · exact reject01467

  · exact reject01468

  · exact reject01469

  · exact reject01470

  · exact reject01471

  · exact reject01472

  · exact reject01473

  · exact reject01474

  · exact reject01475

  · exact reject01476

  · exact reject01477

  · exact reject01478

  · exact reject01479

  · exact reject01480

  · exact reject01481

  · exact reject01482

  · exact reject01483

  · exact reject01484

  · exact reject01485

  · exact reject01486

  · exact reject01487

  · exact reject01488

  · exact reject01489

  · exact reject01490

  · exact reject01491

  · exact reject01492

  · exact reject01493

  · exact reject01494

  · exact reject01495

  · exact reject01496

  · exact reject01497

  · exact reject01498

  · exact reject01499

  · exact reject01500

  · exact reject01501

  · exact reject01502

  · exact reject01503

  · exact reject01504

  · exact reject01505

  · exact reject01506

  · exact reject01507

  · exact reject01508

  · exact reject01509

  · exact reject01510

  · exact reject01511

end PricingIntegration.RemainingGWitnesses
