import PricingIntegration.RemainingGLayouts003

import PricingIntegration.RemainingGLayouts004

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00432_0 : Agrees (spec (fastBase 0 6 0) layout0029) scope0174 := by decide

private theorem bind00432_1 : Agrees (spec (fastBase 0 6 0) layout0030) scope0175 := by decide

theorem reject00432 : Rejected (base 0 6 0) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 0) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 0) _ validLayout0030) (by decide) (by decide) scope0174 scope0175 (by rw [← fastBase_exact]; exact bind00432_0) (by rw [← fastBase_exact]; exact bind00432_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0177 certificate0178 (by decide)

private theorem bind00433_0 : Agrees (spec (fastBase 0 6 1) layout0031) scope0176 := by decide

theorem reject00433 : Rejected (base 0 6 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 1) _ validLayout0031) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind00433_0) certificate0179

private theorem bind00434_0 : Agrees (spec (fastBase 0 6 2) layout0031) scope0177 := by decide

theorem reject00434 : Rejected (base 0 6 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 2) _ validLayout0031) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind00434_0) certificate0180

private theorem bind00435_0 : Agrees (spec (fastBase 0 6 3) layout0029) scope0178 := by decide

private theorem bind00435_1 : Agrees (spec (fastBase 0 6 3) layout0030) scope0179 := by decide

theorem reject00435 : Rejected (base 0 6 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 3) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 3) _ validLayout0030) (by decide) (by decide) scope0178 scope0179 (by rw [← fastBase_exact]; exact bind00435_0) (by rw [← fastBase_exact]; exact bind00435_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0181 certificate0182 (by decide)

private theorem bind00436_0 : Agrees (spec (fastBase 0 6 4) layout0032) scope0180 := by decide

private theorem bind00436_1 : Agrees (spec (fastBase 0 6 4) layout0030) scope0181 := by decide

theorem reject00436 : Rejected (base 0 6 4) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0032 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 4) _ validLayout0032) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 4) _ validLayout0030) (by decide) (by decide) scope0180 scope0181 (by rw [← fastBase_exact]; exact bind00436_0) (by rw [← fastBase_exact]; exact bind00436_1) 3 8 7 2 (by decide) (by decide) 3 2 (by decide) certificate0183 certificate0184 (by decide)

private theorem bind00437_0 : Agrees (spec (fastBase 0 6 5) layout0029) scope0182 := by decide

private theorem bind00437_1 : Agrees (spec (fastBase 0 6 5) layout0030) scope0183 := by decide

theorem reject00437 : Rejected (base 0 6 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 5) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 5) _ validLayout0030) (by decide) (by decide) scope0182 scope0183 (by rw [← fastBase_exact]; exact bind00437_0) (by rw [← fastBase_exact]; exact bind00437_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0186 (by decide)

private theorem bind00438_0 : Agrees (spec (fastBase 0 6 6) layout0031) scope0184 := by decide

theorem reject00438 : Rejected (base 0 6 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 6) _ validLayout0031) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind00438_0) certificate0187

private theorem bind00439_0 : Agrees (spec (fastBase 0 6 7) layout0031) scope0185 := by decide

theorem reject00439 : Rejected (base 0 6 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 7) _ validLayout0031) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind00439_0) certificate0188

private theorem bind00440_0 : Agrees (spec (fastBase 0 6 8) layout0031) scope0186 := by decide

theorem reject00440 : Rejected (base 0 6 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 8) _ validLayout0031) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind00440_0) certificate0189

private theorem bind00441_0 : Agrees (spec (fastBase 0 6 9) layout0033) scope0187 := by decide

private theorem bind00441_1 : Agrees (spec (fastBase 0 6 9) layout0030) scope0188 := by decide

theorem reject00441 : Rejected (base 0 6 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0033 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 9) _ validLayout0033) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 9) _ validLayout0030) (by decide) (by decide) scope0187 scope0188 (by rw [← fastBase_exact]; exact bind00441_0) (by rw [← fastBase_exact]; exact bind00441_1) 3 8 6 1 (by decide) (by decide) 3 2 (by decide) certificate0190 certificate0191 (by decide)

private theorem bind00442_0 : Agrees (spec (fastBase 0 6 10) layout0029) scope0189 := by decide

private theorem bind00442_1 : Agrees (spec (fastBase 0 6 10) layout0030) scope0190 := by decide

theorem reject00442 : Rejected (base 0 6 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 10) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 10) _ validLayout0030) (by decide) (by decide) scope0189 scope0190 (by rw [← fastBase_exact]; exact bind00442_0) (by rw [← fastBase_exact]; exact bind00442_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0192 certificate0193 (by decide)

private theorem bind00443_0 : Agrees (spec (fastBase 0 6 11) layout0031) scope0191 := by decide

theorem reject00443 : Rejected (base 0 6 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 11) _ validLayout0031) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind00443_0) certificate0194

private theorem bind00444_0 : Agrees (spec (fastBase 0 6 12) layout0031) scope0192 := by decide

theorem reject00444 : Rejected (base 0 6 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 12) _ validLayout0031) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind00444_0) certificate0195

private theorem bind00445_0 : Agrees (spec (fastBase 0 6 13) layout0031) scope0177 := by decide

theorem reject00445 : Rejected (base 0 6 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 13) _ validLayout0031) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind00445_0) certificate0180

private theorem bind00446_0 : Agrees (spec (fastBase 0 6 14) layout0029) scope0182 := by decide

private theorem bind00446_1 : Agrees (spec (fastBase 0 6 14) layout0030) scope0183 := by decide

theorem reject00446 : Rejected (base 0 6 14) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 14) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 14) _ validLayout0030) (by decide) (by decide) scope0182 scope0183 (by rw [← fastBase_exact]; exact bind00446_0) (by rw [← fastBase_exact]; exact bind00446_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0186 (by decide)

private theorem bind00447_0 : Agrees (spec (fastBase 0 6 15) layout0031) scope0193 := by decide

theorem reject00447 : Rejected (base 0 6 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 15) _ validLayout0031) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind00447_0) certificate0196

private theorem bind00448_0 : Agrees (spec (fastBase 0 6 16) layout0031) scope0186 := by decide

theorem reject00448 : Rejected (base 0 6 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 16) _ validLayout0031) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind00448_0) certificate0189

private theorem bind00449_0 : Agrees (spec (fastBase 0 6 17) layout0031) scope0194 := by decide

theorem reject00449 : Rejected (base 0 6 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 17) _ validLayout0031) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind00449_0) certificate0197

private theorem bind00450_0 : Agrees (spec (fastBase 0 6 18) layout0033) scope0195 := by decide

theorem reject00450 : Rejected (base 0 6 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0033 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 18) _ validLayout0033) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind00450_0) certificate0198

private theorem bind00451_0 : Agrees (spec (fastBase 0 6 19) layout0029) scope0176 := by decide

theorem reject00451 : Rejected (base 0 6 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 19) _ validLayout0029) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind00451_0) certificate0179

private theorem bind00452_0 : Agrees (spec (fastBase 0 6 20) layout0031) scope0176 := by decide

theorem reject00452 : Rejected (base 0 6 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 20) _ validLayout0031) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind00452_0) certificate0179

private theorem bind00453_0 : Agrees (spec (fastBase 0 6 21) layout0031) scope0196 := by decide

theorem reject00453 : Rejected (base 0 6 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 21) _ validLayout0031) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind00453_0) certificate0199

private theorem bind00454_0 : Agrees (spec (fastBase 0 6 22) layout0033) scope0197 := by decide

theorem reject00454 : Rejected (base 0 6 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0033 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 22) _ validLayout0033) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind00454_0) certificate0200

private theorem bind00455_0 : Agrees (spec (fastBase 0 6 23) layout0034) scope0198 := by decide

theorem reject00455 : Rejected (base 0 6 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0034 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 23) _ validLayout0034) (by decide) scope0198 (by rw [← fastBase_exact]; exact bind00455_0) certificate0201

private theorem bind00456_0 : Agrees (spec (fastBase 0 6 24) layout0031) scope0194 := by decide

theorem reject00456 : Rejected (base 0 6 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 24) _ validLayout0031) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind00456_0) certificate0197

private theorem bind00457_0 : Agrees (spec (fastBase 0 6 25) layout0031) scope0177 := by decide

theorem reject00457 : Rejected (base 0 6 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 25) _ validLayout0031) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind00457_0) certificate0180

private theorem bind00458_0 : Agrees (spec (fastBase 0 6 26) layout0031) scope0199 := by decide

theorem reject00458 : Rejected (base 0 6 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 26) _ validLayout0031) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind00458_0) certificate0202

private theorem bind00459_0 : Agrees (spec (fastBase 0 6 27) layout0031) scope0176 := by decide

theorem reject00459 : Rejected (base 0 6 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 27) _ validLayout0031) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind00459_0) certificate0179

private theorem bind00460_0 : Agrees (spec (fastBase 0 6 28) layout0031) scope0200 := by decide

theorem reject00460 : Rejected (base 0 6 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 28) _ validLayout0031) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind00460_0) certificate0203

private theorem bind00461_0 : Agrees (spec (fastBase 0 6 29) layout0029) scope0178 := by decide

private theorem bind00461_1 : Agrees (spec (fastBase 0 6 29) layout0030) scope0183 := by decide

theorem reject00461 : Rejected (base 0 6 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 29) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 29) _ validLayout0030) (by decide) (by decide) scope0178 scope0183 (by rw [← fastBase_exact]; exact bind00461_0) (by rw [← fastBase_exact]; exact bind00461_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0181 certificate0186 (by decide)

private theorem bind00462_0 : Agrees (spec (fastBase 0 6 30) layout0031) scope0201 := by decide

theorem reject00462 : Rejected (base 0 6 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 30) _ validLayout0031) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind00462_0) certificate0204

private theorem bind00463_0 : Agrees (spec (fastBase 0 6 31) layout0031) scope0191 := by decide

theorem reject00463 : Rejected (base 0 6 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 31) _ validLayout0031) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind00463_0) certificate0194

private theorem bind00464_0 : Agrees (spec (fastBase 0 6 32) layout0031) scope0176 := by decide

theorem reject00464 : Rejected (base 0 6 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 32) _ validLayout0031) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind00464_0) certificate0179

private theorem bind00465_0 : Agrees (spec (fastBase 0 6 33) layout0031) scope0177 := by decide

theorem reject00465 : Rejected (base 0 6 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 33) _ validLayout0031) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind00465_0) certificate0180

private theorem bind00466_0 : Agrees (spec (fastBase 0 6 34) layout0029) scope0182 := by decide

private theorem bind00466_1 : Agrees (spec (fastBase 0 6 34) layout0030) scope0183 := by decide

theorem reject00466 : Rejected (base 0 6 34) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 34) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 34) _ validLayout0030) (by decide) (by decide) scope0182 scope0183 (by rw [← fastBase_exact]; exact bind00466_0) (by rw [← fastBase_exact]; exact bind00466_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0186 (by decide)

private theorem bind00467_0 : Agrees (spec (fastBase 0 6 35) layout0031) scope0192 := by decide

theorem reject00467 : Rejected (base 0 6 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 35) _ validLayout0031) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind00467_0) certificate0195

private theorem bind00468_0 : Agrees (spec (fastBase 0 6 36) layout0031) scope0200 := by decide

theorem reject00468 : Rejected (base 0 6 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 36) _ validLayout0031) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind00468_0) certificate0203

private theorem bind00469_0 : Agrees (spec (fastBase 0 6 37) layout0029) scope0174 := by decide

private theorem bind00469_1 : Agrees (spec (fastBase 0 6 37) layout0030) scope0175 := by decide

theorem reject00469 : Rejected (base 0 6 37) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 37) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 37) _ validLayout0030) (by decide) (by decide) scope0174 scope0175 (by rw [← fastBase_exact]; exact bind00469_0) (by rw [← fastBase_exact]; exact bind00469_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0177 certificate0178 (by decide)

private theorem bind00470_0 : Agrees (spec (fastBase 0 6 38) layout0032) scope0180 := by decide

private theorem bind00470_1 : Agrees (spec (fastBase 0 6 38) layout0030) scope0181 := by decide

theorem reject00470 : Rejected (base 0 6 38) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0032 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 38) _ validLayout0032) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 38) _ validLayout0030) (by decide) (by decide) scope0180 scope0181 (by rw [← fastBase_exact]; exact bind00470_0) (by rw [← fastBase_exact]; exact bind00470_1) 3 8 7 2 (by decide) (by decide) 3 2 (by decide) certificate0183 certificate0184 (by decide)

private theorem bind00471_0 : Agrees (spec (fastBase 0 6 39) layout0029) scope0182 := by decide

private theorem bind00471_1 : Agrees (spec (fastBase 0 6 39) layout0030) scope0179 := by decide

theorem reject00471 : Rejected (base 0 6 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 39) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 39) _ validLayout0030) (by decide) (by decide) scope0182 scope0179 (by rw [← fastBase_exact]; exact bind00471_0) (by rw [← fastBase_exact]; exact bind00471_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0182 (by decide)

private theorem bind00472_0 : Agrees (spec (fastBase 0 6 40) layout0033) scope0187 := by decide

private theorem bind00472_1 : Agrees (spec (fastBase 0 6 40) layout0030) scope0188 := by decide

theorem reject00472 : Rejected (base 0 6 40) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0033 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 40) _ validLayout0033) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 40) _ validLayout0030) (by decide) (by decide) scope0187 scope0188 (by rw [← fastBase_exact]; exact bind00472_0) (by rw [← fastBase_exact]; exact bind00472_1) 3 8 6 1 (by decide) (by decide) 3 2 (by decide) certificate0190 certificate0191 (by decide)

private theorem bind00473_0 : Agrees (spec (fastBase 0 6 41) layout0029) scope0182 := by decide

private theorem bind00473_1 : Agrees (spec (fastBase 0 6 41) layout0030) scope0190 := by decide

theorem reject00473 : Rejected (base 0 6 41) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 41) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 41) _ validLayout0030) (by decide) (by decide) scope0182 scope0190 (by rw [← fastBase_exact]; exact bind00473_0) (by rw [← fastBase_exact]; exact bind00473_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0185 certificate0193 (by decide)

private theorem bind00474_0 : Agrees (spec (fastBase 0 6 42) layout0031) scope0184 := by decide

theorem reject00474 : Rejected (base 0 6 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 42) _ validLayout0031) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind00474_0) certificate0187

private theorem bind00475_0 : Agrees (spec (fastBase 0 6 43) layout0031) scope0184 := by decide

theorem reject00475 : Rejected (base 0 6 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 43) _ validLayout0031) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind00475_0) certificate0187

private theorem bind00476_0 : Agrees (spec (fastBase 0 6 44) layout0031) scope0184 := by decide

theorem reject00476 : Rejected (base 0 6 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 44) _ validLayout0031) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind00476_0) certificate0187

private theorem bind00477_0 : Agrees (spec (fastBase 0 6 45) layout0031) scope0184 := by decide

theorem reject00477 : Rejected (base 0 6 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 45) _ validLayout0031) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind00477_0) certificate0187

private theorem bind00478_0 : Agrees (spec (fastBase 0 6 46) layout0031) scope0184 := by decide

theorem reject00478 : Rejected (base 0 6 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 46) _ validLayout0031) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind00478_0) certificate0187

private theorem bind00479_0 : Agrees (spec (fastBase 0 6 47) layout0031) scope0202 := by decide

theorem reject00479 : Rejected (base 0 6 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 47) _ validLayout0031) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind00479_0) certificate0205

private theorem bind00480_0 : Agrees (spec (fastBase 0 6 48) layout0031) scope0203 := by decide

theorem reject00480 : Rejected (base 0 6 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 48) _ validLayout0031) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind00480_0) certificate0206

private theorem bind00481_0 : Agrees (spec (fastBase 0 6 49) layout0031) scope0185 := by decide

theorem reject00481 : Rejected (base 0 6 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 49) _ validLayout0031) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind00481_0) certificate0188

private theorem bind00482_0 : Agrees (spec (fastBase 0 6 50) layout0034) scope0204 := by decide

theorem reject00482 : Rejected (base 0 6 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0034 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 50) _ validLayout0034) (by decide) scope0204 (by rw [← fastBase_exact]; exact bind00482_0) certificate0207

private theorem bind00483_0 : Agrees (spec (fastBase 0 6 51) layout0029) scope0185 := by decide

theorem reject00483 : Rejected (base 0 6 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 51) _ validLayout0029) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind00483_0) certificate0188

private theorem bind00484_0 : Agrees (spec (fastBase 0 6 52) layout0029) scope0186 := by decide

theorem reject00484 : Rejected (base 0 6 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 52) _ validLayout0029) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind00484_0) certificate0189

private theorem bind00485_0 : Agrees (spec (fastBase 0 6 53) layout0031) scope0199 := by decide

theorem reject00485 : Rejected (base 0 6 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 53) _ validLayout0031) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind00485_0) certificate0202

private theorem bind00486_0 : Agrees (spec (fastBase 0 6 54) layout0031) scope0186 := by decide

theorem reject00486 : Rejected (base 0 6 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 54) _ validLayout0031) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind00486_0) certificate0189

private theorem bind00487_0 : Agrees (spec (fastBase 0 6 55) layout0031) scope0202 := by decide

theorem reject00487 : Rejected (base 0 6 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 55) _ validLayout0031) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind00487_0) certificate0205

private theorem bind00488_0 : Agrees (spec (fastBase 0 6 56) layout0033) scope0205 := by decide

theorem reject00488 : Rejected (base 0 6 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0033 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 56) _ validLayout0033) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind00488_0) certificate0208

private theorem bind00489_0 : Agrees (spec (fastBase 0 6 57) layout0031) scope0201 := by decide

theorem reject00489 : Rejected (base 0 6 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 57) _ validLayout0031) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind00489_0) certificate0204

private theorem bind00490_0 : Agrees (spec (fastBase 0 6 58) layout0029) scope0206 := by decide

private theorem bind00490_1 : Agrees (spec (fastBase 0 6 58) layout0030) scope0183 := by decide

theorem reject00490 : Rejected (base 0 6 58) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 58) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 58) _ validLayout0030) (by decide) (by decide) scope0206 scope0183 (by rw [← fastBase_exact]; exact bind00490_0) (by rw [← fastBase_exact]; exact bind00490_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0209 certificate0186 (by decide)

private theorem bind00491_0 : Agrees (spec (fastBase 0 6 59) layout0031) scope0207 := by decide

theorem reject00491 : Rejected (base 0 6 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 59) _ validLayout0031) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind00491_0) certificate0210

private theorem bind00492_0 : Agrees (spec (fastBase 0 6 60) layout0031) scope0185 := by decide

theorem reject00492 : Rejected (base 0 6 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 60) _ validLayout0031) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind00492_0) certificate0188

private theorem bind00493_0 : Agrees (spec (fastBase 0 6 61) layout0031) scope0191 := by decide

theorem reject00493 : Rejected (base 0 6 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 61) _ validLayout0031) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind00493_0) certificate0194

private theorem bind00494_0 : Agrees (spec (fastBase 0 6 62) layout0031) scope0193 := by decide

theorem reject00494 : Rejected (base 0 6 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 62) _ validLayout0031) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind00494_0) certificate0196

private theorem bind00495_0 : Agrees (spec (fastBase 0 6 63) layout0029) scope0189 := by decide

private theorem bind00495_1 : Agrees (spec (fastBase 0 6 63) layout0030) scope0183 := by decide

theorem reject00495 : Rejected (base 0 6 63) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0029 layout0030 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 63) _ validLayout0029) (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 63) _ validLayout0030) (by decide) (by decide) scope0189 scope0183 (by rw [← fastBase_exact]; exact bind00495_0) (by rw [← fastBase_exact]; exact bind00495_1) 1 6 5 0 (by decide) (by decide) 3 2 (by decide) certificate0192 certificate0186 (by decide)

private theorem bind00496_0 : Agrees (spec (fastBase 0 6 64) layout0031) scope0185 := by decide

theorem reject00496 : Rejected (base 0 6 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 64) _ validLayout0031) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind00496_0) certificate0188

private theorem bind00497_0 : Agrees (spec (fastBase 0 6 65) layout0031) scope0186 := by decide

theorem reject00497 : Rejected (base 0 6 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 65) _ validLayout0031) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind00497_0) certificate0189

private theorem bind00498_0 : Agrees (spec (fastBase 0 6 66) layout0031) scope0207 := by decide

theorem reject00498 : Rejected (base 0 6 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 66) _ validLayout0031) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind00498_0) certificate0210

private theorem bind00499_0 : Agrees (spec (fastBase 0 6 67) layout0029) scope0191 := by decide

theorem reject00499 : Rejected (base 0 6 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 67) _ validLayout0029) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind00499_0) certificate0194

private theorem bind00500_0 : Agrees (spec (fastBase 0 6 68) layout0031) scope0196 := by decide

theorem reject00500 : Rejected (base 0 6 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 68) _ validLayout0031) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind00500_0) certificate0199

private theorem bind00501_0 : Agrees (spec (fastBase 0 6 69) layout0031) scope0191 := by decide

theorem reject00501 : Rejected (base 0 6 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 69) _ validLayout0031) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind00501_0) certificate0194

private theorem bind00502_0 : Agrees (spec (fastBase 0 6 70) layout0033) scope0208 := by decide

theorem reject00502 : Rejected (base 0 6 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0033 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 70) _ validLayout0033) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind00502_0) certificate0211

private theorem bind00503_0 : Agrees (spec (fastBase 0 6 71) layout0031) scope0203 := by decide

theorem reject00503 : Rejected (base 0 6 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 0 6 71) _ validLayout0031) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind00503_0) certificate0206

theorem allCases006 : ∀ y : Fin 72, Rejected (base 0 6 y) := by
  intro y
  fin_cases y

  · exact reject00432

  · exact reject00433

  · exact reject00434

  · exact reject00435

  · exact reject00436

  · exact reject00437

  · exact reject00438

  · exact reject00439

  · exact reject00440

  · exact reject00441

  · exact reject00442

  · exact reject00443

  · exact reject00444

  · exact reject00445

  · exact reject00446

  · exact reject00447

  · exact reject00448

  · exact reject00449

  · exact reject00450

  · exact reject00451

  · exact reject00452

  · exact reject00453

  · exact reject00454

  · exact reject00455

  · exact reject00456

  · exact reject00457

  · exact reject00458

  · exact reject00459

  · exact reject00460

  · exact reject00461

  · exact reject00462

  · exact reject00463

  · exact reject00464

  · exact reject00465

  · exact reject00466

  · exact reject00467

  · exact reject00468

  · exact reject00469

  · exact reject00470

  · exact reject00471

  · exact reject00472

  · exact reject00473

  · exact reject00474

  · exact reject00475

  · exact reject00476

  · exact reject00477

  · exact reject00478

  · exact reject00479

  · exact reject00480

  · exact reject00481

  · exact reject00482

  · exact reject00483

  · exact reject00484

  · exact reject00485

  · exact reject00486

  · exact reject00487

  · exact reject00488

  · exact reject00489

  · exact reject00490

  · exact reject00491

  · exact reject00492

  · exact reject00493

  · exact reject00494

  · exact reject00495

  · exact reject00496

  · exact reject00497

  · exact reject00498

  · exact reject00499

  · exact reject00500

  · exact reject00501

  · exact reject00502

  · exact reject00503

end PricingIntegration.RemainingGWitnesses
