import PricingIntegration.RemainingGLayouts016

import PricingIntegration.RemainingGLayouts017

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks007

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks025


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02448_0 : Agrees (spec (fastBase 0 34 0) layout0134) scope0108 := by decide

theorem reject02448 : Rejected (base 0 34 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 0) _ validLayout0134) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02448_0) certificate0111

private theorem bind02449_0 : Agrees (spec (fastBase 0 34 1) layout0135) scope0140 := by decide

theorem reject02449 : Rejected (base 0 34 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 1) _ validLayout0135) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02449_0) certificate0143

private theorem bind02450_0 : Agrees (spec (fastBase 0 34 2) layout0135) scope0141 := by decide

theorem reject02450 : Rejected (base 0 34 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 2) _ validLayout0135) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02450_0) certificate0144

private theorem bind02451_0 : Agrees (spec (fastBase 0 34 3) layout0134) scope0111 := by decide

theorem reject02451 : Rejected (base 0 34 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 3) _ validLayout0134) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind02451_0) certificate0114

private theorem bind02452_0 : Agrees (spec (fastBase 0 34 4) layout0135) scope0144 := by decide

theorem reject02452 : Rejected (base 0 34 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 4) _ validLayout0135) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02452_0) certificate0147

private theorem bind02453_0 : Agrees (spec (fastBase 0 34 5) layout0135) scope0145 := by decide

theorem reject02453 : Rejected (base 0 34 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 5) _ validLayout0135) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02453_0) certificate0148

private theorem bind02454_0 : Agrees (spec (fastBase 0 34 6) layout0134) scope0114 := by decide

private theorem bind02454_1 : Agrees (spec (fastBase 0 34 6) layout0136) scope0397 := by decide

theorem reject02454 : Rejected (base 0 34 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 6) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 6) _ validLayout0136) (by decide) (by decide) scope0114 scope0397 (by rw [← fastBase_exact]; exact bind02454_0) (by rw [← fastBase_exact]; exact bind02454_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0410 (by decide)

private theorem bind02455_0 : Agrees (spec (fastBase 0 34 7) layout0134) scope0116 := by decide

private theorem bind02455_1 : Agrees (spec (fastBase 0 34 7) layout0136) scope0398 := by decide

theorem reject02455 : Rejected (base 0 34 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 7) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 7) _ validLayout0136) (by decide) (by decide) scope0116 scope0398 (by rw [← fastBase_exact]; exact bind02455_0) (by rw [← fastBase_exact]; exact bind02455_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0411 (by decide)

private theorem bind02456_0 : Agrees (spec (fastBase 0 34 8) layout0135) scope0150 := by decide

theorem reject02456 : Rejected (base 0 34 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 8) _ validLayout0135) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02456_0) certificate0153

private theorem bind02457_0 : Agrees (spec (fastBase 0 34 9) layout0134) scope0119 := by decide

theorem reject02457 : Rejected (base 0 34 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 9) _ validLayout0134) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02457_0) certificate0122

private theorem bind02458_0 : Agrees (spec (fastBase 0 34 10) layout0134) scope0120 := by decide

theorem reject02458 : Rejected (base 0 34 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 10) _ validLayout0134) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02458_0) certificate0123

private theorem bind02459_0 : Agrees (spec (fastBase 0 34 11) layout0135) scope0155 := by decide

theorem reject02459 : Rejected (base 0 34 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 11) _ validLayout0135) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02459_0) certificate0158

private theorem bind02460_0 : Agrees (spec (fastBase 0 34 12) layout0135) scope0156 := by decide

theorem reject02460 : Rejected (base 0 34 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 12) _ validLayout0135) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind02460_0) certificate0159

private theorem bind02461_0 : Agrees (spec (fastBase 0 34 13) layout0135) scope0141 := by decide

theorem reject02461 : Rejected (base 0 34 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 13) _ validLayout0135) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02461_0) certificate0144

private theorem bind02462_0 : Agrees (spec (fastBase 0 34 14) layout0135) scope0145 := by decide

theorem reject02462 : Rejected (base 0 34 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 14) _ validLayout0135) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02462_0) certificate0148

private theorem bind02463_0 : Agrees (spec (fastBase 0 34 15) layout0134) scope0123 := by decide

private theorem bind02463_1 : Agrees (spec (fastBase 0 34 15) layout0137) scope0124 := by decide

theorem reject02463 : Rejected (base 0 34 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 15) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 15) _ validLayout0137) (by decide) (by decide) scope0123 scope0124 (by rw [← fastBase_exact]; exact bind02463_0) (by rw [← fastBase_exact]; exact bind02463_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0126 certificate0127 (by decide)

private theorem bind02464_0 : Agrees (spec (fastBase 0 34 16) layout0135) scope0157 := by decide

theorem reject02464 : Rejected (base 0 34 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 16) _ validLayout0135) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind02464_0) certificate0160

private theorem bind02465_0 : Agrees (spec (fastBase 0 34 17) layout0135) scope0158 := by decide

theorem reject02465 : Rejected (base 0 34 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 17) _ validLayout0135) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02465_0) certificate0161

private theorem bind02466_0 : Agrees (spec (fastBase 0 34 18) layout0134) scope0111 := by decide

theorem reject02466 : Rejected (base 0 34 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 18) _ validLayout0134) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind02466_0) certificate0114

private theorem bind02467_0 : Agrees (spec (fastBase 0 34 19) layout0135) scope0140 := by decide

theorem reject02467 : Rejected (base 0 34 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 19) _ validLayout0135) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02467_0) certificate0143

private theorem bind02468_0 : Agrees (spec (fastBase 0 34 20) layout0135) scope0160 := by decide

theorem reject02468 : Rejected (base 0 34 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 20) _ validLayout0135) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind02468_0) certificate0163

private theorem bind02469_0 : Agrees (spec (fastBase 0 34 21) layout0134) scope0129 := by decide

private theorem bind02469_1 : Agrees (spec (fastBase 0 34 21) layout0137) scope0130 := by decide

theorem reject02469 : Rejected (base 0 34 21) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 21) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 21) _ validLayout0137) (by decide) (by decide) scope0129 scope0130 (by rw [← fastBase_exact]; exact bind02469_0) (by rw [← fastBase_exact]; exact bind02469_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0132 certificate0133 (by decide)

private theorem bind02470_0 : Agrees (spec (fastBase 0 34 22) layout0134) scope0108 := by decide

theorem reject02470 : Rejected (base 0 34 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 22) _ validLayout0134) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02470_0) certificate0111

private theorem bind02471_0 : Agrees (spec (fastBase 0 34 23) layout0135) scope0141 := by decide

theorem reject02471 : Rejected (base 0 34 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 23) _ validLayout0135) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02471_0) certificate0144

private theorem bind02472_0 : Agrees (spec (fastBase 0 34 24) layout0135) scope0162 := by decide

theorem reject02472 : Rejected (base 0 34 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 24) _ validLayout0135) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind02472_0) certificate0165

private theorem bind02473_0 : Agrees (spec (fastBase 0 34 25) layout0135) scope0163 := by decide

theorem reject02473 : Rejected (base 0 34 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 25) _ validLayout0135) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind02473_0) certificate0166

private theorem bind02474_0 : Agrees (spec (fastBase 0 34 26) layout0134) scope0123 := by decide

private theorem bind02474_1 : Agrees (spec (fastBase 0 34 26) layout0137) scope0124 := by decide

theorem reject02474 : Rejected (base 0 34 26) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 26) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 26) _ validLayout0137) (by decide) (by decide) scope0123 scope0124 (by rw [← fastBase_exact]; exact bind02474_0) (by rw [← fastBase_exact]; exact bind02474_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0126 certificate0127 (by decide)

private theorem bind02475_0 : Agrees (spec (fastBase 0 34 27) layout0135) scope0140 := by decide

theorem reject02475 : Rejected (base 0 34 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 27) _ validLayout0135) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02475_0) certificate0143

private theorem bind02476_0 : Agrees (spec (fastBase 0 34 28) layout0135) scope0156 := by decide

theorem reject02476 : Rejected (base 0 34 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 28) _ validLayout0135) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind02476_0) certificate0159

private theorem bind02477_0 : Agrees (spec (fastBase 0 34 29) layout0135) scope0145 := by decide

theorem reject02477 : Rejected (base 0 34 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 29) _ validLayout0135) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02477_0) certificate0148

private theorem bind02478_0 : Agrees (spec (fastBase 0 34 30) layout0134) scope0129 := by decide

private theorem bind02478_1 : Agrees (spec (fastBase 0 34 30) layout0137) scope0130 := by decide

theorem reject02478 : Rejected (base 0 34 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 30) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 30) _ validLayout0137) (by decide) (by decide) scope0129 scope0130 (by rw [← fastBase_exact]; exact bind02478_0) (by rw [← fastBase_exact]; exact bind02478_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0132 certificate0133 (by decide)

private theorem bind02479_0 : Agrees (spec (fastBase 0 34 31) layout0135) scope0165 := by decide

theorem reject02479 : Rejected (base 0 34 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 31) _ validLayout0135) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind02479_0) certificate0168

private theorem bind02480_0 : Agrees (spec (fastBase 0 34 32) layout0135) scope0144 := by decide

theorem reject02480 : Rejected (base 0 34 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 32) _ validLayout0135) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02480_0) certificate0147

private theorem bind02481_0 : Agrees (spec (fastBase 0 34 33) layout0135) scope0144 := by decide

theorem reject02481 : Rejected (base 0 34 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 33) _ validLayout0135) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02481_0) certificate0147

private theorem bind02482_0 : Agrees (spec (fastBase 0 34 34) layout0135) scope0144 := by decide

theorem reject02482 : Rejected (base 0 34 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 34) _ validLayout0135) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02482_0) certificate0147

private theorem bind02483_0 : Agrees (spec (fastBase 0 34 35) layout0135) scope0144 := by decide

theorem reject02483 : Rejected (base 0 34 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 35) _ validLayout0135) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02483_0) certificate0147

private theorem bind02484_0 : Agrees (spec (fastBase 0 34 36) layout0135) scope0144 := by decide

theorem reject02484 : Rejected (base 0 34 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 36) _ validLayout0135) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02484_0) certificate0147

private theorem bind02485_0 : Agrees (spec (fastBase 0 34 37) layout0134) scope0108 := by decide

theorem reject02485 : Rejected (base 0 34 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 37) _ validLayout0134) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02485_0) certificate0111

private theorem bind02486_0 : Agrees (spec (fastBase 0 34 38) layout0135) scope0145 := by decide

theorem reject02486 : Rejected (base 0 34 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 38) _ validLayout0135) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02486_0) certificate0148

private theorem bind02487_0 : Agrees (spec (fastBase 0 34 39) layout0134) scope0113 := by decide

theorem reject02487 : Rejected (base 0 34 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 39) _ validLayout0134) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02487_0) certificate0116

private theorem bind02488_0 : Agrees (spec (fastBase 0 34 40) layout0135) scope0158 := by decide

theorem reject02488 : Rejected (base 0 34 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 40) _ validLayout0135) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02488_0) certificate0161

private theorem bind02489_0 : Agrees (spec (fastBase 0 34 41) layout0135) scope0162 := by decide

theorem reject02489 : Rejected (base 0 34 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 41) _ validLayout0135) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind02489_0) certificate0165

private theorem bind02490_0 : Agrees (spec (fastBase 0 34 42) layout0135) scope0167 := by decide

theorem reject02490 : Rejected (base 0 34 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 42) _ validLayout0135) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind02490_0) certificate0170

private theorem bind02491_0 : Agrees (spec (fastBase 0 34 43) layout0135) scope0168 := by decide

theorem reject02491 : Rejected (base 0 34 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 43) _ validLayout0135) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind02491_0) certificate0171

private theorem bind02492_0 : Agrees (spec (fastBase 0 34 44) layout0135) scope0150 := by decide

theorem reject02492 : Rejected (base 0 34 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 44) _ validLayout0135) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02492_0) certificate0153

private theorem bind02493_0 : Agrees (spec (fastBase 0 34 45) layout0134) scope0116 := by decide

private theorem bind02493_1 : Agrees (spec (fastBase 0 34 45) layout0136) scope0397 := by decide

theorem reject02493 : Rejected (base 0 34 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 45) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 45) _ validLayout0136) (by decide) (by decide) scope0116 scope0397 (by rw [← fastBase_exact]; exact bind02493_0) (by rw [← fastBase_exact]; exact bind02493_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0410 (by decide)

private theorem bind02494_0 : Agrees (spec (fastBase 0 34 46) layout0135) scope0155 := by decide

theorem reject02494 : Rejected (base 0 34 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 46) _ validLayout0135) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02494_0) certificate0158

private theorem bind02495_0 : Agrees (spec (fastBase 0 34 47) layout0134) scope0134 := by decide

theorem reject02495 : Rejected (base 0 34 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 47) _ validLayout0134) (by decide) scope0134 (by rw [← fastBase_exact]; exact bind02495_0) certificate0137

private theorem bind02496_0 : Agrees (spec (fastBase 0 34 48) layout0134) scope0135 := by decide

theorem reject02496 : Rejected (base 0 34 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 48) _ validLayout0134) (by decide) scope0135 (by rw [← fastBase_exact]; exact bind02496_0) certificate0138

private theorem bind02497_0 : Agrees (spec (fastBase 0 34 49) layout0134) scope0114 := by decide

private theorem bind02497_1 : Agrees (spec (fastBase 0 34 49) layout0136) scope0398 := by decide

theorem reject02497 : Rejected (base 0 34 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 49) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 49) _ validLayout0136) (by decide) (by decide) scope0114 scope0398 (by rw [← fastBase_exact]; exact bind02497_0) (by rw [← fastBase_exact]; exact bind02497_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0411 (by decide)

private theorem bind02498_0 : Agrees (spec (fastBase 0 34 50) layout0134) scope0119 := by decide

theorem reject02498 : Rejected (base 0 34 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 50) _ validLayout0134) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02498_0) certificate0122

private theorem bind02499_0 : Agrees (spec (fastBase 0 34 51) layout0137) scope0399 := by decide

theorem reject02499 : Rejected (base 0 34 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 51) _ validLayout0137) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind02499_0) certificate0412

private theorem bind02500_0 : Agrees (spec (fastBase 0 34 52) layout0135) scope0163 := by decide

theorem reject02500 : Rejected (base 0 34 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 52) _ validLayout0135) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind02500_0) certificate0166

private theorem bind02501_0 : Agrees (spec (fastBase 0 34 53) layout0135) scope0150 := by decide

theorem reject02501 : Rejected (base 0 34 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 53) _ validLayout0135) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02501_0) certificate0153

private theorem bind02502_0 : Agrees (spec (fastBase 0 34 54) layout0134) scope0118 := by decide

theorem reject02502 : Rejected (base 0 34 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 54) _ validLayout0134) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind02502_0) certificate0121

private theorem bind02503_0 : Agrees (spec (fastBase 0 34 55) layout0135) scope0171 := by decide

theorem reject02503 : Rejected (base 0 34 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 55) _ validLayout0135) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind02503_0) certificate0174

private theorem bind02504_0 : Agrees (spec (fastBase 0 34 56) layout0134) scope0120 := by decide

theorem reject02504 : Rejected (base 0 34 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 56) _ validLayout0134) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02504_0) certificate0123

private theorem bind02505_0 : Agrees (spec (fastBase 0 34 57) layout0135) scope0140 := by decide

theorem reject02505 : Rejected (base 0 34 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 57) _ validLayout0135) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02505_0) certificate0143

private theorem bind02506_0 : Agrees (spec (fastBase 0 34 58) layout0135) scope0165 := by decide

theorem reject02506 : Rejected (base 0 34 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 58) _ validLayout0135) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind02506_0) certificate0168

private theorem bind02507_0 : Agrees (spec (fastBase 0 34 59) layout0135) scope0167 := by decide

theorem reject02507 : Rejected (base 0 34 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 59) _ validLayout0135) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind02507_0) certificate0170

private theorem bind02508_0 : Agrees (spec (fastBase 0 34 60) layout0137) scope0137 := by decide

theorem reject02508 : Rejected (base 0 34 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 60) _ validLayout0137) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind02508_0) certificate0140

private theorem bind02509_0 : Agrees (spec (fastBase 0 34 61) layout0135) scope0155 := by decide

theorem reject02509 : Rejected (base 0 34 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 61) _ validLayout0135) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02509_0) certificate0158

private theorem bind02510_0 : Agrees (spec (fastBase 0 34 62) layout0135) scope0141 := by decide

theorem reject02510 : Rejected (base 0 34 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 62) _ validLayout0135) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02510_0) certificate0144

private theorem bind02511_0 : Agrees (spec (fastBase 0 34 63) layout0135) scope0157 := by decide

theorem reject02511 : Rejected (base 0 34 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 63) _ validLayout0135) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind02511_0) certificate0160

private theorem bind02512_0 : Agrees (spec (fastBase 0 34 64) layout0134) scope0120 := by decide

theorem reject02512 : Rejected (base 0 34 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 64) _ validLayout0134) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02512_0) certificate0123

private theorem bind02513_0 : Agrees (spec (fastBase 0 34 65) layout0135) scope0150 := by decide

theorem reject02513 : Rejected (base 0 34 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 65) _ validLayout0135) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02513_0) certificate0153

private theorem bind02514_0 : Agrees (spec (fastBase 0 34 66) layout0135) scope0168 := by decide

theorem reject02514 : Rejected (base 0 34 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 66) _ validLayout0135) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind02514_0) certificate0171

private theorem bind02515_0 : Agrees (spec (fastBase 0 34 67) layout0135) scope0160 := by decide

theorem reject02515 : Rejected (base 0 34 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 67) _ validLayout0135) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind02515_0) certificate0163

private theorem bind02516_0 : Agrees (spec (fastBase 0 34 68) layout0135) scope0155 := by decide

theorem reject02516 : Rejected (base 0 34 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 68) _ validLayout0135) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02516_0) certificate0158

private theorem bind02517_0 : Agrees (spec (fastBase 0 34 69) layout0137) scope0400 := by decide

theorem reject02517 : Rejected (base 0 34 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 69) _ validLayout0137) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind02517_0) certificate0413

private theorem bind02518_0 : Agrees (spec (fastBase 0 34 70) layout0134) scope0119 := by decide

theorem reject02518 : Rejected (base 0 34 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 70) _ validLayout0134) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02518_0) certificate0122

private theorem bind02519_0 : Agrees (spec (fastBase 0 34 71) layout0135) scope0171 := by decide

theorem reject02519 : Rejected (base 0 34 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 0 34 71) _ validLayout0135) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind02519_0) certificate0174

theorem allCases034 : ∀ y : Fin 72, Rejected (base 0 34 y) := by
  intro y
  fin_cases y

  · exact reject02448

  · exact reject02449

  · exact reject02450

  · exact reject02451

  · exact reject02452

  · exact reject02453

  · exact reject02454

  · exact reject02455

  · exact reject02456

  · exact reject02457

  · exact reject02458

  · exact reject02459

  · exact reject02460

  · exact reject02461

  · exact reject02462

  · exact reject02463

  · exact reject02464

  · exact reject02465

  · exact reject02466

  · exact reject02467

  · exact reject02468

  · exact reject02469

  · exact reject02470

  · exact reject02471

  · exact reject02472

  · exact reject02473

  · exact reject02474

  · exact reject02475

  · exact reject02476

  · exact reject02477

  · exact reject02478

  · exact reject02479

  · exact reject02480

  · exact reject02481

  · exact reject02482

  · exact reject02483

  · exact reject02484

  · exact reject02485

  · exact reject02486

  · exact reject02487

  · exact reject02488

  · exact reject02489

  · exact reject02490

  · exact reject02491

  · exact reject02492

  · exact reject02493

  · exact reject02494

  · exact reject02495

  · exact reject02496

  · exact reject02497

  · exact reject02498

  · exact reject02499

  · exact reject02500

  · exact reject02501

  · exact reject02502

  · exact reject02503

  · exact reject02504

  · exact reject02505

  · exact reject02506

  · exact reject02507

  · exact reject02508

  · exact reject02509

  · exact reject02510

  · exact reject02511

  · exact reject02512

  · exact reject02513

  · exact reject02514

  · exact reject02515

  · exact reject02516

  · exact reject02517

  · exact reject02518

  · exact reject02519

end PricingIntegration.RemainingGWitnesses
