import PricingIntegration.RemainingGLayouts002

import PricingIntegration.RemainingGLayouts003

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks011


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00360_0 : Agrees (spec (fastBase 0 5 0) layout0023) scope0138 := by decide

private theorem bind00360_1 : Agrees (spec (fastBase 0 5 0) layout0024) scope0139 := by decide

theorem reject00360 : Rejected (base 0 5 0) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 0) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 0) _ validLayout0024) (by decide) (by decide) scope0138 scope0139 (by rw [← fastBase_exact]; exact bind00360_0) (by rw [← fastBase_exact]; exact bind00360_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0141 certificate0142 (by decide)

private theorem bind00361_0 : Agrees (spec (fastBase 0 5 1) layout0025) scope0140 := by decide

theorem reject00361 : Rejected (base 0 5 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 1) _ validLayout0025) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind00361_0) certificate0143

private theorem bind00362_0 : Agrees (spec (fastBase 0 5 2) layout0025) scope0141 := by decide

theorem reject00362 : Rejected (base 0 5 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 2) _ validLayout0025) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind00362_0) certificate0144

private theorem bind00363_0 : Agrees (spec (fastBase 0 5 3) layout0026) scope0142 := by decide

private theorem bind00363_1 : Agrees (spec (fastBase 0 5 3) layout0024) scope0143 := by decide

theorem reject00363 : Rejected (base 0 5 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0026 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 3) _ validLayout0026) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 3) _ validLayout0024) (by decide) (by decide) scope0142 scope0143 (by rw [← fastBase_exact]; exact bind00363_0) (by rw [← fastBase_exact]; exact bind00363_1) 2 7 6 1 (by decide) (by decide) 2 3 (by decide) certificate0145 certificate0146 (by decide)

private theorem bind00364_0 : Agrees (spec (fastBase 0 5 4) layout0025) scope0144 := by decide

theorem reject00364 : Rejected (base 0 5 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 4) _ validLayout0025) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind00364_0) certificate0147

private theorem bind00365_0 : Agrees (spec (fastBase 0 5 5) layout0025) scope0145 := by decide

theorem reject00365 : Rejected (base 0 5 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 5) _ validLayout0025) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind00365_0) certificate0148

private theorem bind00366_0 : Agrees (spec (fastBase 0 5 6) layout0027) scope0146 := by decide

private theorem bind00366_1 : Agrees (spec (fastBase 0 5 6) layout0024) scope0147 := by decide

theorem reject00366 : Rejected (base 0 5 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0027 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 6) _ validLayout0027) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 6) _ validLayout0024) (by decide) (by decide) scope0146 scope0147 (by rw [← fastBase_exact]; exact bind00366_0) (by rw [← fastBase_exact]; exact bind00366_1) 2 7 7 2 (by decide) (by decide) 2 3 (by decide) certificate0149 certificate0150 (by decide)

private theorem bind00367_0 : Agrees (spec (fastBase 0 5 7) layout0023) scope0148 := by decide

private theorem bind00367_1 : Agrees (spec (fastBase 0 5 7) layout0024) scope0149 := by decide

theorem reject00367 : Rejected (base 0 5 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 7) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 7) _ validLayout0024) (by decide) (by decide) scope0148 scope0149 (by rw [← fastBase_exact]; exact bind00367_0) (by rw [← fastBase_exact]; exact bind00367_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0152 (by decide)

private theorem bind00368_0 : Agrees (spec (fastBase 0 5 8) layout0025) scope0150 := by decide

theorem reject00368 : Rejected (base 0 5 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 8) _ validLayout0025) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind00368_0) certificate0153

private theorem bind00369_0 : Agrees (spec (fastBase 0 5 9) layout0023) scope0151 := by decide

private theorem bind00369_1 : Agrees (spec (fastBase 0 5 9) layout0024) scope0152 := by decide

theorem reject00369 : Rejected (base 0 5 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 9) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 9) _ validLayout0024) (by decide) (by decide) scope0151 scope0152 (by rw [← fastBase_exact]; exact bind00369_0) (by rw [← fastBase_exact]; exact bind00369_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0154 certificate0155 (by decide)

private theorem bind00370_0 : Agrees (spec (fastBase 0 5 10) layout0023) scope0153 := by decide

private theorem bind00370_1 : Agrees (spec (fastBase 0 5 10) layout0024) scope0154 := by decide

theorem reject00370 : Rejected (base 0 5 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 10) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 10) _ validLayout0024) (by decide) (by decide) scope0153 scope0154 (by rw [← fastBase_exact]; exact bind00370_0) (by rw [← fastBase_exact]; exact bind00370_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0156 certificate0157 (by decide)

private theorem bind00371_0 : Agrees (spec (fastBase 0 5 11) layout0025) scope0155 := by decide

theorem reject00371 : Rejected (base 0 5 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 11) _ validLayout0025) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind00371_0) certificate0158

private theorem bind00372_0 : Agrees (spec (fastBase 0 5 12) layout0025) scope0156 := by decide

theorem reject00372 : Rejected (base 0 5 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 12) _ validLayout0025) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind00372_0) certificate0159

private theorem bind00373_0 : Agrees (spec (fastBase 0 5 13) layout0025) scope0141 := by decide

theorem reject00373 : Rejected (base 0 5 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 13) _ validLayout0025) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind00373_0) certificate0144

private theorem bind00374_0 : Agrees (spec (fastBase 0 5 14) layout0025) scope0145 := by decide

theorem reject00374 : Rejected (base 0 5 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 14) _ validLayout0025) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind00374_0) certificate0148

private theorem bind00375_0 : Agrees (spec (fastBase 0 5 15) layout0023) scope0138 := by decide

private theorem bind00375_1 : Agrees (spec (fastBase 0 5 15) layout0024) scope0149 := by decide

theorem reject00375 : Rejected (base 0 5 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 15) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 15) _ validLayout0024) (by decide) (by decide) scope0138 scope0149 (by rw [← fastBase_exact]; exact bind00375_0) (by rw [← fastBase_exact]; exact bind00375_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0141 certificate0152 (by decide)

private theorem bind00376_0 : Agrees (spec (fastBase 0 5 16) layout0025) scope0157 := by decide

theorem reject00376 : Rejected (base 0 5 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 16) _ validLayout0025) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind00376_0) certificate0160

private theorem bind00377_0 : Agrees (spec (fastBase 0 5 17) layout0025) scope0158 := by decide

theorem reject00377 : Rejected (base 0 5 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 17) _ validLayout0025) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind00377_0) certificate0161

private theorem bind00378_0 : Agrees (spec (fastBase 0 5 18) layout0028) scope0159 := by decide

theorem reject00378 : Rejected (base 0 5 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 18) _ validLayout0028) (by decide) scope0159 (by rw [← fastBase_exact]; exact bind00378_0) certificate0162

private theorem bind00379_0 : Agrees (spec (fastBase 0 5 19) layout0025) scope0140 := by decide

theorem reject00379 : Rejected (base 0 5 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 19) _ validLayout0025) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind00379_0) certificate0143

private theorem bind00380_0 : Agrees (spec (fastBase 0 5 20) layout0025) scope0160 := by decide

theorem reject00380 : Rejected (base 0 5 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 20) _ validLayout0025) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind00380_0) certificate0163

private theorem bind00381_0 : Agrees (spec (fastBase 0 5 21) layout0023) scope0140 := by decide

theorem reject00381 : Rejected (base 0 5 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 21) _ validLayout0023) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind00381_0) certificate0143

private theorem bind00382_0 : Agrees (spec (fastBase 0 5 22) layout0028) scope0161 := by decide

theorem reject00382 : Rejected (base 0 5 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 22) _ validLayout0028) (by decide) scope0161 (by rw [← fastBase_exact]; exact bind00382_0) certificate0164

private theorem bind00383_0 : Agrees (spec (fastBase 0 5 23) layout0025) scope0141 := by decide

theorem reject00383 : Rejected (base 0 5 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 23) _ validLayout0025) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind00383_0) certificate0144

private theorem bind00384_0 : Agrees (spec (fastBase 0 5 24) layout0025) scope0162 := by decide

theorem reject00384 : Rejected (base 0 5 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 24) _ validLayout0025) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind00384_0) certificate0165

private theorem bind00385_0 : Agrees (spec (fastBase 0 5 25) layout0025) scope0163 := by decide

theorem reject00385 : Rejected (base 0 5 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 25) _ validLayout0025) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind00385_0) certificate0166

private theorem bind00386_0 : Agrees (spec (fastBase 0 5 26) layout0023) scope0141 := by decide

theorem reject00386 : Rejected (base 0 5 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 26) _ validLayout0023) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind00386_0) certificate0144

private theorem bind00387_0 : Agrees (spec (fastBase 0 5 27) layout0025) scope0140 := by decide

theorem reject00387 : Rejected (base 0 5 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 27) _ validLayout0025) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind00387_0) certificate0143

private theorem bind00388_0 : Agrees (spec (fastBase 0 5 28) layout0025) scope0156 := by decide

theorem reject00388 : Rejected (base 0 5 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 28) _ validLayout0025) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind00388_0) certificate0159

private theorem bind00389_0 : Agrees (spec (fastBase 0 5 29) layout0025) scope0145 := by decide

theorem reject00389 : Rejected (base 0 5 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 29) _ validLayout0025) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind00389_0) certificate0148

private theorem bind00390_0 : Agrees (spec (fastBase 0 5 30) layout0023) scope0164 := by decide

private theorem bind00390_1 : Agrees (spec (fastBase 0 5 30) layout0024) scope0149 := by decide

theorem reject00390 : Rejected (base 0 5 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 30) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 30) _ validLayout0024) (by decide) (by decide) scope0164 scope0149 (by rw [← fastBase_exact]; exact bind00390_0) (by rw [← fastBase_exact]; exact bind00390_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0167 certificate0152 (by decide)

private theorem bind00391_0 : Agrees (spec (fastBase 0 5 31) layout0025) scope0165 := by decide

theorem reject00391 : Rejected (base 0 5 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 31) _ validLayout0025) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind00391_0) certificate0168

private theorem bind00392_0 : Agrees (spec (fastBase 0 5 32) layout0025) scope0144 := by decide

theorem reject00392 : Rejected (base 0 5 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 32) _ validLayout0025) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind00392_0) certificate0147

private theorem bind00393_0 : Agrees (spec (fastBase 0 5 33) layout0025) scope0144 := by decide

theorem reject00393 : Rejected (base 0 5 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 33) _ validLayout0025) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind00393_0) certificate0147

private theorem bind00394_0 : Agrees (spec (fastBase 0 5 34) layout0025) scope0144 := by decide

theorem reject00394 : Rejected (base 0 5 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 34) _ validLayout0025) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind00394_0) certificate0147

private theorem bind00395_0 : Agrees (spec (fastBase 0 5 35) layout0025) scope0144 := by decide

theorem reject00395 : Rejected (base 0 5 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 35) _ validLayout0025) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind00395_0) certificate0147

private theorem bind00396_0 : Agrees (spec (fastBase 0 5 36) layout0025) scope0144 := by decide

theorem reject00396 : Rejected (base 0 5 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 36) _ validLayout0025) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind00396_0) certificate0147

private theorem bind00397_0 : Agrees (spec (fastBase 0 5 37) layout0023) scope0145 := by decide

theorem reject00397 : Rejected (base 0 5 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 37) _ validLayout0023) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind00397_0) certificate0148

private theorem bind00398_0 : Agrees (spec (fastBase 0 5 38) layout0025) scope0145 := by decide

theorem reject00398 : Rejected (base 0 5 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 38) _ validLayout0025) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind00398_0) certificate0148

private theorem bind00399_0 : Agrees (spec (fastBase 0 5 39) layout0026) scope0166 := by decide

theorem reject00399 : Rejected (base 0 5 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0026 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 39) _ validLayout0026) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind00399_0) certificate0169

private theorem bind00400_0 : Agrees (spec (fastBase 0 5 40) layout0025) scope0158 := by decide

theorem reject00400 : Rejected (base 0 5 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 40) _ validLayout0025) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind00400_0) certificate0161

private theorem bind00401_0 : Agrees (spec (fastBase 0 5 41) layout0025) scope0162 := by decide

theorem reject00401 : Rejected (base 0 5 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 41) _ validLayout0025) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind00401_0) certificate0165

private theorem bind00402_0 : Agrees (spec (fastBase 0 5 42) layout0025) scope0167 := by decide

theorem reject00402 : Rejected (base 0 5 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 42) _ validLayout0025) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind00402_0) certificate0170

private theorem bind00403_0 : Agrees (spec (fastBase 0 5 43) layout0025) scope0168 := by decide

theorem reject00403 : Rejected (base 0 5 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 43) _ validLayout0025) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind00403_0) certificate0171

private theorem bind00404_0 : Agrees (spec (fastBase 0 5 44) layout0025) scope0150 := by decide

theorem reject00404 : Rejected (base 0 5 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 44) _ validLayout0025) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind00404_0) certificate0153

private theorem bind00405_0 : Agrees (spec (fastBase 0 5 45) layout0023) scope0148 := by decide

private theorem bind00405_1 : Agrees (spec (fastBase 0 5 45) layout0024) scope0149 := by decide

theorem reject00405 : Rejected (base 0 5 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 45) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 45) _ validLayout0024) (by decide) (by decide) scope0148 scope0149 (by rw [← fastBase_exact]; exact bind00405_0) (by rw [← fastBase_exact]; exact bind00405_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0152 (by decide)

private theorem bind00406_0 : Agrees (spec (fastBase 0 5 46) layout0025) scope0155 := by decide

theorem reject00406 : Rejected (base 0 5 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 46) _ validLayout0025) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind00406_0) certificate0158

private theorem bind00407_0 : Agrees (spec (fastBase 0 5 47) layout0023) scope0148 := by decide

private theorem bind00407_1 : Agrees (spec (fastBase 0 5 47) layout0024) scope0139 := by decide

theorem reject00407 : Rejected (base 0 5 47) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 47) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 47) _ validLayout0024) (by decide) (by decide) scope0148 scope0139 (by rw [← fastBase_exact]; exact bind00407_0) (by rw [← fastBase_exact]; exact bind00407_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0142 (by decide)

private theorem bind00408_0 : Agrees (spec (fastBase 0 5 48) layout0026) scope0169 := by decide

private theorem bind00408_1 : Agrees (spec (fastBase 0 5 48) layout0024) scope0143 := by decide

theorem reject00408 : Rejected (base 0 5 48) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0026 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 48) _ validLayout0026) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 48) _ validLayout0024) (by decide) (by decide) scope0169 scope0143 (by rw [← fastBase_exact]; exact bind00408_0) (by rw [← fastBase_exact]; exact bind00408_1) 2 7 6 1 (by decide) (by decide) 2 3 (by decide) certificate0172 certificate0146 (by decide)

private theorem bind00409_0 : Agrees (spec (fastBase 0 5 49) layout0027) scope0169 := by decide

private theorem bind00409_1 : Agrees (spec (fastBase 0 5 49) layout0024) scope0147 := by decide

theorem reject00409 : Rejected (base 0 5 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0027 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 49) _ validLayout0027) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 49) _ validLayout0024) (by decide) (by decide) scope0169 scope0147 (by rw [← fastBase_exact]; exact bind00409_0) (by rw [← fastBase_exact]; exact bind00409_1) 2 7 7 2 (by decide) (by decide) 2 3 (by decide) certificate0172 certificate0150 (by decide)

private theorem bind00410_0 : Agrees (spec (fastBase 0 5 50) layout0023) scope0148 := by decide

private theorem bind00410_1 : Agrees (spec (fastBase 0 5 50) layout0024) scope0152 := by decide

theorem reject00410 : Rejected (base 0 5 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 50) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 50) _ validLayout0024) (by decide) (by decide) scope0148 scope0152 (by rw [← fastBase_exact]; exact bind00410_0) (by rw [← fastBase_exact]; exact bind00410_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0155 (by decide)

private theorem bind00411_0 : Agrees (spec (fastBase 0 5 51) layout0023) scope0153 := by decide

private theorem bind00411_1 : Agrees (spec (fastBase 0 5 51) layout0024) scope0154 := by decide

theorem reject00411 : Rejected (base 0 5 51) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 51) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 51) _ validLayout0024) (by decide) (by decide) scope0153 scope0154 (by rw [← fastBase_exact]; exact bind00411_0) (by rw [← fastBase_exact]; exact bind00411_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0156 certificate0157 (by decide)

private theorem bind00412_0 : Agrees (spec (fastBase 0 5 52) layout0025) scope0163 := by decide

theorem reject00412 : Rejected (base 0 5 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 52) _ validLayout0025) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind00412_0) certificate0166

private theorem bind00413_0 : Agrees (spec (fastBase 0 5 53) layout0025) scope0150 := by decide

theorem reject00413 : Rejected (base 0 5 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 53) _ validLayout0025) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind00413_0) certificate0153

private theorem bind00414_0 : Agrees (spec (fastBase 0 5 54) layout0026) scope0170 := by decide

theorem reject00414 : Rejected (base 0 5 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0026 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 54) _ validLayout0026) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind00414_0) certificate0173

private theorem bind00415_0 : Agrees (spec (fastBase 0 5 55) layout0025) scope0171 := by decide

theorem reject00415 : Rejected (base 0 5 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 55) _ validLayout0025) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind00415_0) certificate0174

private theorem bind00416_0 : Agrees (spec (fastBase 0 5 56) layout0028) scope0172 := by decide

theorem reject00416 : Rejected (base 0 5 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 56) _ validLayout0028) (by decide) scope0172 (by rw [← fastBase_exact]; exact bind00416_0) certificate0175

private theorem bind00417_0 : Agrees (spec (fastBase 0 5 57) layout0025) scope0140 := by decide

theorem reject00417 : Rejected (base 0 5 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 57) _ validLayout0025) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind00417_0) certificate0143

private theorem bind00418_0 : Agrees (spec (fastBase 0 5 58) layout0025) scope0165 := by decide

theorem reject00418 : Rejected (base 0 5 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 58) _ validLayout0025) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind00418_0) certificate0168

private theorem bind00419_0 : Agrees (spec (fastBase 0 5 59) layout0025) scope0167 := by decide

theorem reject00419 : Rejected (base 0 5 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 59) _ validLayout0025) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind00419_0) certificate0170

private theorem bind00420_0 : Agrees (spec (fastBase 0 5 60) layout0023) scope0151 := by decide

private theorem bind00420_1 : Agrees (spec (fastBase 0 5 60) layout0024) scope0149 := by decide

theorem reject00420 : Rejected (base 0 5 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 60) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 60) _ validLayout0024) (by decide) (by decide) scope0151 scope0149 (by rw [← fastBase_exact]; exact bind00420_0) (by rw [← fastBase_exact]; exact bind00420_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0154 certificate0152 (by decide)

private theorem bind00421_0 : Agrees (spec (fastBase 0 5 61) layout0025) scope0155 := by decide

theorem reject00421 : Rejected (base 0 5 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 61) _ validLayout0025) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind00421_0) certificate0158

private theorem bind00422_0 : Agrees (spec (fastBase 0 5 62) layout0025) scope0141 := by decide

theorem reject00422 : Rejected (base 0 5 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 62) _ validLayout0025) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind00422_0) certificate0144

private theorem bind00423_0 : Agrees (spec (fastBase 0 5 63) layout0025) scope0157 := by decide

theorem reject00423 : Rejected (base 0 5 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 63) _ validLayout0025) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind00423_0) certificate0160

private theorem bind00424_0 : Agrees (spec (fastBase 0 5 64) layout0023) scope0148 := by decide

private theorem bind00424_1 : Agrees (spec (fastBase 0 5 64) layout0024) scope0149 := by decide

theorem reject00424 : Rejected (base 0 5 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0023 layout0024 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 64) _ validLayout0023) (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 64) _ validLayout0024) (by decide) (by decide) scope0148 scope0149 (by rw [← fastBase_exact]; exact bind00424_0) (by rw [← fastBase_exact]; exact bind00424_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0152 (by decide)

private theorem bind00425_0 : Agrees (spec (fastBase 0 5 65) layout0025) scope0150 := by decide

theorem reject00425 : Rejected (base 0 5 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 65) _ validLayout0025) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind00425_0) certificate0153

private theorem bind00426_0 : Agrees (spec (fastBase 0 5 66) layout0025) scope0168 := by decide

theorem reject00426 : Rejected (base 0 5 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 66) _ validLayout0025) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind00426_0) certificate0171

private theorem bind00427_0 : Agrees (spec (fastBase 0 5 67) layout0025) scope0160 := by decide

theorem reject00427 : Rejected (base 0 5 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 67) _ validLayout0025) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind00427_0) certificate0163

private theorem bind00428_0 : Agrees (spec (fastBase 0 5 68) layout0025) scope0155 := by decide

theorem reject00428 : Rejected (base 0 5 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 68) _ validLayout0025) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind00428_0) certificate0158

private theorem bind00429_0 : Agrees (spec (fastBase 0 5 69) layout0023) scope0155 := by decide

theorem reject00429 : Rejected (base 0 5 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0023 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 69) _ validLayout0023) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind00429_0) certificate0158

private theorem bind00430_0 : Agrees (spec (fastBase 0 5 70) layout0028) scope0173 := by decide

theorem reject00430 : Rejected (base 0 5 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0028 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 70) _ validLayout0028) (by decide) scope0173 (by rw [← fastBase_exact]; exact bind00430_0) certificate0176

private theorem bind00431_0 : Agrees (spec (fastBase 0 5 71) layout0025) scope0171 := by decide

theorem reject00431 : Rejected (base 0 5 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0025 (layoutValid_of_refines _ _ (base_refines_skeleton 0 5 71) _ validLayout0025) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind00431_0) certificate0174

theorem allCases005 : ∀ y : Fin 72, Rejected (base 0 5 y) := by
  intro y
  fin_cases y

  · exact reject00360

  · exact reject00361

  · exact reject00362

  · exact reject00363

  · exact reject00364

  · exact reject00365

  · exact reject00366

  · exact reject00367

  · exact reject00368

  · exact reject00369

  · exact reject00370

  · exact reject00371

  · exact reject00372

  · exact reject00373

  · exact reject00374

  · exact reject00375

  · exact reject00376

  · exact reject00377

  · exact reject00378

  · exact reject00379

  · exact reject00380

  · exact reject00381

  · exact reject00382

  · exact reject00383

  · exact reject00384

  · exact reject00385

  · exact reject00386

  · exact reject00387

  · exact reject00388

  · exact reject00389

  · exact reject00390

  · exact reject00391

  · exact reject00392

  · exact reject00393

  · exact reject00394

  · exact reject00395

  · exact reject00396

  · exact reject00397

  · exact reject00398

  · exact reject00399

  · exact reject00400

  · exact reject00401

  · exact reject00402

  · exact reject00403

  · exact reject00404

  · exact reject00405

  · exact reject00406

  · exact reject00407

  · exact reject00408

  · exact reject00409

  · exact reject00410

  · exact reject00411

  · exact reject00412

  · exact reject00413

  · exact reject00414

  · exact reject00415

  · exact reject00416

  · exact reject00417

  · exact reject00418

  · exact reject00419

  · exact reject00420

  · exact reject00421

  · exact reject00422

  · exact reject00423

  · exact reject00424

  · exact reject00425

  · exact reject00426

  · exact reject00427

  · exact reject00428

  · exact reject00429

  · exact reject00430

  · exact reject00431

end PricingIntegration.RemainingGWitnesses
