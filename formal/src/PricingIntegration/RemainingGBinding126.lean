import PricingIntegration.RemainingGLayouts026

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks015

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks030

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind09072_0 : Agrees (spec (fastBase 1 54 0) layout0212) scope0547 := by decide

theorem reject09072 : Rejected (base 1 54 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 0) _ validLayout0212) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind09072_0) certificate0589

private theorem bind09073_0 : Agrees (spec (fastBase 1 54 1) layout0212) scope0232 := by decide

theorem reject09073 : Rejected (base 1 54 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 1) _ validLayout0212) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind09073_0) certificate0235

private theorem bind09074_0 : Agrees (spec (fastBase 1 54 2) layout0212) scope0438 := by decide

theorem reject09074 : Rejected (base 1 54 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 2) _ validLayout0212) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind09074_0) certificate0467

private theorem bind09075_0 : Agrees (spec (fastBase 1 54 3) layout0212) scope0441 := by decide

theorem reject09075 : Rejected (base 1 54 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 3) _ validLayout0212) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind09075_0) certificate0470

private theorem bind09076_0 : Agrees (spec (fastBase 1 54 4) layout0212) scope0444 := by decide

theorem reject09076 : Rejected (base 1 54 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 4) _ validLayout0212) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind09076_0) certificate0475

private theorem bind09077_0 : Agrees (spec (fastBase 1 54 5) layout0212) scope0433 := by decide

theorem reject09077 : Rejected (base 1 54 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 5) _ validLayout0212) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind09077_0) certificate0460

private theorem bind09078_0 : Agrees (spec (fastBase 1 54 6) layout0212) scope0548 := by decide

theorem reject09078 : Rejected (base 1 54 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 6) _ validLayout0212) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind09078_0) certificate0590

private theorem bind09079_0 : Agrees (spec (fastBase 1 54 7) layout0213) scope0450 := by decide

theorem reject09079 : Rejected (base 1 54 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 7) _ validLayout0213) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind09079_0) certificate0483

private theorem bind09080_0 : Agrees (spec (fastBase 1 54 8) layout0212) scope0233 := by decide

theorem reject09080 : Rejected (base 1 54 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 8) _ validLayout0212) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind09080_0) certificate0236

private theorem bind09081_0 : Agrees (spec (fastBase 1 54 9) layout0214) scope0182 := by decide

private theorem bind09081_1 : Agrees (spec (fastBase 1 54 9) layout0213) scope0250 := by decide

theorem reject09081 : Rejected (base 1 54 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 9) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 9) _ validLayout0213) (by decide) (by decide) scope0182 scope0250 (by rw [← fastBase_exact]; exact bind09081_0) (by rw [← fastBase_exact]; exact bind09081_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0253 (by decide)

private theorem bind09082_0 : Agrees (spec (fastBase 1 54 10) layout0212) scope0236 := by decide

theorem reject09082 : Rejected (base 1 54 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 10) _ validLayout0212) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind09082_0) certificate0239

private theorem bind09083_0 : Agrees (spec (fastBase 1 54 11) layout0212) scope0434 := by decide

theorem reject09083 : Rejected (base 1 54 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 11) _ validLayout0212) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind09083_0) certificate0461

private theorem bind09084_0 : Agrees (spec (fastBase 1 54 12) layout0214) scope0194 := by decide

theorem reject09084 : Rejected (base 1 54 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 12) _ validLayout0214) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind09084_0) certificate0197

private theorem bind09085_0 : Agrees (spec (fastBase 1 54 13) layout0212) scope0547 := by decide

theorem reject09085 : Rejected (base 1 54 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 13) _ validLayout0212) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind09085_0) certificate0589

private theorem bind09086_0 : Agrees (spec (fastBase 1 54 14) layout0212) scope0551 := by decide

theorem reject09086 : Rejected (base 1 54 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 14) _ validLayout0212) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind09086_0) certificate0594

private theorem bind09087_0 : Agrees (spec (fastBase 1 54 15) layout0214) scope0178 := by decide

private theorem bind09087_1 : Agrees (spec (fastBase 1 54 15) layout0213) scope0452 := by decide

theorem reject09087 : Rejected (base 1 54 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 15) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 15) _ validLayout0213) (by decide) (by decide) scope0178 scope0452 (by rw [← fastBase_exact]; exact bind09087_0) (by rw [← fastBase_exact]; exact bind09087_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0486 certificate0487 (by decide)

private theorem bind09088_0 : Agrees (spec (fastBase 1 54 16) layout0212) scope0233 := by decide

theorem reject09088 : Rejected (base 1 54 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 16) _ validLayout0212) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind09088_0) certificate0236

private theorem bind09089_0 : Agrees (spec (fastBase 1 54 17) layout0212) scope0550 := by decide

theorem reject09089 : Rejected (base 1 54 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 17) _ validLayout0212) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind09089_0) certificate0593

private theorem bind09090_0 : Agrees (spec (fastBase 1 54 18) layout0212) scope0442 := by decide

theorem reject09090 : Rejected (base 1 54 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 18) _ validLayout0212) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind09090_0) certificate0471

private theorem bind09091_0 : Agrees (spec (fastBase 1 54 19) layout0212) scope0444 := by decide

theorem reject09091 : Rejected (base 1 54 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 19) _ validLayout0212) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind09091_0) certificate0475

private theorem bind09092_0 : Agrees (spec (fastBase 1 54 20) layout0212) scope0548 := by decide

theorem reject09092 : Rejected (base 1 54 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 20) _ validLayout0212) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind09092_0) certificate0590

private theorem bind09093_0 : Agrees (spec (fastBase 1 54 21) layout0212) scope0232 := by decide

theorem reject09093 : Rejected (base 1 54 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 21) _ validLayout0212) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind09093_0) certificate0235

private theorem bind09094_0 : Agrees (spec (fastBase 1 54 22) layout0212) scope0438 := by decide

theorem reject09094 : Rejected (base 1 54 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 22) _ validLayout0212) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind09094_0) certificate0467

private theorem bind09095_0 : Agrees (spec (fastBase 1 54 23) layout0212) scope0438 := by decide

theorem reject09095 : Rejected (base 1 54 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 23) _ validLayout0212) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind09095_0) certificate0467

private theorem bind09096_0 : Agrees (spec (fastBase 1 54 24) layout0212) scope0438 := by decide

theorem reject09096 : Rejected (base 1 54 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 24) _ validLayout0212) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind09096_0) certificate0467

private theorem bind09097_0 : Agrees (spec (fastBase 1 54 25) layout0212) scope0438 := by decide

theorem reject09097 : Rejected (base 1 54 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 25) _ validLayout0212) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind09097_0) certificate0467

private theorem bind09098_0 : Agrees (spec (fastBase 1 54 26) layout0212) scope0438 := by decide

theorem reject09098 : Rejected (base 1 54 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 26) _ validLayout0212) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind09098_0) certificate0467

private theorem bind09099_0 : Agrees (spec (fastBase 1 54 27) layout0212) scope0443 := by decide

theorem reject09099 : Rejected (base 1 54 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 27) _ validLayout0212) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind09099_0) certificate0474

private theorem bind09100_0 : Agrees (spec (fastBase 1 54 28) layout0212) scope0441 := by decide

theorem reject09100 : Rejected (base 1 54 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 28) _ validLayout0212) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind09100_0) certificate0470

private theorem bind09101_0 : Agrees (spec (fastBase 1 54 29) layout0212) scope0433 := by decide

theorem reject09101 : Rejected (base 1 54 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 29) _ validLayout0212) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind09101_0) certificate0460

private theorem bind09102_0 : Agrees (spec (fastBase 1 54 30) layout0214) scope0203 := by decide

theorem reject09102 : Rejected (base 1 54 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 30) _ validLayout0214) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind09102_0) certificate0206

private theorem bind09103_0 : Agrees (spec (fastBase 1 54 31) layout0212) scope0434 := by decide

theorem reject09103 : Rejected (base 1 54 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 31) _ validLayout0212) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind09103_0) certificate0461

private theorem bind09104_0 : Agrees (spec (fastBase 1 54 32) layout0212) scope0232 := by decide

theorem reject09104 : Rejected (base 1 54 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 32) _ validLayout0212) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind09104_0) certificate0235

private theorem bind09105_0 : Agrees (spec (fastBase 1 54 33) layout0212) scope0444 := by decide

theorem reject09105 : Rejected (base 1 54 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 33) _ validLayout0212) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind09105_0) certificate0475

private theorem bind09106_0 : Agrees (spec (fastBase 1 54 34) layout0212) scope0443 := by decide

theorem reject09106 : Rejected (base 1 54 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 34) _ validLayout0212) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind09106_0) certificate0474

private theorem bind09107_0 : Agrees (spec (fastBase 1 54 35) layout0212) scope0439 := by decide

theorem reject09107 : Rejected (base 1 54 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 35) _ validLayout0212) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind09107_0) certificate0468

private theorem bind09108_0 : Agrees (spec (fastBase 1 54 36) layout0212) scope0434 := by decide

theorem reject09108 : Rejected (base 1 54 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 36) _ validLayout0212) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind09108_0) certificate0461

private theorem bind09109_0 : Agrees (spec (fastBase 1 54 37) layout0212) scope0389 := by decide

theorem reject09109 : Rejected (base 1 54 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 37) _ validLayout0212) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind09109_0) certificate0402

private theorem bind09110_0 : Agrees (spec (fastBase 1 54 38) layout0212) scope0552 := by decide

theorem reject09110 : Rejected (base 1 54 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 38) _ validLayout0212) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind09110_0) certificate0595

private theorem bind09111_0 : Agrees (spec (fastBase 1 54 39) layout0212) scope0441 := by decide

theorem reject09111 : Rejected (base 1 54 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 39) _ validLayout0212) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind09111_0) certificate0470

private theorem bind09112_0 : Agrees (spec (fastBase 1 54 40) layout0212) scope0433 := by decide

theorem reject09112 : Rejected (base 1 54 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 40) _ validLayout0212) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind09112_0) certificate0460

private theorem bind09113_0 : Agrees (spec (fastBase 1 54 41) layout0212) scope0236 := by decide

theorem reject09113 : Rejected (base 1 54 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 41) _ validLayout0212) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind09113_0) certificate0239

private theorem bind09114_0 : Agrees (spec (fastBase 1 54 42) layout0212) scope0232 := by decide

theorem reject09114 : Rejected (base 1 54 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 42) _ validLayout0212) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind09114_0) certificate0235

private theorem bind09115_0 : Agrees (spec (fastBase 1 54 43) layout0212) scope0548 := by decide

theorem reject09115 : Rejected (base 1 54 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 43) _ validLayout0212) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind09115_0) certificate0590

private theorem bind09116_0 : Agrees (spec (fastBase 1 54 44) layout0212) scope0233 := by decide

theorem reject09116 : Rejected (base 1 54 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 44) _ validLayout0212) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind09116_0) certificate0236

private theorem bind09117_0 : Agrees (spec (fastBase 1 54 45) layout0214) scope0200 := by decide

theorem reject09117 : Rejected (base 1 54 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 45) _ validLayout0214) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind09117_0) certificate0203

private theorem bind09118_0 : Agrees (spec (fastBase 1 54 46) layout0212) scope0439 := by decide

theorem reject09118 : Rejected (base 1 54 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 46) _ validLayout0212) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind09118_0) certificate0468

private theorem bind09119_0 : Agrees (spec (fastBase 1 54 47) layout0212) scope0547 := by decide

theorem reject09119 : Rejected (base 1 54 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 47) _ validLayout0212) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind09119_0) certificate0589

private theorem bind09120_0 : Agrees (spec (fastBase 1 54 48) layout0212) scope0389 := by decide

theorem reject09120 : Rejected (base 1 54 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 48) _ validLayout0212) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind09120_0) certificate0402

private theorem bind09121_0 : Agrees (spec (fastBase 1 54 49) layout0212) scope0228 := by decide

theorem reject09121 : Rejected (base 1 54 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 49) _ validLayout0212) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind09121_0) certificate0231

private theorem bind09122_0 : Agrees (spec (fastBase 1 54 50) layout0214) scope0178 := by decide

private theorem bind09122_1 : Agrees (spec (fastBase 1 54 50) layout0213) scope0250 := by decide

theorem reject09122 : Rejected (base 1 54 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 50) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 50) _ validLayout0213) (by decide) (by decide) scope0178 scope0250 (by rw [← fastBase_exact]; exact bind09122_0) (by rw [← fastBase_exact]; exact bind09122_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0486 certificate0253 (by decide)

private theorem bind09123_0 : Agrees (spec (fastBase 1 54 51) layout0212) scope0236 := by decide

theorem reject09123 : Rejected (base 1 54 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 51) _ validLayout0212) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind09123_0) certificate0239

private theorem bind09124_0 : Agrees (spec (fastBase 1 54 52) layout0212) scope0547 := by decide

theorem reject09124 : Rejected (base 1 54 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 52) _ validLayout0212) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind09124_0) certificate0589

private theorem bind09125_0 : Agrees (spec (fastBase 1 54 53) layout0212) scope0550 := by decide

theorem reject09125 : Rejected (base 1 54 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 53) _ validLayout0212) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind09125_0) certificate0593

private theorem bind09126_0 : Agrees (spec (fastBase 1 54 54) layout0212) scope0548 := by decide

theorem reject09126 : Rejected (base 1 54 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 54) _ validLayout0212) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind09126_0) certificate0590

private theorem bind09127_0 : Agrees (spec (fastBase 1 54 55) layout0212) scope0233 := by decide

theorem reject09127 : Rejected (base 1 54 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 55) _ validLayout0212) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind09127_0) certificate0236

private theorem bind09128_0 : Agrees (spec (fastBase 1 54 56) layout0212) scope0228 := by decide

theorem reject09128 : Rejected (base 1 54 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 56) _ validLayout0212) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind09128_0) certificate0231

private theorem bind09129_0 : Agrees (spec (fastBase 1 54 57) layout0213) scope0453 := by decide

theorem reject09129 : Rejected (base 1 54 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 57) _ validLayout0213) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind09129_0) certificate0488

private theorem bind09130_0 : Agrees (spec (fastBase 1 54 58) layout0214) scope0182 := by decide

private theorem bind09130_1 : Agrees (spec (fastBase 1 54 58) layout0213) scope0245 := by decide

theorem reject09130 : Rejected (base 1 54 58) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 58) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 58) _ validLayout0213) (by decide) (by decide) scope0182 scope0245 (by rw [← fastBase_exact]; exact bind09130_0) (by rw [← fastBase_exact]; exact bind09130_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0248 (by decide)

private theorem bind09131_0 : Agrees (spec (fastBase 1 54 59) layout0213) scope0456 := by decide

theorem reject09131 : Rejected (base 1 54 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 59) _ validLayout0213) (by decide) scope0456 (by rw [← fastBase_exact]; exact bind09131_0) certificate0491

private theorem bind09132_0 : Agrees (spec (fastBase 1 54 60) layout0213) scope0450 := by decide

theorem reject09132 : Rejected (base 1 54 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 60) _ validLayout0213) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind09132_0) certificate0483

private theorem bind09133_0 : Agrees (spec (fastBase 1 54 61) layout0214) scope0182 := by decide

private theorem bind09133_1 : Agrees (spec (fastBase 1 54 61) layout0213) scope0250 := by decide

theorem reject09133 : Rejected (base 1 54 61) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 61) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 61) _ validLayout0213) (by decide) (by decide) scope0182 scope0250 (by rw [← fastBase_exact]; exact bind09133_0) (by rw [← fastBase_exact]; exact bind09133_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0253 (by decide)

private theorem bind09134_0 : Agrees (spec (fastBase 1 54 62) layout0212) scope0236 := by decide

theorem reject09134 : Rejected (base 1 54 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 62) _ validLayout0212) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind09134_0) certificate0239

private theorem bind09135_0 : Agrees (spec (fastBase 1 54 63) layout0212) scope0433 := by decide

theorem reject09135 : Rejected (base 1 54 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 63) _ validLayout0212) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind09135_0) certificate0460

private theorem bind09136_0 : Agrees (spec (fastBase 1 54 64) layout0214) scope0191 := by decide

theorem reject09136 : Rejected (base 1 54 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 64) _ validLayout0214) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind09136_0) certificate0194

private theorem bind09137_0 : Agrees (spec (fastBase 1 54 65) layout0212) scope0551 := by decide

theorem reject09137 : Rejected (base 1 54 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 65) _ validLayout0212) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind09137_0) certificate0594

private theorem bind09138_0 : Agrees (spec (fastBase 1 54 66) layout0214) scope0203 := by decide

theorem reject09138 : Rejected (base 1 54 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 66) _ validLayout0214) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind09138_0) certificate0206

private theorem bind09139_0 : Agrees (spec (fastBase 1 54 67) layout0212) scope0441 := by decide

theorem reject09139 : Rejected (base 1 54 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 67) _ validLayout0212) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind09139_0) certificate0470

private theorem bind09140_0 : Agrees (spec (fastBase 1 54 68) layout0212) scope0444 := by decide

theorem reject09140 : Rejected (base 1 54 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 68) _ validLayout0212) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind09140_0) certificate0475

private theorem bind09141_0 : Agrees (spec (fastBase 1 54 69) layout0212) scope0442 := by decide

theorem reject09141 : Rejected (base 1 54 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 69) _ validLayout0212) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind09141_0) certificate0471

private theorem bind09142_0 : Agrees (spec (fastBase 1 54 70) layout0212) scope0434 := by decide

theorem reject09142 : Rejected (base 1 54 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 70) _ validLayout0212) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind09142_0) certificate0461

private theorem bind09143_0 : Agrees (spec (fastBase 1 54 71) layout0212) scope0552 := by decide

theorem reject09143 : Rejected (base 1 54 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 1 54 71) _ validLayout0212) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind09143_0) certificate0595

theorem allCases126 : ∀ y : Fin 72, Rejected (base 1 54 y) := by
  intro y
  fin_cases y

  · exact reject09072

  · exact reject09073

  · exact reject09074

  · exact reject09075

  · exact reject09076

  · exact reject09077

  · exact reject09078

  · exact reject09079

  · exact reject09080

  · exact reject09081

  · exact reject09082

  · exact reject09083

  · exact reject09084

  · exact reject09085

  · exact reject09086

  · exact reject09087

  · exact reject09088

  · exact reject09089

  · exact reject09090

  · exact reject09091

  · exact reject09092

  · exact reject09093

  · exact reject09094

  · exact reject09095

  · exact reject09096

  · exact reject09097

  · exact reject09098

  · exact reject09099

  · exact reject09100

  · exact reject09101

  · exact reject09102

  · exact reject09103

  · exact reject09104

  · exact reject09105

  · exact reject09106

  · exact reject09107

  · exact reject09108

  · exact reject09109

  · exact reject09110

  · exact reject09111

  · exact reject09112

  · exact reject09113

  · exact reject09114

  · exact reject09115

  · exact reject09116

  · exact reject09117

  · exact reject09118

  · exact reject09119

  · exact reject09120

  · exact reject09121

  · exact reject09122

  · exact reject09123

  · exact reject09124

  · exact reject09125

  · exact reject09126

  · exact reject09127

  · exact reject09128

  · exact reject09129

  · exact reject09130

  · exact reject09131

  · exact reject09132

  · exact reject09133

  · exact reject09134

  · exact reject09135

  · exact reject09136

  · exact reject09137

  · exact reject09138

  · exact reject09139

  · exact reject09140

  · exact reject09141

  · exact reject09142

  · exact reject09143

end PricingIntegration.RemainingGWitnesses
