import PricingIntegration.RemainingGLayouts021

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks004

import PricingIntegration.RemainingGScopeChecks005

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks028


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03096_0 : Agrees (spec (fastBase 0 43 0) layout0171) scope0056 := by decide

theorem reject03096 : Rejected (base 0 43 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 0) _ validLayout0171) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind03096_0) certificate0058

private theorem bind03097_0 : Agrees (spec (fastBase 0 43 1) layout0171) scope0059 := by decide

theorem reject03097 : Rejected (base 0 43 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 1) _ validLayout0171) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind03097_0) certificate0061

private theorem bind03098_0 : Agrees (spec (fastBase 0 43 2) layout0171) scope0054 := by decide

theorem reject03098 : Rejected (base 0 43 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 2) _ validLayout0171) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind03098_0) certificate0056

private theorem bind03099_0 : Agrees (spec (fastBase 0 43 3) layout0171) scope0060 := by decide

theorem reject03099 : Rejected (base 0 43 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 3) _ validLayout0171) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind03099_0) certificate0062

private theorem bind03100_0 : Agrees (spec (fastBase 0 43 4) layout0171) scope0055 := by decide

theorem reject03100 : Rejected (base 0 43 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 4) _ validLayout0171) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind03100_0) certificate0057

private theorem bind03101_0 : Agrees (spec (fastBase 0 43 5) layout0171) scope0076 := by decide

private theorem bind03101_1 : Agrees (spec (fastBase 0 43 5) layout0172) scope0063 := by decide

theorem reject03101 : Rejected (base 0 43 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0171 layout0172 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 5) _ validLayout0171) (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 5) _ validLayout0172) (by decide) (by decide) scope0076 scope0063 (by rw [← fastBase_exact]; exact bind03101_0) (by rw [← fastBase_exact]; exact bind03101_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0078 certificate0079 (by decide)

private theorem bind03102_0 : Agrees (spec (fastBase 0 43 6) layout0171) scope0064 := by decide

theorem reject03102 : Rejected (base 0 43 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 6) _ validLayout0171) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind03102_0) certificate0066

private theorem bind03103_0 : Agrees (spec (fastBase 0 43 7) layout0171) scope0066 := by decide

theorem reject03103 : Rejected (base 0 43 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 7) _ validLayout0171) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind03103_0) certificate0068

private theorem bind03104_0 : Agrees (spec (fastBase 0 43 8) layout0171) scope0061 := by decide

theorem reject03104 : Rejected (base 0 43 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 8) _ validLayout0171) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind03104_0) certificate0063

private theorem bind03105_0 : Agrees (spec (fastBase 0 43 9) layout0171) scope0067 := by decide

theorem reject03105 : Rejected (base 0 43 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 9) _ validLayout0171) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind03105_0) certificate0069

private theorem bind03106_0 : Agrees (spec (fastBase 0 43 10) layout0171) scope0062 := by decide

private theorem bind03106_1 : Agrees (spec (fastBase 0 43 10) layout0172) scope0057 := by decide

theorem reject03106 : Rejected (base 0 43 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0171 layout0172 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 10) _ validLayout0171) (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 10) _ validLayout0172) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind03106_0) (by rw [← fastBase_exact]; exact bind03106_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind03107_0 : Agrees (spec (fastBase 0 43 11) layout0171) scope0065 := by decide

theorem reject03107 : Rejected (base 0 43 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 11) _ validLayout0171) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind03107_0) certificate0067

private theorem bind03108_0 : Agrees (spec (fastBase 0 43 12) layout0171) scope0056 := by decide

theorem reject03108 : Rejected (base 0 43 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 12) _ validLayout0171) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind03108_0) certificate0058

private theorem bind03109_0 : Agrees (spec (fastBase 0 43 13) layout0173) scope0199 := by decide

theorem reject03109 : Rejected (base 0 43 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0173 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 13) _ validLayout0173) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind03109_0) certificate0202

private theorem bind03110_0 : Agrees (spec (fastBase 0 43 14) layout0171) scope0076 := by decide

private theorem bind03110_1 : Agrees (spec (fastBase 0 43 14) layout0172) scope0063 := by decide

theorem reject03110 : Rejected (base 0 43 14) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0171 layout0172 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 14) _ validLayout0171) (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 14) _ validLayout0172) (by decide) (by decide) scope0076 scope0063 (by rw [← fastBase_exact]; exact bind03110_0) (by rw [← fastBase_exact]; exact bind03110_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0078 certificate0079 (by decide)

private theorem bind03111_0 : Agrees (spec (fastBase 0 43 15) layout0171) scope0074 := by decide

theorem reject03111 : Rejected (base 0 43 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 15) _ validLayout0171) (by decide) scope0074 (by rw [← fastBase_exact]; exact bind03111_0) certificate0076

private theorem bind03112_0 : Agrees (spec (fastBase 0 43 16) layout0171) scope0061 := by decide

theorem reject03112 : Rejected (base 0 43 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 16) _ validLayout0171) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind03112_0) certificate0063

private theorem bind03113_0 : Agrees (spec (fastBase 0 43 17) layout0171) scope0059 := by decide

theorem reject03113 : Rejected (base 0 43 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 17) _ validLayout0171) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind03113_0) certificate0061

private theorem bind03114_0 : Agrees (spec (fastBase 0 43 18) layout0171) scope0059 := by decide

theorem reject03114 : Rejected (base 0 43 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 18) _ validLayout0171) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind03114_0) certificate0061

private theorem bind03115_0 : Agrees (spec (fastBase 0 43 19) layout0171) scope0059 := by decide

theorem reject03115 : Rejected (base 0 43 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 19) _ validLayout0171) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind03115_0) certificate0061

private theorem bind03116_0 : Agrees (spec (fastBase 0 43 20) layout0171) scope0059 := by decide

theorem reject03116 : Rejected (base 0 43 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 20) _ validLayout0171) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind03116_0) certificate0061

private theorem bind03117_0 : Agrees (spec (fastBase 0 43 21) layout0171) scope0059 := by decide

theorem reject03117 : Rejected (base 0 43 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 21) _ validLayout0171) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind03117_0) certificate0061

private theorem bind03118_0 : Agrees (spec (fastBase 0 43 22) layout0171) scope0068 := by decide

theorem reject03118 : Rejected (base 0 43 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 22) _ validLayout0171) (by decide) scope0068 (by rw [← fastBase_exact]; exact bind03118_0) certificate0070

private theorem bind03119_0 : Agrees (spec (fastBase 0 43 23) layout0171) scope0055 := by decide

theorem reject03119 : Rejected (base 0 43 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 23) _ validLayout0171) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind03119_0) certificate0057

private theorem bind03120_0 : Agrees (spec (fastBase 0 43 24) layout0171) scope0069 := by decide

theorem reject03120 : Rejected (base 0 43 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 24) _ validLayout0171) (by decide) scope0069 (by rw [← fastBase_exact]; exact bind03120_0) certificate0071

private theorem bind03121_0 : Agrees (spec (fastBase 0 43 25) layout0171) scope0064 := by decide

theorem reject03121 : Rejected (base 0 43 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 25) _ validLayout0171) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind03121_0) certificate0066

private theorem bind03122_0 : Agrees (spec (fastBase 0 43 26) layout0171) scope0054 := by decide

theorem reject03122 : Rejected (base 0 43 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 26) _ validLayout0171) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind03122_0) certificate0056

private theorem bind03123_0 : Agrees (spec (fastBase 0 43 27) layout0171) scope0060 := by decide

theorem reject03123 : Rejected (base 0 43 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 27) _ validLayout0171) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind03123_0) certificate0062

private theorem bind03124_0 : Agrees (spec (fastBase 0 43 28) layout0171) scope0077 := by decide

theorem reject03124 : Rejected (base 0 43 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 28) _ validLayout0171) (by decide) scope0077 (by rw [← fastBase_exact]; exact bind03124_0) certificate0080

private theorem bind03125_0 : Agrees (spec (fastBase 0 43 29) layout0173) scope0203 := by decide

theorem reject03125 : Rejected (base 0 43 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0173 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 29) _ validLayout0173) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03125_0) certificate0206

private theorem bind03126_0 : Agrees (spec (fastBase 0 43 30) layout0171) scope0066 := by decide

theorem reject03126 : Rejected (base 0 43 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 30) _ validLayout0171) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind03126_0) certificate0068

private theorem bind03127_0 : Agrees (spec (fastBase 0 43 31) layout0171) scope0065 := by decide

theorem reject03127 : Rejected (base 0 43 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 31) _ validLayout0171) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind03127_0) certificate0067

private theorem bind03128_0 : Agrees (spec (fastBase 0 43 32) layout0171) scope0055 := by decide

theorem reject03128 : Rejected (base 0 43 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 32) _ validLayout0171) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind03128_0) certificate0057

private theorem bind03129_0 : Agrees (spec (fastBase 0 43 33) layout0171) scope0054 := by decide

theorem reject03129 : Rejected (base 0 43 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 33) _ validLayout0171) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind03129_0) certificate0056

private theorem bind03130_0 : Agrees (spec (fastBase 0 43 34) layout0173) scope0193 := by decide

theorem reject03130 : Rejected (base 0 43 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0173 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 34) _ validLayout0173) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind03130_0) certificate0196

private theorem bind03131_0 : Agrees (spec (fastBase 0 43 35) layout0171) scope0061 := by decide

theorem reject03131 : Rejected (base 0 43 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 35) _ validLayout0171) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind03131_0) certificate0063

private theorem bind03132_0 : Agrees (spec (fastBase 0 43 36) layout0171) scope0071 := by decide

theorem reject03132 : Rejected (base 0 43 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 36) _ validLayout0171) (by decide) scope0071 (by rw [← fastBase_exact]; exact bind03132_0) certificate0073

private theorem bind03133_0 : Agrees (spec (fastBase 0 43 37) layout0171) scope0056 := by decide

theorem reject03133 : Rejected (base 0 43 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 37) _ validLayout0171) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind03133_0) certificate0058

private theorem bind03134_0 : Agrees (spec (fastBase 0 43 38) layout0171) scope0070 := by decide

theorem reject03134 : Rejected (base 0 43 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 38) _ validLayout0171) (by decide) scope0070 (by rw [← fastBase_exact]; exact bind03134_0) certificate0072

private theorem bind03135_0 : Agrees (spec (fastBase 0 43 39) layout0171) scope0075 := by decide

theorem reject03135 : Rejected (base 0 43 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 39) _ validLayout0171) (by decide) scope0075 (by rw [← fastBase_exact]; exact bind03135_0) certificate0077

private theorem bind03136_0 : Agrees (spec (fastBase 0 43 40) layout0171) scope0067 := by decide

theorem reject03136 : Rejected (base 0 43 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 40) _ validLayout0171) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind03136_0) certificate0069

private theorem bind03137_0 : Agrees (spec (fastBase 0 43 41) layout0174) scope0422 := by decide

private theorem bind03137_1 : Agrees (spec (fastBase 0 43 41) layout0175) scope0058 := by decide

theorem reject03137 : Rejected (base 0 43 41) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0174 layout0175 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 41) _ validLayout0174) (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 41) _ validLayout0175) (by decide) (by decide) scope0422 scope0058 (by rw [← fastBase_exact]; exact bind03137_0) (by rw [← fastBase_exact]; exact bind03137_1) 3 8 3 8 (by decide) (by decide) 3 2 (by decide) certificate0445 certificate0446 (by decide)

private theorem bind03138_0 : Agrees (spec (fastBase 0 43 42) layout0171) scope0064 := by decide

theorem reject03138 : Rejected (base 0 43 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 42) _ validLayout0171) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind03138_0) certificate0066

private theorem bind03139_0 : Agrees (spec (fastBase 0 43 43) layout0171) scope0054 := by decide

theorem reject03139 : Rejected (base 0 43 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 43) _ validLayout0171) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind03139_0) certificate0056

private theorem bind03140_0 : Agrees (spec (fastBase 0 43 44) layout0171) scope0071 := by decide

theorem reject03140 : Rejected (base 0 43 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 44) _ validLayout0171) (by decide) scope0071 (by rw [← fastBase_exact]; exact bind03140_0) certificate0073

private theorem bind03141_0 : Agrees (spec (fastBase 0 43 45) layout0171) scope0077 := by decide

theorem reject03141 : Rejected (base 0 43 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 45) _ validLayout0171) (by decide) scope0077 (by rw [← fastBase_exact]; exact bind03141_0) certificate0080

private theorem bind03142_0 : Agrees (spec (fastBase 0 43 46) layout0171) scope0065 := by decide

theorem reject03142 : Rejected (base 0 43 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 46) _ validLayout0171) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind03142_0) certificate0067

private theorem bind03143_0 : Agrees (spec (fastBase 0 43 47) layout0171) scope0075 := by decide

theorem reject03143 : Rejected (base 0 43 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 47) _ validLayout0171) (by decide) scope0075 (by rw [← fastBase_exact]; exact bind03143_0) certificate0077

private theorem bind03144_0 : Agrees (spec (fastBase 0 43 48) layout0171) scope0060 := by decide

theorem reject03144 : Rejected (base 0 43 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 48) _ validLayout0171) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind03144_0) certificate0062

private theorem bind03145_0 : Agrees (spec (fastBase 0 43 49) layout0171) scope0080 := by decide

theorem reject03145 : Rejected (base 0 43 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 49) _ validLayout0171) (by decide) scope0080 (by rw [← fastBase_exact]; exact bind03145_0) certificate0083

private theorem bind03146_0 : Agrees (spec (fastBase 0 43 50) layout0171) scope0067 := by decide

theorem reject03146 : Rejected (base 0 43 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 50) _ validLayout0171) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind03146_0) certificate0069

private theorem bind03147_0 : Agrees (spec (fastBase 0 43 51) layout0171) scope0066 := by decide

theorem reject03147 : Rejected (base 0 43 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 51) _ validLayout0171) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind03147_0) certificate0068

private theorem bind03148_0 : Agrees (spec (fastBase 0 43 52) layout0171) scope0056 := by decide

theorem reject03148 : Rejected (base 0 43 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 52) _ validLayout0171) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind03148_0) certificate0058

private theorem bind03149_0 : Agrees (spec (fastBase 0 43 53) layout0171) scope0055 := by decide

theorem reject03149 : Rejected (base 0 43 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 53) _ validLayout0171) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind03149_0) certificate0057

private theorem bind03150_0 : Agrees (spec (fastBase 0 43 54) layout0171) scope0068 := by decide

theorem reject03150 : Rejected (base 0 43 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 54) _ validLayout0171) (by decide) scope0068 (by rw [← fastBase_exact]; exact bind03150_0) certificate0070

private theorem bind03151_0 : Agrees (spec (fastBase 0 43 55) layout0171) scope0070 := by decide

theorem reject03151 : Rejected (base 0 43 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 55) _ validLayout0171) (by decide) scope0070 (by rw [← fastBase_exact]; exact bind03151_0) certificate0072

private theorem bind03152_0 : Agrees (spec (fastBase 0 43 56) layout0171) scope0061 := by decide

theorem reject03152 : Rejected (base 0 43 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 56) _ validLayout0171) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind03152_0) certificate0063

private theorem bind03153_0 : Agrees (spec (fastBase 0 43 57) layout0171) scope0067 := by decide

theorem reject03153 : Rejected (base 0 43 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 57) _ validLayout0171) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind03153_0) certificate0069

private theorem bind03154_0 : Agrees (spec (fastBase 0 43 58) layout0173) scope0185 := by decide

theorem reject03154 : Rejected (base 0 43 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0173 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 58) _ validLayout0173) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03154_0) certificate0188

private theorem bind03155_0 : Agrees (spec (fastBase 0 43 59) layout0171) scope0074 := by decide

theorem reject03155 : Rejected (base 0 43 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 59) _ validLayout0171) (by decide) scope0074 (by rw [← fastBase_exact]; exact bind03155_0) certificate0076

private theorem bind03156_0 : Agrees (spec (fastBase 0 43 60) layout0171) scope0066 := by decide

theorem reject03156 : Rejected (base 0 43 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 60) _ validLayout0171) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind03156_0) certificate0068

private theorem bind03157_0 : Agrees (spec (fastBase 0 43 61) layout0173) scope0203 := by decide

theorem reject03157 : Rejected (base 0 43 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0173 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 61) _ validLayout0173) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03157_0) certificate0206

private theorem bind03158_0 : Agrees (spec (fastBase 0 43 62) layout0174) scope0420 := by decide

theorem reject03158 : Rejected (base 0 43 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0174 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 62) _ validLayout0174) (by decide) scope0420 (by rw [← fastBase_exact]; exact bind03158_0) certificate0443

private theorem bind03159_0 : Agrees (spec (fastBase 0 43 63) layout0171) scope0062 := by decide

private theorem bind03159_1 : Agrees (spec (fastBase 0 43 63) layout0172) scope0063 := by decide

theorem reject03159 : Rejected (base 0 43 63) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0171 layout0172 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 63) _ validLayout0171) (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 63) _ validLayout0172) (by decide) (by decide) scope0062 scope0063 (by rw [← fastBase_exact]; exact bind03159_0) (by rw [← fastBase_exact]; exact bind03159_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0065 (by decide)

private theorem bind03160_0 : Agrees (spec (fastBase 0 43 64) layout0174) scope0423 := by decide

theorem reject03160 : Rejected (base 0 43 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0174 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 64) _ validLayout0174) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind03160_0) certificate0447

private theorem bind03161_0 : Agrees (spec (fastBase 0 43 65) layout0171) scope0062 := by decide

private theorem bind03161_1 : Agrees (spec (fastBase 0 43 65) layout0172) scope0057 := by decide

theorem reject03161 : Rejected (base 0 43 65) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0171 layout0172 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 65) _ validLayout0171) (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 65) _ validLayout0172) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind03161_0) (by rw [← fastBase_exact]; exact bind03161_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind03162_0 : Agrees (spec (fastBase 0 43 66) layout0174) scope0424 := by decide

theorem reject03162 : Rejected (base 0 43 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0174 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 66) _ validLayout0174) (by decide) scope0424 (by rw [← fastBase_exact]; exact bind03162_0) certificate0448

private theorem bind03163_0 : Agrees (spec (fastBase 0 43 67) layout0171) scope0060 := by decide

theorem reject03163 : Rejected (base 0 43 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 67) _ validLayout0171) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind03163_0) certificate0062

private theorem bind03164_0 : Agrees (spec (fastBase 0 43 68) layout0171) scope0069 := by decide

theorem reject03164 : Rejected (base 0 43 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 68) _ validLayout0171) (by decide) scope0069 (by rw [← fastBase_exact]; exact bind03164_0) certificate0071

private theorem bind03165_0 : Agrees (spec (fastBase 0 43 69) layout0171) scope0064 := by decide

theorem reject03165 : Rejected (base 0 43 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 69) _ validLayout0171) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind03165_0) certificate0066

private theorem bind03166_0 : Agrees (spec (fastBase 0 43 70) layout0171) scope0080 := by decide

theorem reject03166 : Rejected (base 0 43 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 70) _ validLayout0171) (by decide) scope0080 (by rw [← fastBase_exact]; exact bind03166_0) certificate0083

private theorem bind03167_0 : Agrees (spec (fastBase 0 43 71) layout0171) scope0065 := by decide

theorem reject03167 : Rejected (base 0 43 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0171 (layoutValid_of_refines _ _ (base_refines_skeleton 0 43 71) _ validLayout0171) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind03167_0) certificate0067

theorem allCases043 : ∀ y : Fin 72, Rejected (base 0 43 y) := by
  intro y
  fin_cases y

  · exact reject03096

  · exact reject03097

  · exact reject03098

  · exact reject03099

  · exact reject03100

  · exact reject03101

  · exact reject03102

  · exact reject03103

  · exact reject03104

  · exact reject03105

  · exact reject03106

  · exact reject03107

  · exact reject03108

  · exact reject03109

  · exact reject03110

  · exact reject03111

  · exact reject03112

  · exact reject03113

  · exact reject03114

  · exact reject03115

  · exact reject03116

  · exact reject03117

  · exact reject03118

  · exact reject03119

  · exact reject03120

  · exact reject03121

  · exact reject03122

  · exact reject03123

  · exact reject03124

  · exact reject03125

  · exact reject03126

  · exact reject03127

  · exact reject03128

  · exact reject03129

  · exact reject03130

  · exact reject03131

  · exact reject03132

  · exact reject03133

  · exact reject03134

  · exact reject03135

  · exact reject03136

  · exact reject03137

  · exact reject03138

  · exact reject03139

  · exact reject03140

  · exact reject03141

  · exact reject03142

  · exact reject03143

  · exact reject03144

  · exact reject03145

  · exact reject03146

  · exact reject03147

  · exact reject03148

  · exact reject03149

  · exact reject03150

  · exact reject03151

  · exact reject03152

  · exact reject03153

  · exact reject03154

  · exact reject03155

  · exact reject03156

  · exact reject03157

  · exact reject03158

  · exact reject03159

  · exact reject03160

  · exact reject03161

  · exact reject03162

  · exact reject03163

  · exact reject03164

  · exact reject03165

  · exact reject03166

  · exact reject03167

end PricingIntegration.RemainingGWitnesses
