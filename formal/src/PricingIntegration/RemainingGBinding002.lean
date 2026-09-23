import PricingIntegration.RemainingGLayouts001

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks004

import PricingIntegration.RemainingGScopeChecks005


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00144_0 : Agrees (spec (fastBase 0 2 0) layout0010) scope0054 := by decide

theorem reject00144 : Rejected (base 0 2 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 0) _ validLayout0010) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind00144_0) certificate0056

private theorem bind00145_0 : Agrees (spec (fastBase 0 2 1) layout0010) scope0055 := by decide

theorem reject00145 : Rejected (base 0 2 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 1) _ validLayout0010) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind00145_0) certificate0057

private theorem bind00146_0 : Agrees (spec (fastBase 0 2 2) layout0010) scope0056 := by decide

theorem reject00146 : Rejected (base 0 2 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 2) _ validLayout0010) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind00146_0) certificate0058

private theorem bind00147_0 : Agrees (spec (fastBase 0 2 3) layout0011) scope0057 := by decide

private theorem bind00147_1 : Agrees (spec (fastBase 0 2 3) layout0012) scope0058 := by decide

theorem reject00147 : Rejected (base 0 2 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0011 layout0012 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 3) _ validLayout0011) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 3) _ validLayout0012) (by decide) (by decide) scope0057 scope0058 (by rw [← fastBase_exact]; exact bind00147_0) (by rw [← fastBase_exact]; exact bind00147_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0059 certificate0060 (by decide)

private theorem bind00148_0 : Agrees (spec (fastBase 0 2 4) layout0010) scope0059 := by decide

theorem reject00148 : Rejected (base 0 2 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 4) _ validLayout0010) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind00148_0) certificate0061

private theorem bind00149_0 : Agrees (spec (fastBase 0 2 5) layout0010) scope0060 := by decide

theorem reject00149 : Rejected (base 0 2 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 5) _ validLayout0010) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind00149_0) certificate0062

private theorem bind00150_0 : Agrees (spec (fastBase 0 2 6) layout0010) scope0061 := by decide

theorem reject00150 : Rejected (base 0 2 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 6) _ validLayout0010) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind00150_0) certificate0063

private theorem bind00151_0 : Agrees (spec (fastBase 0 2 7) layout0013) scope0062 := by decide

private theorem bind00151_1 : Agrees (spec (fastBase 0 2 7) layout0011) scope0063 := by decide

theorem reject00151 : Rejected (base 0 2 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0013 layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 7) _ validLayout0013) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 7) _ validLayout0011) (by decide) (by decide) scope0062 scope0063 (by rw [← fastBase_exact]; exact bind00151_0) (by rw [← fastBase_exact]; exact bind00151_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0065 (by decide)

private theorem bind00152_0 : Agrees (spec (fastBase 0 2 8) layout0010) scope0064 := by decide

theorem reject00152 : Rejected (base 0 2 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 8) _ validLayout0010) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind00152_0) certificate0066

private theorem bind00153_0 : Agrees (spec (fastBase 0 2 9) layout0010) scope0065 := by decide

theorem reject00153 : Rejected (base 0 2 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 9) _ validLayout0010) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind00153_0) certificate0067

private theorem bind00154_0 : Agrees (spec (fastBase 0 2 10) layout0010) scope0066 := by decide

theorem reject00154 : Rejected (base 0 2 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 10) _ validLayout0010) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind00154_0) certificate0068

private theorem bind00155_0 : Agrees (spec (fastBase 0 2 11) layout0010) scope0067 := by decide

theorem reject00155 : Rejected (base 0 2 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 11) _ validLayout0010) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind00155_0) certificate0069

private theorem bind00156_0 : Agrees (spec (fastBase 0 2 12) layout0010) scope0055 := by decide

theorem reject00156 : Rejected (base 0 2 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 12) _ validLayout0010) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind00156_0) certificate0057

private theorem bind00157_0 : Agrees (spec (fastBase 0 2 13) layout0010) scope0068 := by decide

theorem reject00157 : Rejected (base 0 2 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 13) _ validLayout0010) (by decide) scope0068 (by rw [← fastBase_exact]; exact bind00157_0) certificate0070

private theorem bind00158_0 : Agrees (spec (fastBase 0 2 14) layout0010) scope0069 := by decide

theorem reject00158 : Rejected (base 0 2 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 14) _ validLayout0010) (by decide) scope0069 (by rw [← fastBase_exact]; exact bind00158_0) certificate0071

private theorem bind00159_0 : Agrees (spec (fastBase 0 2 15) layout0010) scope0054 := by decide

theorem reject00159 : Rejected (base 0 2 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 15) _ validLayout0010) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind00159_0) certificate0056

private theorem bind00160_0 : Agrees (spec (fastBase 0 2 16) layout0010) scope0064 := by decide

theorem reject00160 : Rejected (base 0 2 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 16) _ validLayout0010) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind00160_0) certificate0066

private theorem bind00161_0 : Agrees (spec (fastBase 0 2 17) layout0010) scope0054 := by decide

theorem reject00161 : Rejected (base 0 2 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 17) _ validLayout0010) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind00161_0) certificate0056

private theorem bind00162_0 : Agrees (spec (fastBase 0 2 18) layout0013) scope0070 := by decide

theorem reject00162 : Rejected (base 0 2 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0013 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 18) _ validLayout0013) (by decide) scope0070 (by rw [← fastBase_exact]; exact bind00162_0) certificate0072

private theorem bind00163_0 : Agrees (spec (fastBase 0 2 19) layout0010) scope0055 := by decide

theorem reject00163 : Rejected (base 0 2 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 19) _ validLayout0010) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind00163_0) certificate0057

private theorem bind00164_0 : Agrees (spec (fastBase 0 2 20) layout0010) scope0061 := by decide

theorem reject00164 : Rejected (base 0 2 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 20) _ validLayout0010) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind00164_0) certificate0063

private theorem bind00165_0 : Agrees (spec (fastBase 0 2 21) layout0010) scope0071 := by decide

theorem reject00165 : Rejected (base 0 2 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 21) _ validLayout0010) (by decide) scope0071 (by rw [← fastBase_exact]; exact bind00165_0) certificate0073

private theorem bind00166_0 : Agrees (spec (fastBase 0 2 22) layout0011) scope0072 := by decide

theorem reject00166 : Rejected (base 0 2 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 22) _ validLayout0011) (by decide) scope0072 (by rw [← fastBase_exact]; exact bind00166_0) certificate0074

private theorem bind00167_0 : Agrees (spec (fastBase 0 2 23) layout0010) scope0056 := by decide

theorem reject00167 : Rejected (base 0 2 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 23) _ validLayout0010) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind00167_0) certificate0058

private theorem bind00168_0 : Agrees (spec (fastBase 0 2 24) layout0014) scope0073 := by decide

theorem reject00168 : Rejected (base 0 2 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0014 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 24) _ validLayout0014) (by decide) scope0073 (by rw [← fastBase_exact]; exact bind00168_0) certificate0075

private theorem bind00169_0 : Agrees (spec (fastBase 0 2 25) layout0010) scope0061 := by decide

theorem reject00169 : Rejected (base 0 2 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 25) _ validLayout0010) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind00169_0) certificate0063

private theorem bind00170_0 : Agrees (spec (fastBase 0 2 26) layout0010) scope0074 := by decide

theorem reject00170 : Rejected (base 0 2 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 26) _ validLayout0010) (by decide) scope0074 (by rw [← fastBase_exact]; exact bind00170_0) certificate0076

private theorem bind00171_0 : Agrees (spec (fastBase 0 2 27) layout0010) scope0070 := by decide

theorem reject00171 : Rejected (base 0 2 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 27) _ validLayout0010) (by decide) scope0070 (by rw [← fastBase_exact]; exact bind00171_0) certificate0072

private theorem bind00172_0 : Agrees (spec (fastBase 0 2 28) layout0010) scope0056 := by decide

theorem reject00172 : Rejected (base 0 2 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 28) _ validLayout0010) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind00172_0) certificate0058

private theorem bind00173_0 : Agrees (spec (fastBase 0 2 29) layout0010) scope0075 := by decide

theorem reject00173 : Rejected (base 0 2 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 29) _ validLayout0010) (by decide) scope0075 (by rw [← fastBase_exact]; exact bind00173_0) certificate0077

private theorem bind00174_0 : Agrees (spec (fastBase 0 2 30) layout0013) scope0076 := by decide

private theorem bind00174_1 : Agrees (spec (fastBase 0 2 30) layout0011) scope0063 := by decide

theorem reject00174 : Rejected (base 0 2 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0013 layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 30) _ validLayout0013) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 30) _ validLayout0011) (by decide) (by decide) scope0076 scope0063 (by rw [← fastBase_exact]; exact bind00174_0) (by rw [← fastBase_exact]; exact bind00174_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0078 certificate0079 (by decide)

private theorem bind00175_0 : Agrees (spec (fastBase 0 2 31) layout0010) scope0067 := by decide

theorem reject00175 : Rejected (base 0 2 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 31) _ validLayout0010) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind00175_0) certificate0069

private theorem bind00176_0 : Agrees (spec (fastBase 0 2 32) layout0010) scope0059 := by decide

theorem reject00176 : Rejected (base 0 2 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 32) _ validLayout0010) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind00176_0) certificate0061

private theorem bind00177_0 : Agrees (spec (fastBase 0 2 33) layout0010) scope0059 := by decide

theorem reject00177 : Rejected (base 0 2 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 33) _ validLayout0010) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind00177_0) certificate0061

private theorem bind00178_0 : Agrees (spec (fastBase 0 2 34) layout0010) scope0059 := by decide

theorem reject00178 : Rejected (base 0 2 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 34) _ validLayout0010) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind00178_0) certificate0061

private theorem bind00179_0 : Agrees (spec (fastBase 0 2 35) layout0010) scope0059 := by decide

theorem reject00179 : Rejected (base 0 2 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 35) _ validLayout0010) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind00179_0) certificate0061

private theorem bind00180_0 : Agrees (spec (fastBase 0 2 36) layout0010) scope0059 := by decide

theorem reject00180 : Rejected (base 0 2 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 36) _ validLayout0010) (by decide) scope0059 (by rw [← fastBase_exact]; exact bind00180_0) certificate0061

private theorem bind00181_0 : Agrees (spec (fastBase 0 2 37) layout0010) scope0077 := by decide

theorem reject00181 : Rejected (base 0 2 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 37) _ validLayout0010) (by decide) scope0077 (by rw [← fastBase_exact]; exact bind00181_0) certificate0080

private theorem bind00182_0 : Agrees (spec (fastBase 0 2 38) layout0010) scope0060 := by decide

theorem reject00182 : Rejected (base 0 2 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 38) _ validLayout0010) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind00182_0) certificate0062

private theorem bind00183_0 : Agrees (spec (fastBase 0 2 39) layout0013) scope0078 := by decide

private theorem bind00183_1 : Agrees (spec (fastBase 0 2 39) layout0014) scope0079 := by decide

theorem reject00183 : Rejected (base 0 2 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0013 layout0014 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 39) _ validLayout0013) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 39) _ validLayout0014) (by decide) (by decide) scope0078 scope0079 (by rw [← fastBase_exact]; exact bind00183_0) (by rw [← fastBase_exact]; exact bind00183_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0081 certificate0082 (by decide)

private theorem bind00184_0 : Agrees (spec (fastBase 0 2 40) layout0010) scope0065 := by decide

theorem reject00184 : Rejected (base 0 2 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 40) _ validLayout0010) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind00184_0) certificate0067

private theorem bind00185_0 : Agrees (spec (fastBase 0 2 41) layout0010) scope0066 := by decide

theorem reject00185 : Rejected (base 0 2 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 41) _ validLayout0010) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind00185_0) certificate0068

private theorem bind00186_0 : Agrees (spec (fastBase 0 2 42) layout0010) scope0055 := by decide

theorem reject00186 : Rejected (base 0 2 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 42) _ validLayout0010) (by decide) scope0055 (by rw [← fastBase_exact]; exact bind00186_0) certificate0057

private theorem bind00187_0 : Agrees (spec (fastBase 0 2 43) layout0010) scope0056 := by decide

theorem reject00187 : Rejected (base 0 2 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 43) _ validLayout0010) (by decide) scope0056 (by rw [← fastBase_exact]; exact bind00187_0) certificate0058

private theorem bind00188_0 : Agrees (spec (fastBase 0 2 44) layout0010) scope0068 := by decide

theorem reject00188 : Rejected (base 0 2 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 44) _ validLayout0010) (by decide) scope0068 (by rw [← fastBase_exact]; exact bind00188_0) certificate0070

private theorem bind00189_0 : Agrees (spec (fastBase 0 2 45) layout0010) scope0061 := by decide

theorem reject00189 : Rejected (base 0 2 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 45) _ validLayout0010) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind00189_0) certificate0063

private theorem bind00190_0 : Agrees (spec (fastBase 0 2 46) layout0010) scope0070 := by decide

theorem reject00190 : Rejected (base 0 2 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 46) _ validLayout0010) (by decide) scope0070 (by rw [← fastBase_exact]; exact bind00190_0) certificate0072

private theorem bind00191_0 : Agrees (spec (fastBase 0 2 47) layout0013) scope0054 := by decide

theorem reject00191 : Rejected (base 0 2 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0013 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 47) _ validLayout0013) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind00191_0) certificate0056

private theorem bind00192_0 : Agrees (spec (fastBase 0 2 48) layout0013) scope0062 := by decide

private theorem bind00192_1 : Agrees (spec (fastBase 0 2 48) layout0011) scope0057 := by decide

theorem reject00192 : Rejected (base 0 2 48) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0013 layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 48) _ validLayout0013) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 48) _ validLayout0011) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind00192_0) (by rw [← fastBase_exact]; exact bind00192_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind00193_0 : Agrees (spec (fastBase 0 2 49) layout0013) scope0061 := by decide

theorem reject00193 : Rejected (base 0 2 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0013 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 49) _ validLayout0013) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind00193_0) certificate0063

private theorem bind00194_0 : Agrees (spec (fastBase 0 2 50) layout0013) scope0062 := by decide

private theorem bind00194_1 : Agrees (spec (fastBase 0 2 50) layout0011) scope0063 := by decide

theorem reject00194 : Rejected (base 0 2 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0013 layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 50) _ validLayout0013) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 50) _ validLayout0011) (by decide) (by decide) scope0062 scope0063 (by rw [← fastBase_exact]; exact bind00194_0) (by rw [← fastBase_exact]; exact bind00194_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0065 (by decide)

private theorem bind00195_0 : Agrees (spec (fastBase 0 2 51) layout0013) scope0062 := by decide

private theorem bind00195_1 : Agrees (spec (fastBase 0 2 51) layout0011) scope0063 := by decide

theorem reject00195 : Rejected (base 0 2 51) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0013 layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 51) _ validLayout0013) (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 51) _ validLayout0011) (by decide) (by decide) scope0062 scope0063 (by rw [← fastBase_exact]; exact bind00195_0) (by rw [← fastBase_exact]; exact bind00195_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0065 (by decide)

private theorem bind00196_0 : Agrees (spec (fastBase 0 2 52) layout0010) scope0054 := by decide

theorem reject00196 : Rejected (base 0 2 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 52) _ validLayout0010) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind00196_0) certificate0056

private theorem bind00197_0 : Agrees (spec (fastBase 0 2 53) layout0010) scope0064 := by decide

theorem reject00197 : Rejected (base 0 2 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 53) _ validLayout0010) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind00197_0) certificate0066

private theorem bind00198_0 : Agrees (spec (fastBase 0 2 54) layout0010) scope0071 := by decide

theorem reject00198 : Rejected (base 0 2 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 54) _ validLayout0010) (by decide) scope0071 (by rw [← fastBase_exact]; exact bind00198_0) certificate0073

private theorem bind00199_0 : Agrees (spec (fastBase 0 2 55) layout0010) scope0065 := by decide

theorem reject00199 : Rejected (base 0 2 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 55) _ validLayout0010) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind00199_0) certificate0067

private theorem bind00200_0 : Agrees (spec (fastBase 0 2 56) layout0010) scope0077 := by decide

theorem reject00200 : Rejected (base 0 2 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 56) _ validLayout0010) (by decide) scope0077 (by rw [← fastBase_exact]; exact bind00200_0) certificate0080

private theorem bind00201_0 : Agrees (spec (fastBase 0 2 57) layout0010) scope0069 := by decide

theorem reject00201 : Rejected (base 0 2 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 57) _ validLayout0010) (by decide) scope0069 (by rw [← fastBase_exact]; exact bind00201_0) certificate0071

private theorem bind00202_0 : Agrees (spec (fastBase 0 2 58) layout0010) scope0060 := by decide

theorem reject00202 : Rejected (base 0 2 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 58) _ validLayout0010) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind00202_0) certificate0062

private theorem bind00203_0 : Agrees (spec (fastBase 0 2 59) layout0010) scope0064 := by decide

theorem reject00203 : Rejected (base 0 2 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 59) _ validLayout0010) (by decide) scope0064 (by rw [← fastBase_exact]; exact bind00203_0) certificate0066

private theorem bind00204_0 : Agrees (spec (fastBase 0 2 60) layout0010) scope0065 := by decide

theorem reject00204 : Rejected (base 0 2 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 60) _ validLayout0010) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind00204_0) certificate0067

private theorem bind00205_0 : Agrees (spec (fastBase 0 2 61) layout0010) scope0080 := by decide

theorem reject00205 : Rejected (base 0 2 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 61) _ validLayout0010) (by decide) scope0080 (by rw [← fastBase_exact]; exact bind00205_0) certificate0083

private theorem bind00206_0 : Agrees (spec (fastBase 0 2 62) layout0010) scope0075 := by decide

theorem reject00206 : Rejected (base 0 2 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 62) _ validLayout0010) (by decide) scope0075 (by rw [← fastBase_exact]; exact bind00206_0) certificate0077

private theorem bind00207_0 : Agrees (spec (fastBase 0 2 63) layout0010) scope0060 := by decide

theorem reject00207 : Rejected (base 0 2 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 63) _ validLayout0010) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind00207_0) certificate0062

private theorem bind00208_0 : Agrees (spec (fastBase 0 2 64) layout0010) scope0066 := by decide

theorem reject00208 : Rejected (base 0 2 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 64) _ validLayout0010) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind00208_0) certificate0068

private theorem bind00209_0 : Agrees (spec (fastBase 0 2 65) layout0010) scope0080 := by decide

theorem reject00209 : Rejected (base 0 2 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 65) _ validLayout0010) (by decide) scope0080 (by rw [← fastBase_exact]; exact bind00209_0) certificate0083

private theorem bind00210_0 : Agrees (spec (fastBase 0 2 66) layout0010) scope0067 := by decide

theorem reject00210 : Rejected (base 0 2 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 66) _ validLayout0010) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind00210_0) certificate0069

private theorem bind00211_0 : Agrees (spec (fastBase 0 2 67) layout0013) scope0067 := by decide

theorem reject00211 : Rejected (base 0 2 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0013 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 67) _ validLayout0013) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind00211_0) certificate0069

private theorem bind00212_0 : Agrees (spec (fastBase 0 2 68) layout0010) scope0067 := by decide

theorem reject00212 : Rejected (base 0 2 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 68) _ validLayout0010) (by decide) scope0067 (by rw [← fastBase_exact]; exact bind00212_0) certificate0069

private theorem bind00213_0 : Agrees (spec (fastBase 0 2 69) layout0010) scope0074 := by decide

theorem reject00213 : Rejected (base 0 2 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 69) _ validLayout0010) (by decide) scope0074 (by rw [← fastBase_exact]; exact bind00213_0) certificate0076

private theorem bind00214_0 : Agrees (spec (fastBase 0 2 70) layout0011) scope0081 := by decide

theorem reject00214 : Rejected (base 0 2 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0011 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 70) _ validLayout0011) (by decide) scope0081 (by rw [← fastBase_exact]; exact bind00214_0) certificate0084

private theorem bind00215_0 : Agrees (spec (fastBase 0 2 71) layout0010) scope0066 := by decide

theorem reject00215 : Rejected (base 0 2 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0010 (layoutValid_of_refines _ _ (base_refines_skeleton 0 2 71) _ validLayout0010) (by decide) scope0066 (by rw [← fastBase_exact]; exact bind00215_0) certificate0068

theorem allCases002 : ∀ y : Fin 72, Rejected (base 0 2 y) := by
  intro y
  fin_cases y

  · exact reject00144

  · exact reject00145

  · exact reject00146

  · exact reject00147

  · exact reject00148

  · exact reject00149

  · exact reject00150

  · exact reject00151

  · exact reject00152

  · exact reject00153

  · exact reject00154

  · exact reject00155

  · exact reject00156

  · exact reject00157

  · exact reject00158

  · exact reject00159

  · exact reject00160

  · exact reject00161

  · exact reject00162

  · exact reject00163

  · exact reject00164

  · exact reject00165

  · exact reject00166

  · exact reject00167

  · exact reject00168

  · exact reject00169

  · exact reject00170

  · exact reject00171

  · exact reject00172

  · exact reject00173

  · exact reject00174

  · exact reject00175

  · exact reject00176

  · exact reject00177

  · exact reject00178

  · exact reject00179

  · exact reject00180

  · exact reject00181

  · exact reject00182

  · exact reject00183

  · exact reject00184

  · exact reject00185

  · exact reject00186

  · exact reject00187

  · exact reject00188

  · exact reject00189

  · exact reject00190

  · exact reject00191

  · exact reject00192

  · exact reject00193

  · exact reject00194

  · exact reject00195

  · exact reject00196

  · exact reject00197

  · exact reject00198

  · exact reject00199

  · exact reject00200

  · exact reject00201

  · exact reject00202

  · exact reject00203

  · exact reject00204

  · exact reject00205

  · exact reject00206

  · exact reject00207

  · exact reject00208

  · exact reject00209

  · exact reject00210

  · exact reject00211

  · exact reject00212

  · exact reject00213

  · exact reject00214

  · exact reject00215

end PricingIntegration.RemainingGWitnesses
