import PricingIntegration.RemainingGLayouts001

import PricingIntegration.RemainingGLayouts002

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks005

import PricingIntegration.RemainingGScopeChecks006


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00216_0 : Agrees (spec (fastBase 0 3 0) layout0015) scope0082 := by decide

theorem reject00216 : Rejected (base 0 3 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 0) _ validLayout0015) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind00216_0) certificate0085

private theorem bind00217_0 : Agrees (spec (fastBase 0 3 1) layout0015) scope0083 := by decide

theorem reject00217 : Rejected (base 0 3 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 1) _ validLayout0015) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind00217_0) certificate0086

private theorem bind00218_0 : Agrees (spec (fastBase 0 3 2) layout0015) scope0084 := by decide

theorem reject00218 : Rejected (base 0 3 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 2) _ validLayout0015) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind00218_0) certificate0087

private theorem bind00219_0 : Agrees (spec (fastBase 0 3 3) layout0015) scope0085 := by decide

theorem reject00219 : Rejected (base 0 3 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 3) _ validLayout0015) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind00219_0) certificate0088

private theorem bind00220_0 : Agrees (spec (fastBase 0 3 4) layout0015) scope0086 := by decide

theorem reject00220 : Rejected (base 0 3 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 4) _ validLayout0015) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind00220_0) certificate0089

private theorem bind00221_0 : Agrees (spec (fastBase 0 3 5) layout0015) scope0087 := by decide

theorem reject00221 : Rejected (base 0 3 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 5) _ validLayout0015) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind00221_0) certificate0090

private theorem bind00222_0 : Agrees (spec (fastBase 0 3 6) layout0015) scope0088 := by decide

theorem reject00222 : Rejected (base 0 3 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 6) _ validLayout0015) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind00222_0) certificate0091

private theorem bind00223_0 : Agrees (spec (fastBase 0 3 7) layout0015) scope0089 := by decide

theorem reject00223 : Rejected (base 0 3 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 7) _ validLayout0015) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind00223_0) certificate0092

private theorem bind00224_0 : Agrees (spec (fastBase 0 3 8) layout0015) scope0090 := by decide

theorem reject00224 : Rejected (base 0 3 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 8) _ validLayout0015) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind00224_0) certificate0093

private theorem bind00225_0 : Agrees (spec (fastBase 0 3 9) layout0016) scope0091 := by decide

private theorem bind00225_1 : Agrees (spec (fastBase 0 3 9) layout0017) scope0092 := by decide

theorem reject00225 : Rejected (base 0 3 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0016 layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 9) _ validLayout0016) (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 9) _ validLayout0017) (by decide) (by decide) scope0091 scope0092 (by rw [← fastBase_exact]; exact bind00225_0) (by rw [← fastBase_exact]; exact bind00225_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0094 certificate0095 (by decide)

private theorem bind00226_0 : Agrees (spec (fastBase 0 3 10) layout0015) scope0093 := by decide

theorem reject00226 : Rejected (base 0 3 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 10) _ validLayout0015) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind00226_0) certificate0096

private theorem bind00227_0 : Agrees (spec (fastBase 0 3 11) layout0016) scope0094 := by decide

private theorem bind00227_1 : Agrees (spec (fastBase 0 3 11) layout0017) scope0095 := by decide

theorem reject00227 : Rejected (base 0 3 11) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0016 layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 11) _ validLayout0016) (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 11) _ validLayout0017) (by decide) (by decide) scope0094 scope0095 (by rw [← fastBase_exact]; exact bind00227_0) (by rw [← fastBase_exact]; exact bind00227_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0097 certificate0098 (by decide)

private theorem bind00228_0 : Agrees (spec (fastBase 0 3 12) layout0015) scope0083 := by decide

theorem reject00228 : Rejected (base 0 3 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 12) _ validLayout0015) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind00228_0) certificate0086

private theorem bind00229_0 : Agrees (spec (fastBase 0 3 13) layout0015) scope0082 := by decide

theorem reject00229 : Rejected (base 0 3 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 13) _ validLayout0015) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind00229_0) certificate0085

private theorem bind00230_0 : Agrees (spec (fastBase 0 3 14) layout0015) scope0087 := by decide

theorem reject00230 : Rejected (base 0 3 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 14) _ validLayout0015) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind00230_0) certificate0090

private theorem bind00231_0 : Agrees (spec (fastBase 0 3 15) layout0015) scope0096 := by decide

theorem reject00231 : Rejected (base 0 3 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 15) _ validLayout0015) (by decide) scope0096 (by rw [← fastBase_exact]; exact bind00231_0) certificate0099

private theorem bind00232_0 : Agrees (spec (fastBase 0 3 16) layout0015) scope0097 := by decide

theorem reject00232 : Rejected (base 0 3 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 16) _ validLayout0015) (by decide) scope0097 (by rw [← fastBase_exact]; exact bind00232_0) certificate0100

private theorem bind00233_0 : Agrees (spec (fastBase 0 3 17) layout0015) scope0082 := by decide

theorem reject00233 : Rejected (base 0 3 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 17) _ validLayout0015) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind00233_0) certificate0085

private theorem bind00234_0 : Agrees (spec (fastBase 0 3 18) layout0015) scope0085 := by decide

theorem reject00234 : Rejected (base 0 3 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 18) _ validLayout0015) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind00234_0) certificate0088

private theorem bind00235_0 : Agrees (spec (fastBase 0 3 19) layout0015) scope0098 := by decide

theorem reject00235 : Rejected (base 0 3 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 19) _ validLayout0015) (by decide) scope0098 (by rw [← fastBase_exact]; exact bind00235_0) certificate0101

private theorem bind00236_0 : Agrees (spec (fastBase 0 3 20) layout0015) scope0099 := by decide

theorem reject00236 : Rejected (base 0 3 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 20) _ validLayout0015) (by decide) scope0099 (by rw [← fastBase_exact]; exact bind00236_0) certificate0102

private theorem bind00237_0 : Agrees (spec (fastBase 0 3 21) layout0015) scope0083 := by decide

theorem reject00237 : Rejected (base 0 3 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 21) _ validLayout0015) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind00237_0) certificate0086

private theorem bind00238_0 : Agrees (spec (fastBase 0 3 22) layout0015) scope0084 := by decide

theorem reject00238 : Rejected (base 0 3 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 22) _ validLayout0015) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind00238_0) certificate0087

private theorem bind00239_0 : Agrees (spec (fastBase 0 3 23) layout0015) scope0084 := by decide

theorem reject00239 : Rejected (base 0 3 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 23) _ validLayout0015) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind00239_0) certificate0087

private theorem bind00240_0 : Agrees (spec (fastBase 0 3 24) layout0015) scope0084 := by decide

theorem reject00240 : Rejected (base 0 3 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 24) _ validLayout0015) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind00240_0) certificate0087

private theorem bind00241_0 : Agrees (spec (fastBase 0 3 25) layout0015) scope0084 := by decide

theorem reject00241 : Rejected (base 0 3 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 25) _ validLayout0015) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind00241_0) certificate0087

private theorem bind00242_0 : Agrees (spec (fastBase 0 3 26) layout0015) scope0084 := by decide

theorem reject00242 : Rejected (base 0 3 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 26) _ validLayout0015) (by decide) scope0084 (by rw [← fastBase_exact]; exact bind00242_0) certificate0087

private theorem bind00243_0 : Agrees (spec (fastBase 0 3 27) layout0015) scope0083 := by decide

theorem reject00243 : Rejected (base 0 3 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 27) _ validLayout0015) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind00243_0) certificate0086

private theorem bind00244_0 : Agrees (spec (fastBase 0 3 28) layout0015) scope0085 := by decide

theorem reject00244 : Rejected (base 0 3 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 28) _ validLayout0015) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind00244_0) certificate0088

private theorem bind00245_0 : Agrees (spec (fastBase 0 3 29) layout0015) scope0096 := by decide

theorem reject00245 : Rejected (base 0 3 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 29) _ validLayout0015) (by decide) scope0096 (by rw [← fastBase_exact]; exact bind00245_0) certificate0099

private theorem bind00246_0 : Agrees (spec (fastBase 0 3 30) layout0015) scope0089 := by decide

theorem reject00246 : Rejected (base 0 3 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 30) _ validLayout0015) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind00246_0) certificate0092

private theorem bind00247_0 : Agrees (spec (fastBase 0 3 31) layout0016) scope0100 := by decide

theorem reject00247 : Rejected (base 0 3 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 31) _ validLayout0016) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind00247_0) certificate0103

private theorem bind00248_0 : Agrees (spec (fastBase 0 3 32) layout0015) scope0097 := by decide

theorem reject00248 : Rejected (base 0 3 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 32) _ validLayout0015) (by decide) scope0097 (by rw [← fastBase_exact]; exact bind00248_0) certificate0100

private theorem bind00249_0 : Agrees (spec (fastBase 0 3 33) layout0015) scope0086 := by decide

theorem reject00249 : Rejected (base 0 3 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 33) _ validLayout0015) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind00249_0) certificate0089

private theorem bind00250_0 : Agrees (spec (fastBase 0 3 34) layout0015) scope0087 := by decide

theorem reject00250 : Rejected (base 0 3 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 34) _ validLayout0015) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind00250_0) certificate0090

private theorem bind00251_0 : Agrees (spec (fastBase 0 3 35) layout0015) scope0090 := by decide

theorem reject00251 : Rejected (base 0 3 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 35) _ validLayout0015) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind00251_0) certificate0093

private theorem bind00252_0 : Agrees (spec (fastBase 0 3 36) layout0016) scope0101 := by decide

theorem reject00252 : Rejected (base 0 3 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 36) _ validLayout0016) (by decide) scope0101 (by rw [← fastBase_exact]; exact bind00252_0) certificate0104

private theorem bind00253_0 : Agrees (spec (fastBase 0 3 37) layout0015) scope0082 := by decide

theorem reject00253 : Rejected (base 0 3 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 37) _ validLayout0015) (by decide) scope0082 (by rw [← fastBase_exact]; exact bind00253_0) certificate0085

private theorem bind00254_0 : Agrees (spec (fastBase 0 3 38) layout0015) scope0086 := by decide

theorem reject00254 : Rejected (base 0 3 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 38) _ validLayout0015) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind00254_0) certificate0089

private theorem bind00255_0 : Agrees (spec (fastBase 0 3 39) layout0015) scope0098 := by decide

theorem reject00255 : Rejected (base 0 3 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 39) _ validLayout0015) (by decide) scope0098 (by rw [← fastBase_exact]; exact bind00255_0) certificate0101

private theorem bind00256_0 : Agrees (spec (fastBase 0 3 40) layout0015) scope0087 := by decide

theorem reject00256 : Rejected (base 0 3 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 40) _ validLayout0015) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind00256_0) certificate0090

private theorem bind00257_0 : Agrees (spec (fastBase 0 3 41) layout0015) scope0102 := by decide

theorem reject00257 : Rejected (base 0 3 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 41) _ validLayout0015) (by decide) scope0102 (by rw [← fastBase_exact]; exact bind00257_0) certificate0105

private theorem bind00258_0 : Agrees (spec (fastBase 0 3 42) layout0017) scope0103 := by decide

theorem reject00258 : Rejected (base 0 3 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 42) _ validLayout0017) (by decide) scope0103 (by rw [← fastBase_exact]; exact bind00258_0) certificate0106

private theorem bind00259_0 : Agrees (spec (fastBase 0 3 43) layout0015) scope0088 := by decide

theorem reject00259 : Rejected (base 0 3 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 43) _ validLayout0015) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind00259_0) certificate0091

private theorem bind00260_0 : Agrees (spec (fastBase 0 3 44) layout0015) scope0104 := by decide

theorem reject00260 : Rejected (base 0 3 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 44) _ validLayout0015) (by decide) scope0104 (by rw [← fastBase_exact]; exact bind00260_0) certificate0107

private theorem bind00261_0 : Agrees (spec (fastBase 0 3 45) layout0015) scope0089 := by decide

theorem reject00261 : Rejected (base 0 3 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 45) _ validLayout0015) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind00261_0) certificate0092

private theorem bind00262_0 : Agrees (spec (fastBase 0 3 46) layout0018) scope0105 := by decide

theorem reject00262 : Rejected (base 0 3 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0018 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 46) _ validLayout0018) (by decide) scope0105 (by rw [← fastBase_exact]; exact bind00262_0) certificate0108

private theorem bind00263_0 : Agrees (spec (fastBase 0 3 47) layout0015) scope0099 := by decide

theorem reject00263 : Rejected (base 0 3 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 47) _ validLayout0015) (by decide) scope0099 (by rw [← fastBase_exact]; exact bind00263_0) certificate0102

private theorem bind00264_0 : Agrees (spec (fastBase 0 3 48) layout0015) scope0085 := by decide

theorem reject00264 : Rejected (base 0 3 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 48) _ validLayout0015) (by decide) scope0085 (by rw [← fastBase_exact]; exact bind00264_0) certificate0088

private theorem bind00265_0 : Agrees (spec (fastBase 0 3 49) layout0015) scope0088 := by decide

theorem reject00265 : Rejected (base 0 3 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 49) _ validLayout0015) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind00265_0) certificate0091

private theorem bind00266_0 : Agrees (spec (fastBase 0 3 50) layout0015) scope0089 := by decide

theorem reject00266 : Rejected (base 0 3 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 50) _ validLayout0015) (by decide) scope0089 (by rw [← fastBase_exact]; exact bind00266_0) certificate0092

private theorem bind00267_0 : Agrees (spec (fastBase 0 3 51) layout0015) scope0100 := by decide

theorem reject00267 : Rejected (base 0 3 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 51) _ validLayout0015) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind00267_0) certificate0103

private theorem bind00268_0 : Agrees (spec (fastBase 0 3 52) layout0015) scope0102 := by decide

theorem reject00268 : Rejected (base 0 3 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 52) _ validLayout0015) (by decide) scope0102 (by rw [← fastBase_exact]; exact bind00268_0) certificate0105

private theorem bind00269_0 : Agrees (spec (fastBase 0 3 53) layout0015) scope0086 := by decide

theorem reject00269 : Rejected (base 0 3 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 53) _ validLayout0015) (by decide) scope0086 (by rw [← fastBase_exact]; exact bind00269_0) certificate0089

private theorem bind00270_0 : Agrees (spec (fastBase 0 3 54) layout0015) scope0101 := by decide

theorem reject00270 : Rejected (base 0 3 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 54) _ validLayout0015) (by decide) scope0101 (by rw [← fastBase_exact]; exact bind00270_0) certificate0104

private theorem bind00271_0 : Agrees (spec (fastBase 0 3 55) layout0015) scope0090 := by decide

theorem reject00271 : Rejected (base 0 3 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 55) _ validLayout0015) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind00271_0) certificate0093

private theorem bind00272_0 : Agrees (spec (fastBase 0 3 56) layout0015) scope0093 := by decide

theorem reject00272 : Rejected (base 0 3 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 56) _ validLayout0015) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind00272_0) certificate0096

private theorem bind00273_0 : Agrees (spec (fastBase 0 3 57) layout0016) scope0083 := by decide

theorem reject00273 : Rejected (base 0 3 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 57) _ validLayout0016) (by decide) scope0083 (by rw [← fastBase_exact]; exact bind00273_0) certificate0086

private theorem bind00274_0 : Agrees (spec (fastBase 0 3 58) layout0016) scope0087 := by decide

theorem reject00274 : Rejected (base 0 3 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0016 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 58) _ validLayout0016) (by decide) scope0087 (by rw [← fastBase_exact]; exact bind00274_0) certificate0090

private theorem bind00275_0 : Agrees (spec (fastBase 0 3 59) layout0018) scope0106 := by decide

theorem reject00275 : Rejected (base 0 3 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0018 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 59) _ validLayout0018) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind00275_0) certificate0109

private theorem bind00276_0 : Agrees (spec (fastBase 0 3 60) layout0016) scope0091 := by decide

private theorem bind00276_1 : Agrees (spec (fastBase 0 3 60) layout0017) scope0092 := by decide

theorem reject00276 : Rejected (base 0 3 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0016 layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 60) _ validLayout0016) (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 60) _ validLayout0017) (by decide) (by decide) scope0091 scope0092 (by rw [← fastBase_exact]; exact bind00276_0) (by rw [← fastBase_exact]; exact bind00276_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0094 certificate0095 (by decide)

private theorem bind00277_0 : Agrees (spec (fastBase 0 3 61) layout0016) scope0091 := by decide

private theorem bind00277_1 : Agrees (spec (fastBase 0 3 61) layout0017) scope0095 := by decide

theorem reject00277 : Rejected (base 0 3 61) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0016 layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 61) _ validLayout0016) (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 61) _ validLayout0017) (by decide) (by decide) scope0091 scope0095 (by rw [← fastBase_exact]; exact bind00277_0) (by rw [← fastBase_exact]; exact bind00277_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0094 certificate0098 (by decide)

private theorem bind00278_0 : Agrees (spec (fastBase 0 3 62) layout0015) scope0093 := by decide

theorem reject00278 : Rejected (base 0 3 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 62) _ validLayout0015) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind00278_0) certificate0096

private theorem bind00279_0 : Agrees (spec (fastBase 0 3 63) layout0017) scope0107 := by decide

theorem reject00279 : Rejected (base 0 3 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 63) _ validLayout0017) (by decide) scope0107 (by rw [← fastBase_exact]; exact bind00279_0) certificate0110

private theorem bind00280_0 : Agrees (spec (fastBase 0 3 64) layout0015) scope0104 := by decide

theorem reject00280 : Rejected (base 0 3 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 64) _ validLayout0015) (by decide) scope0104 (by rw [← fastBase_exact]; exact bind00280_0) certificate0107

private theorem bind00281_0 : Agrees (spec (fastBase 0 3 65) layout0015) scope0090 := by decide

theorem reject00281 : Rejected (base 0 3 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 65) _ validLayout0015) (by decide) scope0090 (by rw [← fastBase_exact]; exact bind00281_0) certificate0093

private theorem bind00282_0 : Agrees (spec (fastBase 0 3 66) layout0016) scope0094 := by decide

private theorem bind00282_1 : Agrees (spec (fastBase 0 3 66) layout0017) scope0095 := by decide

theorem reject00282 : Rejected (base 0 3 66) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0016 layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 66) _ validLayout0016) (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 66) _ validLayout0017) (by decide) (by decide) scope0094 scope0095 (by rw [← fastBase_exact]; exact bind00282_0) (by rw [← fastBase_exact]; exact bind00282_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0097 certificate0098 (by decide)

private theorem bind00283_0 : Agrees (spec (fastBase 0 3 67) layout0015) scope0100 := by decide

theorem reject00283 : Rejected (base 0 3 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 67) _ validLayout0015) (by decide) scope0100 (by rw [← fastBase_exact]; exact bind00283_0) certificate0103

private theorem bind00284_0 : Agrees (spec (fastBase 0 3 68) layout0015) scope0101 := by decide

theorem reject00284 : Rejected (base 0 3 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 68) _ validLayout0015) (by decide) scope0101 (by rw [← fastBase_exact]; exact bind00284_0) certificate0104

private theorem bind00285_0 : Agrees (spec (fastBase 0 3 69) layout0015) scope0088 := by decide

theorem reject00285 : Rejected (base 0 3 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 69) _ validLayout0015) (by decide) scope0088 (by rw [← fastBase_exact]; exact bind00285_0) certificate0091

private theorem bind00286_0 : Agrees (spec (fastBase 0 3 70) layout0016) scope0094 := by decide

private theorem bind00286_1 : Agrees (spec (fastBase 0 3 70) layout0017) scope0092 := by decide

theorem reject00286 : Rejected (base 0 3 70) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0016 layout0017 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 70) _ validLayout0016) (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 70) _ validLayout0017) (by decide) (by decide) scope0094 scope0092 (by rw [← fastBase_exact]; exact bind00286_0) (by rw [← fastBase_exact]; exact bind00286_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0097 certificate0095 (by decide)

private theorem bind00287_0 : Agrees (spec (fastBase 0 3 71) layout0015) scope0093 := by decide

theorem reject00287 : Rejected (base 0 3 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0015 (layoutValid_of_refines _ _ (base_refines_skeleton 0 3 71) _ validLayout0015) (by decide) scope0093 (by rw [← fastBase_exact]; exact bind00287_0) certificate0096

theorem allCases003 : ∀ y : Fin 72, Rejected (base 0 3 y) := by
  intro y
  fin_cases y

  · exact reject00216

  · exact reject00217

  · exact reject00218

  · exact reject00219

  · exact reject00220

  · exact reject00221

  · exact reject00222

  · exact reject00223

  · exact reject00224

  · exact reject00225

  · exact reject00226

  · exact reject00227

  · exact reject00228

  · exact reject00229

  · exact reject00230

  · exact reject00231

  · exact reject00232

  · exact reject00233

  · exact reject00234

  · exact reject00235

  · exact reject00236

  · exact reject00237

  · exact reject00238

  · exact reject00239

  · exact reject00240

  · exact reject00241

  · exact reject00242

  · exact reject00243

  · exact reject00244

  · exact reject00245

  · exact reject00246

  · exact reject00247

  · exact reject00248

  · exact reject00249

  · exact reject00250

  · exact reject00251

  · exact reject00252

  · exact reject00253

  · exact reject00254

  · exact reject00255

  · exact reject00256

  · exact reject00257

  · exact reject00258

  · exact reject00259

  · exact reject00260

  · exact reject00261

  · exact reject00262

  · exact reject00263

  · exact reject00264

  · exact reject00265

  · exact reject00266

  · exact reject00267

  · exact reject00268

  · exact reject00269

  · exact reject00270

  · exact reject00271

  · exact reject00272

  · exact reject00273

  · exact reject00274

  · exact reject00275

  · exact reject00276

  · exact reject00277

  · exact reject00278

  · exact reject00279

  · exact reject00280

  · exact reject00281

  · exact reject00282

  · exact reject00283

  · exact reject00284

  · exact reject00285

  · exact reject00286

  · exact reject00287

end PricingIntegration.RemainingGWitnesses
