import PricingIntegration.RemainingGLayouts014

import PricingIntegration.RemainingGLayouts015

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks005

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks024

import PricingIntegration.RemainingGScopeChecks025


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02088_0 : Agrees (spec (fastBase 0 29 0) layout0118) scope0144 := by decide

theorem reject02088 : Rejected (base 0 29 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 0) _ validLayout0118) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02088_0) certificate0147

private theorem bind02089_0 : Agrees (spec (fastBase 0 29 1) layout0118) scope0141 := by decide

theorem reject02089 : Rejected (base 0 29 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 1) _ validLayout0118) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02089_0) certificate0144

private theorem bind02090_0 : Agrees (spec (fastBase 0 29 2) layout0118) scope0150 := by decide

theorem reject02090 : Rejected (base 0 29 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 2) _ validLayout0118) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02090_0) certificate0153

private theorem bind02091_0 : Agrees (spec (fastBase 0 29 3) layout0119) scope0385 := by decide

theorem reject02091 : Rejected (base 0 29 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 3) _ validLayout0119) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind02091_0) certificate0395

private theorem bind02092_0 : Agrees (spec (fastBase 0 29 4) layout0119) scope0386 := by decide

theorem reject02092 : Rejected (base 0 29 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 4) _ validLayout0119) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind02092_0) certificate0396

private theorem bind02093_0 : Agrees (spec (fastBase 0 29 5) layout0118) scope0155 := by decide

theorem reject02093 : Rejected (base 0 29 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 5) _ validLayout0118) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02093_0) certificate0158

private theorem bind02094_0 : Agrees (spec (fastBase 0 29 6) layout0119) scope0387 := by decide

theorem reject02094 : Rejected (base 0 29 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 6) _ validLayout0119) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind02094_0) certificate0397

private theorem bind02095_0 : Agrees (spec (fastBase 0 29 7) layout0118) scope0145 := by decide

theorem reject02095 : Rejected (base 0 29 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 7) _ validLayout0118) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02095_0) certificate0148

private theorem bind02096_0 : Agrees (spec (fastBase 0 29 8) layout0118) scope0140 := by decide

theorem reject02096 : Rejected (base 0 29 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 8) _ validLayout0118) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02096_0) certificate0143

private theorem bind02097_0 : Agrees (spec (fastBase 0 29 9) layout0120) scope0164 := by decide

private theorem bind02097_1 : Agrees (spec (fastBase 0 29 9) layout0121) scope0092 := by decide

theorem reject02097 : Rejected (base 0 29 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 9) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 9) _ validLayout0121) (by decide) (by decide) scope0164 scope0092 (by rw [← fastBase_exact]; exact bind02097_0) (by rw [← fastBase_exact]; exact bind02097_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0398 certificate0095 (by decide)

private theorem bind02098_0 : Agrees (spec (fastBase 0 29 10) layout0119) scope0106 := by decide

theorem reject02098 : Rejected (base 0 29 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 10) _ validLayout0119) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind02098_0) certificate0109

private theorem bind02099_0 : Agrees (spec (fastBase 0 29 11) layout0120) scope0148 := by decide

private theorem bind02099_1 : Agrees (spec (fastBase 0 29 11) layout0121) scope0095 := by decide

theorem reject02099 : Rejected (base 0 29 11) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 11) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 11) _ validLayout0121) (by decide) (by decide) scope0148 scope0095 (by rw [← fastBase_exact]; exact bind02099_0) (by rw [← fastBase_exact]; exact bind02099_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0399 certificate0098 (by decide)

private theorem bind02100_0 : Agrees (spec (fastBase 0 29 12) layout0118) scope0144 := by decide

theorem reject02100 : Rejected (base 0 29 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 12) _ validLayout0118) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02100_0) certificate0147

private theorem bind02101_0 : Agrees (spec (fastBase 0 29 13) layout0118) scope0144 := by decide

theorem reject02101 : Rejected (base 0 29 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 13) _ validLayout0118) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02101_0) certificate0147

private theorem bind02102_0 : Agrees (spec (fastBase 0 29 14) layout0118) scope0144 := by decide

theorem reject02102 : Rejected (base 0 29 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 14) _ validLayout0118) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02102_0) certificate0147

private theorem bind02103_0 : Agrees (spec (fastBase 0 29 15) layout0118) scope0144 := by decide

theorem reject02103 : Rejected (base 0 29 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 15) _ validLayout0118) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02103_0) certificate0147

private theorem bind02104_0 : Agrees (spec (fastBase 0 29 16) layout0118) scope0144 := by decide

theorem reject02104 : Rejected (base 0 29 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 16) _ validLayout0118) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind02104_0) certificate0147

private theorem bind02105_0 : Agrees (spec (fastBase 0 29 17) layout0118) scope0141 := by decide

theorem reject02105 : Rejected (base 0 29 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 17) _ validLayout0118) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02105_0) certificate0144

private theorem bind02106_0 : Agrees (spec (fastBase 0 29 18) layout0120) scope0141 := by decide

theorem reject02106 : Rejected (base 0 29 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0120 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 18) _ validLayout0120) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02106_0) certificate0144

private theorem bind02107_0 : Agrees (spec (fastBase 0 29 19) layout0118) scope0163 := by decide

theorem reject02107 : Rejected (base 0 29 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 19) _ validLayout0118) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind02107_0) certificate0166

private theorem bind02108_0 : Agrees (spec (fastBase 0 29 20) layout0119) scope0387 := by decide

theorem reject02108 : Rejected (base 0 29 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 20) _ validLayout0119) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind02108_0) certificate0397

private theorem bind02109_0 : Agrees (spec (fastBase 0 29 21) layout0118) scope0162 := by decide

theorem reject02109 : Rejected (base 0 29 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 21) _ validLayout0118) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind02109_0) certificate0165

private theorem bind02110_0 : Agrees (spec (fastBase 0 29 22) layout0118) scope0150 := by decide

theorem reject02110 : Rejected (base 0 29 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 22) _ validLayout0118) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02110_0) certificate0153

private theorem bind02111_0 : Agrees (spec (fastBase 0 29 23) layout0119) scope0388 := by decide

theorem reject02111 : Rejected (base 0 29 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 23) _ validLayout0119) (by decide) scope0388 (by rw [← fastBase_exact]; exact bind02111_0) certificate0400

private theorem bind02112_0 : Agrees (spec (fastBase 0 29 24) layout0119) scope0385 := by decide

theorem reject02112 : Rejected (base 0 29 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 24) _ validLayout0119) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind02112_0) certificate0395

private theorem bind02113_0 : Agrees (spec (fastBase 0 29 25) layout0118) scope0163 := by decide

theorem reject02113 : Rejected (base 0 29 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 25) _ validLayout0118) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind02113_0) certificate0166

private theorem bind02114_0 : Agrees (spec (fastBase 0 29 26) layout0118) scope0171 := by decide

theorem reject02114 : Rejected (base 0 29 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 26) _ validLayout0118) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind02114_0) certificate0174

private theorem bind02115_0 : Agrees (spec (fastBase 0 29 27) layout0118) scope0141 := by decide

theorem reject02115 : Rejected (base 0 29 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 27) _ validLayout0118) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02115_0) certificate0144

private theorem bind02116_0 : Agrees (spec (fastBase 0 29 28) layout0118) scope0150 := by decide

theorem reject02116 : Rejected (base 0 29 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 28) _ validLayout0118) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02116_0) certificate0153

private theorem bind02117_0 : Agrees (spec (fastBase 0 29 29) layout0118) scope0168 := by decide

theorem reject02117 : Rejected (base 0 29 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 29) _ validLayout0118) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind02117_0) certificate0171

private theorem bind02118_0 : Agrees (spec (fastBase 0 29 30) layout0118) scope0157 := by decide

theorem reject02118 : Rejected (base 0 29 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 30) _ validLayout0118) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind02118_0) certificate0160

private theorem bind02119_0 : Agrees (spec (fastBase 0 29 31) layout0119) scope0385 := by decide

theorem reject02119 : Rejected (base 0 29 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 31) _ validLayout0119) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind02119_0) certificate0395

private theorem bind02120_0 : Agrees (spec (fastBase 0 29 32) layout0118) scope0168 := by decide

theorem reject02120 : Rejected (base 0 29 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 32) _ validLayout0118) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind02120_0) certificate0171

private theorem bind02121_0 : Agrees (spec (fastBase 0 29 33) layout0118) scope0150 := by decide

theorem reject02121 : Rejected (base 0 29 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 33) _ validLayout0118) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02121_0) certificate0153

private theorem bind02122_0 : Agrees (spec (fastBase 0 29 34) layout0118) scope0155 := by decide

theorem reject02122 : Rejected (base 0 29 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 34) _ validLayout0118) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02122_0) certificate0158

private theorem bind02123_0 : Agrees (spec (fastBase 0 29 35) layout0118) scope0167 := by decide

theorem reject02123 : Rejected (base 0 29 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 35) _ validLayout0118) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind02123_0) certificate0170

private theorem bind02124_0 : Agrees (spec (fastBase 0 29 36) layout0122) scope0386 := by decide

theorem reject02124 : Rejected (base 0 29 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0122 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 36) _ validLayout0122) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind02124_0) certificate0396

private theorem bind02125_0 : Agrees (spec (fastBase 0 29 37) layout0118) scope0155 := by decide

theorem reject02125 : Rejected (base 0 29 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 37) _ validLayout0118) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02125_0) certificate0158

private theorem bind02126_0 : Agrees (spec (fastBase 0 29 38) layout0120) scope0155 := by decide

theorem reject02126 : Rejected (base 0 29 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0120 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 38) _ validLayout0120) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02126_0) certificate0158

private theorem bind02127_0 : Agrees (spec (fastBase 0 29 39) layout0118) scope0171 := by decide

theorem reject02127 : Rejected (base 0 29 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 39) _ validLayout0118) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind02127_0) certificate0174

private theorem bind02128_0 : Agrees (spec (fastBase 0 29 40) layout0118) scope0160 := by decide

theorem reject02128 : Rejected (base 0 29 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 40) _ validLayout0118) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind02128_0) certificate0163

private theorem bind02129_0 : Agrees (spec (fastBase 0 29 41) layout0119) scope0106 := by decide

theorem reject02129 : Rejected (base 0 29 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 41) _ validLayout0119) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind02129_0) certificate0109

private theorem bind02130_0 : Agrees (spec (fastBase 0 29 42) layout0118) scope0141 := by decide

theorem reject02130 : Rejected (base 0 29 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 42) _ validLayout0118) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind02130_0) certificate0144

private theorem bind02131_0 : Agrees (spec (fastBase 0 29 43) layout0118) scope0157 := by decide

theorem reject02131 : Rejected (base 0 29 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 43) _ validLayout0118) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind02131_0) certificate0160

private theorem bind02132_0 : Agrees (spec (fastBase 0 29 44) layout0118) scope0156 := by decide

theorem reject02132 : Rejected (base 0 29 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 44) _ validLayout0118) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind02132_0) certificate0159

private theorem bind02133_0 : Agrees (spec (fastBase 0 29 45) layout0118) scope0145 := by decide

theorem reject02133 : Rejected (base 0 29 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 45) _ validLayout0118) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02133_0) certificate0148

private theorem bind02134_0 : Agrees (spec (fastBase 0 29 46) layout0119) scope0387 := by decide

theorem reject02134 : Rejected (base 0 29 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 46) _ validLayout0119) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind02134_0) certificate0397

private theorem bind02135_0 : Agrees (spec (fastBase 0 29 47) layout0118) scope0145 := by decide

theorem reject02135 : Rejected (base 0 29 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 47) _ validLayout0118) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02135_0) certificate0148

private theorem bind02136_0 : Agrees (spec (fastBase 0 29 48) layout0118) scope0162 := by decide

theorem reject02136 : Rejected (base 0 29 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 48) _ validLayout0118) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind02136_0) certificate0165

private theorem bind02137_0 : Agrees (spec (fastBase 0 29 49) layout0120) scope0145 := by decide

theorem reject02137 : Rejected (base 0 29 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0120 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 49) _ validLayout0120) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02137_0) certificate0148

private theorem bind02138_0 : Agrees (spec (fastBase 0 29 50) layout0119) scope0105 := by decide

theorem reject02138 : Rejected (base 0 29 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 50) _ validLayout0119) (by decide) scope0105 (by rw [← fastBase_exact]; exact bind02138_0) certificate0108

private theorem bind02139_0 : Agrees (spec (fastBase 0 29 51) layout0118) scope0158 := by decide

theorem reject02139 : Rejected (base 0 29 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 51) _ validLayout0118) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02139_0) certificate0161

private theorem bind02140_0 : Agrees (spec (fastBase 0 29 52) layout0118) scope0140 := by decide

theorem reject02140 : Rejected (base 0 29 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 52) _ validLayout0118) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02140_0) certificate0143

private theorem bind02141_0 : Agrees (spec (fastBase 0 29 53) layout0118) scope0160 := by decide

theorem reject02141 : Rejected (base 0 29 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 53) _ validLayout0118) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind02141_0) certificate0163

private theorem bind02142_0 : Agrees (spec (fastBase 0 29 54) layout0118) scope0158 := by decide

theorem reject02142 : Rejected (base 0 29 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 54) _ validLayout0118) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02142_0) certificate0161

private theorem bind02143_0 : Agrees (spec (fastBase 0 29 55) layout0120) scope0164 := by decide

private theorem bind02143_1 : Agrees (spec (fastBase 0 29 55) layout0121) scope0092 := by decide

theorem reject02143 : Rejected (base 0 29 55) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 55) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 55) _ validLayout0121) (by decide) (by decide) scope0164 scope0092 (by rw [← fastBase_exact]; exact bind02143_0) (by rw [← fastBase_exact]; exact bind02143_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0398 certificate0095 (by decide)

private theorem bind02144_0 : Agrees (spec (fastBase 0 29 56) layout0120) scope0140 := by decide

theorem reject02144 : Rejected (base 0 29 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0120 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 56) _ validLayout0120) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02144_0) certificate0143

private theorem bind02145_0 : Agrees (spec (fastBase 0 29 57) layout0118) scope0156 := by decide

theorem reject02145 : Rejected (base 0 29 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 57) _ validLayout0118) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind02145_0) certificate0159

private theorem bind02146_0 : Agrees (spec (fastBase 0 29 58) layout0118) scope0165 := by decide

theorem reject02146 : Rejected (base 0 29 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 58) _ validLayout0118) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind02146_0) certificate0168

private theorem bind02147_0 : Agrees (spec (fastBase 0 29 59) layout0118) scope0140 := by decide

theorem reject02147 : Rejected (base 0 29 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 59) _ validLayout0118) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02147_0) certificate0143

private theorem bind02148_0 : Agrees (spec (fastBase 0 29 60) layout0118) scope0145 := by decide

theorem reject02148 : Rejected (base 0 29 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 60) _ validLayout0118) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02148_0) certificate0148

private theorem bind02149_0 : Agrees (spec (fastBase 0 29 61) layout0120) scope0164 := by decide

private theorem bind02149_1 : Agrees (spec (fastBase 0 29 61) layout0121) scope0095 := by decide

theorem reject02149 : Rejected (base 0 29 61) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 61) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 61) _ validLayout0121) (by decide) (by decide) scope0164 scope0095 (by rw [← fastBase_exact]; exact bind02149_0) (by rw [← fastBase_exact]; exact bind02149_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0398 certificate0098 (by decide)

private theorem bind02150_0 : Agrees (spec (fastBase 0 29 62) layout0118) scope0167 := by decide

theorem reject02150 : Rejected (base 0 29 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 62) _ validLayout0118) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind02150_0) certificate0170

private theorem bind02151_0 : Agrees (spec (fastBase 0 29 63) layout0118) scope0155 := by decide

theorem reject02151 : Rejected (base 0 29 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 63) _ validLayout0118) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind02151_0) certificate0158

private theorem bind02152_0 : Agrees (spec (fastBase 0 29 64) layout0118) scope0165 := by decide

theorem reject02152 : Rejected (base 0 29 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 64) _ validLayout0118) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind02152_0) certificate0168

private theorem bind02153_0 : Agrees (spec (fastBase 0 29 65) layout0118) scope0140 := by decide

theorem reject02153 : Rejected (base 0 29 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0118 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 65) _ validLayout0118) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02153_0) certificate0143

private theorem bind02154_0 : Agrees (spec (fastBase 0 29 66) layout0120) scope0151 := by decide

private theorem bind02154_1 : Agrees (spec (fastBase 0 29 66) layout0121) scope0095 := by decide

theorem reject02154 : Rejected (base 0 29 66) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 66) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 66) _ validLayout0121) (by decide) (by decide) scope0151 scope0095 (by rw [← fastBase_exact]; exact bind02154_0) (by rw [← fastBase_exact]; exact bind02154_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0401 certificate0098 (by decide)

private theorem bind02155_0 : Agrees (spec (fastBase 0 29 67) layout0122) scope0385 := by decide

theorem reject02155 : Rejected (base 0 29 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0122 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 67) _ validLayout0122) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind02155_0) certificate0395

private theorem bind02156_0 : Agrees (spec (fastBase 0 29 68) layout0119) scope0386 := by decide

theorem reject02156 : Rejected (base 0 29 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 68) _ validLayout0119) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind02156_0) certificate0396

private theorem bind02157_0 : Agrees (spec (fastBase 0 29 69) layout0120) scope0148 := by decide

private theorem bind02157_1 : Agrees (spec (fastBase 0 29 69) layout0121) scope0095 := by decide

theorem reject02157 : Rejected (base 0 29 69) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 69) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 69) _ validLayout0121) (by decide) (by decide) scope0148 scope0095 (by rw [← fastBase_exact]; exact bind02157_0) (by rw [← fastBase_exact]; exact bind02157_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0399 certificate0098 (by decide)

private theorem bind02158_0 : Agrees (spec (fastBase 0 29 70) layout0120) scope0148 := by decide

private theorem bind02158_1 : Agrees (spec (fastBase 0 29 70) layout0121) scope0092 := by decide

theorem reject02158 : Rejected (base 0 29 70) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0120 layout0121 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 70) _ validLayout0120) (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 70) _ validLayout0121) (by decide) (by decide) scope0148 scope0092 (by rw [← fastBase_exact]; exact bind02158_0) (by rw [← fastBase_exact]; exact bind02158_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0399 certificate0095 (by decide)

private theorem bind02159_0 : Agrees (spec (fastBase 0 29 71) layout0119) scope0106 := by decide

theorem reject02159 : Rejected (base 0 29 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0119 (layoutValid_of_refines _ _ (base_refines_skeleton 0 29 71) _ validLayout0119) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind02159_0) certificate0109

theorem allCases029 : ∀ y : Fin 72, Rejected (base 0 29 y) := by
  intro y
  fin_cases y

  · exact reject02088

  · exact reject02089

  · exact reject02090

  · exact reject02091

  · exact reject02092

  · exact reject02093

  · exact reject02094

  · exact reject02095

  · exact reject02096

  · exact reject02097

  · exact reject02098

  · exact reject02099

  · exact reject02100

  · exact reject02101

  · exact reject02102

  · exact reject02103

  · exact reject02104

  · exact reject02105

  · exact reject02106

  · exact reject02107

  · exact reject02108

  · exact reject02109

  · exact reject02110

  · exact reject02111

  · exact reject02112

  · exact reject02113

  · exact reject02114

  · exact reject02115

  · exact reject02116

  · exact reject02117

  · exact reject02118

  · exact reject02119

  · exact reject02120

  · exact reject02121

  · exact reject02122

  · exact reject02123

  · exact reject02124

  · exact reject02125

  · exact reject02126

  · exact reject02127

  · exact reject02128

  · exact reject02129

  · exact reject02130

  · exact reject02131

  · exact reject02132

  · exact reject02133

  · exact reject02134

  · exact reject02135

  · exact reject02136

  · exact reject02137

  · exact reject02138

  · exact reject02139

  · exact reject02140

  · exact reject02141

  · exact reject02142

  · exact reject02143

  · exact reject02144

  · exact reject02145

  · exact reject02146

  · exact reject02147

  · exact reject02148

  · exact reject02149

  · exact reject02150

  · exact reject02151

  · exact reject02152

  · exact reject02153

  · exact reject02154

  · exact reject02155

  · exact reject02156

  · exact reject02157

  · exact reject02158

  · exact reject02159

end PricingIntegration.RemainingGWitnesses
