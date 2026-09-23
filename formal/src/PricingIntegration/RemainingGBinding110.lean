import PricingIntegration.RemainingGLayouts018

import PricingIntegration.RemainingGLayouts034

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks026

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks035


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind07920_0 : Agrees (spec (fastBase 1 38 0) layout0147) scope0411 := by decide

theorem reject07920 : Rejected (base 1 38 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 0) _ validLayout0147) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind07920_0) certificate0431

private theorem bind07921_0 : Agrees (spec (fastBase 1 38 1) layout0148) scope0140 := by decide

theorem reject07921 : Rejected (base 1 38 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 1) _ validLayout0148) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind07921_0) certificate0143

private theorem bind07922_0 : Agrees (spec (fastBase 1 38 2) layout0148) scope0141 := by decide

theorem reject07922 : Rejected (base 1 38 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 2) _ validLayout0148) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind07922_0) certificate0144

private theorem bind07923_0 : Agrees (spec (fastBase 1 38 3) layout0147) scope0524 := by decide

theorem reject07923 : Rejected (base 1 38 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 3) _ validLayout0147) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind07923_0) certificate0566

private theorem bind07924_0 : Agrees (spec (fastBase 1 38 4) layout0147) scope0166 := by decide

theorem reject07924 : Rejected (base 1 38 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 4) _ validLayout0147) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind07924_0) certificate0169

private theorem bind07925_0 : Agrees (spec (fastBase 1 38 5) layout0147) scope0525 := by decide

theorem reject07925 : Rejected (base 1 38 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 5) _ validLayout0147) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind07925_0) certificate0567

private theorem bind07926_0 : Agrees (spec (fastBase 1 38 6) layout0150) scope0148 := by decide

private theorem bind07926_1 : Agrees (spec (fastBase 1 38 6) layout0278) scope0147 := by decide

theorem reject07926 : Rejected (base 1 38 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0150 layout0278 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 6) _ validLayout0150) (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 6) _ validLayout0278) (by decide) (by decide) scope0148 scope0147 (by rw [← fastBase_exact]; exact bind07926_0) (by rw [← fastBase_exact]; exact bind07926_1) 2 7 7 2 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0150 (by decide)

private theorem bind07927_0 : Agrees (spec (fastBase 1 38 7) layout0148) scope0148 := by decide

private theorem bind07927_1 : Agrees (spec (fastBase 1 38 7) layout0278) scope0149 := by decide

theorem reject07927 : Rejected (base 1 38 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0148 layout0278 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 7) _ validLayout0148) (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 7) _ validLayout0278) (by decide) (by decide) scope0148 scope0149 (by rw [← fastBase_exact]; exact bind07927_0) (by rw [← fastBase_exact]; exact bind07927_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0152 (by decide)

private theorem bind07928_0 : Agrees (spec (fastBase 1 38 8) layout0148) scope0150 := by decide

theorem reject07928 : Rejected (base 1 38 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 8) _ validLayout0148) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind07928_0) certificate0153

private theorem bind07929_0 : Agrees (spec (fastBase 1 38 9) layout0147) scope0406 := by decide

theorem reject07929 : Rejected (base 1 38 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 9) _ validLayout0147) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind07929_0) certificate0423

private theorem bind07930_0 : Agrees (spec (fastBase 1 38 10) layout0147) scope0170 := by decide

theorem reject07930 : Rejected (base 1 38 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 10) _ validLayout0147) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind07930_0) certificate0173

private theorem bind07931_0 : Agrees (spec (fastBase 1 38 11) layout0148) scope0155 := by decide

theorem reject07931 : Rejected (base 1 38 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 11) _ validLayout0148) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind07931_0) certificate0158

private theorem bind07932_0 : Agrees (spec (fastBase 1 38 12) layout0147) scope0408 := by decide

theorem reject07932 : Rejected (base 1 38 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 12) _ validLayout0147) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind07932_0) certificate0428

private theorem bind07933_0 : Agrees (spec (fastBase 1 38 13) layout0148) scope0141 := by decide

theorem reject07933 : Rejected (base 1 38 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 13) _ validLayout0148) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind07933_0) certificate0144

private theorem bind07934_0 : Agrees (spec (fastBase 1 38 14) layout0147) scope0411 := by decide

theorem reject07934 : Rejected (base 1 38 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 14) _ validLayout0147) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind07934_0) certificate0431

private theorem bind07935_0 : Agrees (spec (fastBase 1 38 15) layout0147) scope0528 := by decide

theorem reject07935 : Rejected (base 1 38 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 15) _ validLayout0147) (by decide) scope0528 (by rw [← fastBase_exact]; exact bind07935_0) certificate0570

private theorem bind07936_0 : Agrees (spec (fastBase 1 38 16) layout0148) scope0163 := by decide

theorem reject07936 : Rejected (base 1 38 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 16) _ validLayout0148) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind07936_0) certificate0166

private theorem bind07937_0 : Agrees (spec (fastBase 1 38 17) layout0147) scope0529 := by decide

theorem reject07937 : Rejected (base 1 38 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 17) _ validLayout0147) (by decide) scope0529 (by rw [← fastBase_exact]; exact bind07937_0) certificate0571

private theorem bind07938_0 : Agrees (spec (fastBase 1 38 18) layout0147) scope0524 := by decide

theorem reject07938 : Rejected (base 1 38 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 18) _ validLayout0147) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind07938_0) certificate0566

private theorem bind07939_0 : Agrees (spec (fastBase 1 38 19) layout0147) scope0166 := by decide

theorem reject07939 : Rejected (base 1 38 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 19) _ validLayout0147) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind07939_0) certificate0169

private theorem bind07940_0 : Agrees (spec (fastBase 1 38 20) layout0148) scope0160 := by decide

theorem reject07940 : Rejected (base 1 38 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 20) _ validLayout0148) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind07940_0) certificate0163

private theorem bind07941_0 : Agrees (spec (fastBase 1 38 21) layout0147) scope0416 := by decide

theorem reject07941 : Rejected (base 1 38 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 21) _ validLayout0147) (by decide) scope0416 (by rw [← fastBase_exact]; exact bind07941_0) certificate0439

private theorem bind07942_0 : Agrees (spec (fastBase 1 38 22) layout0147) scope0411 := by decide

theorem reject07942 : Rejected (base 1 38 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 22) _ validLayout0147) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind07942_0) certificate0431

private theorem bind07943_0 : Agrees (spec (fastBase 1 38 23) layout0147) scope0166 := by decide

theorem reject07943 : Rejected (base 1 38 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 23) _ validLayout0147) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind07943_0) certificate0169

private theorem bind07944_0 : Agrees (spec (fastBase 1 38 24) layout0147) scope0529 := by decide

theorem reject07944 : Rejected (base 1 38 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 24) _ validLayout0147) (by decide) scope0529 (by rw [← fastBase_exact]; exact bind07944_0) certificate0571

private theorem bind07945_0 : Agrees (spec (fastBase 1 38 25) layout0148) scope0163 := by decide

theorem reject07945 : Rejected (base 1 38 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 25) _ validLayout0148) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind07945_0) certificate0166

private theorem bind07946_0 : Agrees (spec (fastBase 1 38 26) layout0147) scope0530 := by decide

theorem reject07946 : Rejected (base 1 38 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 26) _ validLayout0147) (by decide) scope0530 (by rw [← fastBase_exact]; exact bind07946_0) certificate0572

private theorem bind07947_0 : Agrees (spec (fastBase 1 38 27) layout0148) scope0140 := by decide

theorem reject07947 : Rejected (base 1 38 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 27) _ validLayout0148) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind07947_0) certificate0143

private theorem bind07948_0 : Agrees (spec (fastBase 1 38 28) layout0147) scope0531 := by decide

theorem reject07948 : Rejected (base 1 38 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 28) _ validLayout0147) (by decide) scope0531 (by rw [← fastBase_exact]; exact bind07948_0) certificate0573

private theorem bind07949_0 : Agrees (spec (fastBase 1 38 29) layout0147) scope0524 := by decide

theorem reject07949 : Rejected (base 1 38 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 29) _ validLayout0147) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind07949_0) certificate0566

private theorem bind07950_0 : Agrees (spec (fastBase 1 38 30) layout0147) scope0410 := by decide

theorem reject07950 : Rejected (base 1 38 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 30) _ validLayout0147) (by decide) scope0410 (by rw [← fastBase_exact]; exact bind07950_0) certificate0430

private theorem bind07951_0 : Agrees (spec (fastBase 1 38 31) layout0148) scope0160 := by decide

theorem reject07951 : Rejected (base 1 38 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 31) _ validLayout0148) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind07951_0) certificate0163

private theorem bind07952_0 : Agrees (spec (fastBase 1 38 32) layout0148) scope0140 := by decide

theorem reject07952 : Rejected (base 1 38 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 32) _ validLayout0148) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind07952_0) certificate0143

private theorem bind07953_0 : Agrees (spec (fastBase 1 38 33) layout0148) scope0144 := by decide

theorem reject07953 : Rejected (base 1 38 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 33) _ validLayout0148) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind07953_0) certificate0147

private theorem bind07954_0 : Agrees (spec (fastBase 1 38 34) layout0147) scope0166 := by decide

theorem reject07954 : Rejected (base 1 38 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 34) _ validLayout0147) (by decide) scope0166 (by rw [← fastBase_exact]; exact bind07954_0) certificate0169

private theorem bind07955_0 : Agrees (spec (fastBase 1 38 35) layout0147) scope0408 := by decide

theorem reject07955 : Rejected (base 1 38 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 35) _ validLayout0147) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind07955_0) certificate0428

private theorem bind07956_0 : Agrees (spec (fastBase 1 38 36) layout0147) scope0531 := by decide

theorem reject07956 : Rejected (base 1 38 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 36) _ validLayout0147) (by decide) scope0531 (by rw [← fastBase_exact]; exact bind07956_0) certificate0573

private theorem bind07957_0 : Agrees (spec (fastBase 1 38 37) layout0147) scope0525 := by decide

theorem reject07957 : Rejected (base 1 38 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 37) _ validLayout0147) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind07957_0) certificate0567

private theorem bind07958_0 : Agrees (spec (fastBase 1 38 38) layout0147) scope0525 := by decide

theorem reject07958 : Rejected (base 1 38 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 38) _ validLayout0147) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind07958_0) certificate0567

private theorem bind07959_0 : Agrees (spec (fastBase 1 38 39) layout0147) scope0525 := by decide

theorem reject07959 : Rejected (base 1 38 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 39) _ validLayout0147) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind07959_0) certificate0567

private theorem bind07960_0 : Agrees (spec (fastBase 1 38 40) layout0147) scope0525 := by decide

theorem reject07960 : Rejected (base 1 38 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 40) _ validLayout0147) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind07960_0) certificate0567

private theorem bind07961_0 : Agrees (spec (fastBase 1 38 41) layout0147) scope0525 := by decide

theorem reject07961 : Rejected (base 1 38 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 41) _ validLayout0147) (by decide) scope0525 (by rw [← fastBase_exact]; exact bind07961_0) certificate0567

private theorem bind07962_0 : Agrees (spec (fastBase 1 38 42) layout0148) scope0167 := by decide

theorem reject07962 : Rejected (base 1 38 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 42) _ validLayout0148) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind07962_0) certificate0170

private theorem bind07963_0 : Agrees (spec (fastBase 1 38 43) layout0148) scope0168 := by decide

theorem reject07963 : Rejected (base 1 38 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 43) _ validLayout0148) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind07963_0) certificate0171

private theorem bind07964_0 : Agrees (spec (fastBase 1 38 44) layout0148) scope0150 := by decide

theorem reject07964 : Rejected (base 1 38 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 44) _ validLayout0148) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind07964_0) certificate0153

private theorem bind07965_0 : Agrees (spec (fastBase 1 38 45) layout0148) scope0148 := by decide

private theorem bind07965_1 : Agrees (spec (fastBase 1 38 45) layout0278) scope0149 := by decide

theorem reject07965 : Rejected (base 1 38 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0148 layout0278 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 45) _ validLayout0148) (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 45) _ validLayout0278) (by decide) (by decide) scope0148 scope0149 (by rw [← fastBase_exact]; exact bind07965_0) (by rw [← fastBase_exact]; exact bind07965_1) 2 7 5 0 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0152 (by decide)

private theorem bind07966_0 : Agrees (spec (fastBase 1 38 46) layout0151) scope0406 := by decide

theorem reject07966 : Rejected (base 1 38 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0151 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 46) _ validLayout0151) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind07966_0) certificate0423

private theorem bind07967_0 : Agrees (spec (fastBase 1 38 47) layout0147) scope0413 := by decide

theorem reject07967 : Rejected (base 1 38 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 47) _ validLayout0147) (by decide) scope0413 (by rw [← fastBase_exact]; exact bind07967_0) certificate0435

private theorem bind07968_0 : Agrees (spec (fastBase 1 38 48) layout0147) scope0417 := by decide

theorem reject07968 : Rejected (base 1 38 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 48) _ validLayout0147) (by decide) scope0417 (by rw [← fastBase_exact]; exact bind07968_0) certificate0440

private theorem bind07969_0 : Agrees (spec (fastBase 1 38 49) layout0150) scope0405 := by decide

private theorem bind07969_1 : Agrees (spec (fastBase 1 38 49) layout0278) scope0147 := by decide

theorem reject07969 : Rejected (base 1 38 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0150 layout0278 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 49) _ validLayout0150) (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 49) _ validLayout0278) (by decide) (by decide) scope0405 scope0147 (by rw [← fastBase_exact]; exact bind07969_0) (by rw [← fastBase_exact]; exact bind07969_1) 2 7 7 2 (by decide) (by decide) 2 3 (by decide) certificate0420 certificate0150 (by decide)

private theorem bind07970_0 : Agrees (spec (fastBase 1 38 50) layout0147) scope0406 := by decide

theorem reject07970 : Rejected (base 1 38 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 50) _ validLayout0147) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind07970_0) certificate0423

private theorem bind07971_0 : Agrees (spec (fastBase 1 38 51) layout0147) scope0170 := by decide

theorem reject07971 : Rejected (base 1 38 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 51) _ validLayout0147) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind07971_0) certificate0173

private theorem bind07972_0 : Agrees (spec (fastBase 1 38 52) layout0147) scope0411 := by decide

theorem reject07972 : Rejected (base 1 38 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 52) _ validLayout0147) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind07972_0) certificate0431

private theorem bind07973_0 : Agrees (spec (fastBase 1 38 53) layout0147) scope0530 := by decide

theorem reject07973 : Rejected (base 1 38 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 53) _ validLayout0147) (by decide) scope0530 (by rw [← fastBase_exact]; exact bind07973_0) certificate0572

private theorem bind07974_0 : Agrees (spec (fastBase 1 38 54) layout0151) scope0170 := by decide

theorem reject07974 : Rejected (base 1 38 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0151 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 54) _ validLayout0151) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind07974_0) certificate0173

private theorem bind07975_0 : Agrees (spec (fastBase 1 38 55) layout0147) scope0413 := by decide

theorem reject07975 : Rejected (base 1 38 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 55) _ validLayout0147) (by decide) scope0413 (by rw [← fastBase_exact]; exact bind07975_0) certificate0435

private theorem bind07976_0 : Agrees (spec (fastBase 1 38 56) layout0147) scope0170 := by decide

theorem reject07976 : Rejected (base 1 38 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 56) _ validLayout0147) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind07976_0) certificate0173

private theorem bind07977_0 : Agrees (spec (fastBase 1 38 57) layout0147) scope0410 := by decide

theorem reject07977 : Rejected (base 1 38 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 57) _ validLayout0147) (by decide) scope0410 (by rw [← fastBase_exact]; exact bind07977_0) certificate0430

private theorem bind07978_0 : Agrees (spec (fastBase 1 38 58) layout0147) scope0406 := by decide

theorem reject07978 : Rejected (base 1 38 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 58) _ validLayout0147) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind07978_0) certificate0423

private theorem bind07979_0 : Agrees (spec (fastBase 1 38 59) layout0147) scope0412 := by decide

theorem reject07979 : Rejected (base 1 38 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 59) _ validLayout0147) (by decide) scope0412 (by rw [← fastBase_exact]; exact bind07979_0) certificate0432

private theorem bind07980_0 : Agrees (spec (fastBase 1 38 60) layout0150) scope0155 := by decide

theorem reject07980 : Rejected (base 1 38 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 60) _ validLayout0150) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind07980_0) certificate0158

private theorem bind07981_0 : Agrees (spec (fastBase 1 38 61) layout0148) scope0155 := by decide

theorem reject07981 : Rejected (base 1 38 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 61) _ validLayout0148) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind07981_0) certificate0158

private theorem bind07982_0 : Agrees (spec (fastBase 1 38 62) layout0147) scope0528 := by decide

theorem reject07982 : Rejected (base 1 38 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 62) _ validLayout0147) (by decide) scope0528 (by rw [← fastBase_exact]; exact bind07982_0) certificate0570

private theorem bind07983_0 : Agrees (spec (fastBase 1 38 63) layout0147) scope0170 := by decide

theorem reject07983 : Rejected (base 1 38 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 63) _ validLayout0147) (by decide) scope0170 (by rw [← fastBase_exact]; exact bind07983_0) certificate0173

private theorem bind07984_0 : Agrees (spec (fastBase 1 38 64) layout0150) scope0150 := by decide

theorem reject07984 : Rejected (base 1 38 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 64) _ validLayout0150) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind07984_0) certificate0153

private theorem bind07985_0 : Agrees (spec (fastBase 1 38 65) layout0148) scope0150 := by decide

theorem reject07985 : Rejected (base 1 38 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 65) _ validLayout0148) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind07985_0) certificate0153

private theorem bind07986_0 : Agrees (spec (fastBase 1 38 66) layout0147) scope0412 := by decide

theorem reject07986 : Rejected (base 1 38 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 66) _ validLayout0147) (by decide) scope0412 (by rw [← fastBase_exact]; exact bind07986_0) certificate0432

private theorem bind07987_0 : Agrees (spec (fastBase 1 38 67) layout0147) scope0524 := by decide

theorem reject07987 : Rejected (base 1 38 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 67) _ validLayout0147) (by decide) scope0524 (by rw [← fastBase_exact]; exact bind07987_0) certificate0566

private theorem bind07988_0 : Agrees (spec (fastBase 1 38 68) layout0147) scope0416 := by decide

theorem reject07988 : Rejected (base 1 38 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 68) _ validLayout0147) (by decide) scope0416 (by rw [← fastBase_exact]; exact bind07988_0) certificate0439

private theorem bind07989_0 : Agrees (spec (fastBase 1 38 69) layout0148) scope0155 := by decide

theorem reject07989 : Rejected (base 1 38 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 69) _ validLayout0148) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind07989_0) certificate0158

private theorem bind07990_0 : Agrees (spec (fastBase 1 38 70) layout0147) scope0406 := by decide

theorem reject07990 : Rejected (base 1 38 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 70) _ validLayout0147) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind07990_0) certificate0423

private theorem bind07991_0 : Agrees (spec (fastBase 1 38 71) layout0147) scope0417 := by decide

theorem reject07991 : Rejected (base 1 38 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 1 38 71) _ validLayout0147) (by decide) scope0417 (by rw [← fastBase_exact]; exact bind07991_0) certificate0440

theorem allCases110 : ∀ y : Fin 72, Rejected (base 1 38 y) := by
  intro y
  fin_cases y

  · exact reject07920

  · exact reject07921

  · exact reject07922

  · exact reject07923

  · exact reject07924

  · exact reject07925

  · exact reject07926

  · exact reject07927

  · exact reject07928

  · exact reject07929

  · exact reject07930

  · exact reject07931

  · exact reject07932

  · exact reject07933

  · exact reject07934

  · exact reject07935

  · exact reject07936

  · exact reject07937

  · exact reject07938

  · exact reject07939

  · exact reject07940

  · exact reject07941

  · exact reject07942

  · exact reject07943

  · exact reject07944

  · exact reject07945

  · exact reject07946

  · exact reject07947

  · exact reject07948

  · exact reject07949

  · exact reject07950

  · exact reject07951

  · exact reject07952

  · exact reject07953

  · exact reject07954

  · exact reject07955

  · exact reject07956

  · exact reject07957

  · exact reject07958

  · exact reject07959

  · exact reject07960

  · exact reject07961

  · exact reject07962

  · exact reject07963

  · exact reject07964

  · exact reject07965

  · exact reject07966

  · exact reject07967

  · exact reject07968

  · exact reject07969

  · exact reject07970

  · exact reject07971

  · exact reject07972

  · exact reject07973

  · exact reject07974

  · exact reject07975

  · exact reject07976

  · exact reject07977

  · exact reject07978

  · exact reject07979

  · exact reject07980

  · exact reject07981

  · exact reject07982

  · exact reject07983

  · exact reject07984

  · exact reject07985

  · exact reject07986

  · exact reject07987

  · exact reject07988

  · exact reject07989

  · exact reject07990

  · exact reject07991

end PricingIntegration.RemainingGWitnesses
