import PricingIntegration.RemainingGLayouts006

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks019

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks030

import PricingIntegration.RemainingGScopeChecks031

import PricingIntegration.RemainingGScopeChecks038


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05904_0 : Agrees (spec (fastBase 1 10 0) layout0049) scope0569 := by decide

theorem reject05904 : Rejected (base 1 10 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 0) _ validLayout0049) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind05904_0) certificate0612

private theorem bind05905_0 : Agrees (spec (fastBase 1 10 1) layout0049) scope0449 := by decide

theorem reject05905 : Rejected (base 1 10 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 1) _ validLayout0049) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind05905_0) certificate0481

private theorem bind05906_0 : Agrees (spec (fastBase 1 10 2) layout0049) scope0447 := by decide

theorem reject05906 : Rejected (base 1 10 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 2) _ validLayout0049) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind05906_0) certificate0479

private theorem bind05907_0 : Agrees (spec (fastBase 1 10 3) layout0049) scope0454 := by decide

theorem reject05907 : Rejected (base 1 10 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 3) _ validLayout0049) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind05907_0) certificate0489

private theorem bind05908_0 : Agrees (spec (fastBase 1 10 4) layout0049) scope0570 := by decide

theorem reject05908 : Rejected (base 1 10 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 4) _ validLayout0049) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind05908_0) certificate0613

private theorem bind05909_0 : Agrees (spec (fastBase 1 10 5) layout0050) scope0299 := by decide

theorem reject05909 : Rejected (base 1 10 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 5) _ validLayout0050) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind05909_0) certificate0304

private theorem bind05910_0 : Agrees (spec (fastBase 1 10 6) layout0049) scope0448 := by decide

theorem reject05910 : Rejected (base 1 10 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 6) _ validLayout0049) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind05910_0) certificate0480

private theorem bind05911_0 : Agrees (spec (fastBase 1 10 7) layout0049) scope0450 := by decide

theorem reject05911 : Rejected (base 1 10 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 7) _ validLayout0049) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind05911_0) certificate0483

private theorem bind05912_0 : Agrees (spec (fastBase 1 10 8) layout0049) scope0451 := by decide

theorem reject05912 : Rejected (base 1 10 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 8) _ validLayout0049) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind05912_0) certificate0484

private theorem bind05913_0 : Agrees (spec (fastBase 1 10 9) layout0050) scope0304 := by decide

theorem reject05913 : Rejected (base 1 10 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 9) _ validLayout0050) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind05913_0) certificate0309

private theorem bind05914_0 : Agrees (spec (fastBase 1 10 10) layout0049) scope0259 := by decide

theorem reject05914 : Rejected (base 1 10 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 10) _ validLayout0049) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind05914_0) certificate0262

private theorem bind05915_0 : Agrees (spec (fastBase 1 10 11) layout0049) scope0264 := by decide

theorem reject05915 : Rejected (base 1 10 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 11) _ validLayout0049) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind05915_0) certificate0267

private theorem bind05916_0 : Agrees (spec (fastBase 1 10 12) layout0049) scope0446 := by decide

theorem reject05916 : Rejected (base 1 10 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 12) _ validLayout0049) (by decide) scope0446 (by rw [← fastBase_exact]; exact bind05916_0) certificate0478

private theorem bind05917_0 : Agrees (spec (fastBase 1 10 13) layout0049) scope0447 := by decide

theorem reject05917 : Rejected (base 1 10 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 13) _ validLayout0049) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind05917_0) certificate0479

private theorem bind05918_0 : Agrees (spec (fastBase 1 10 14) layout0049) scope0569 := by decide

theorem reject05918 : Rejected (base 1 10 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 14) _ validLayout0049) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind05918_0) certificate0612

private theorem bind05919_0 : Agrees (spec (fastBase 1 10 15) layout0049) scope0260 := by decide

theorem reject05919 : Rejected (base 1 10 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 15) _ validLayout0049) (by decide) scope0260 (by rw [← fastBase_exact]; exact bind05919_0) certificate0263

private theorem bind05920_0 : Agrees (spec (fastBase 1 10 16) layout0049) scope0451 := by decide

theorem reject05920 : Rejected (base 1 10 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 16) _ validLayout0049) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind05920_0) certificate0484

private theorem bind05921_0 : Agrees (spec (fastBase 1 10 17) layout0049) scope0571 := by decide

theorem reject05921 : Rejected (base 1 10 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 17) _ validLayout0049) (by decide) scope0571 (by rw [← fastBase_exact]; exact bind05921_0) certificate0614

private theorem bind05922_0 : Agrees (spec (fastBase 1 10 18) layout0049) scope0454 := by decide

theorem reject05922 : Rejected (base 1 10 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 18) _ validLayout0049) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind05922_0) certificate0489

private theorem bind05923_0 : Agrees (spec (fastBase 1 10 19) layout0049) scope0570 := by decide

theorem reject05923 : Rejected (base 1 10 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 19) _ validLayout0049) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind05923_0) certificate0613

private theorem bind05924_0 : Agrees (spec (fastBase 1 10 20) layout0049) scope0449 := by decide

theorem reject05924 : Rejected (base 1 10 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 20) _ validLayout0049) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind05924_0) certificate0481

private theorem bind05925_0 : Agrees (spec (fastBase 1 10 21) layout0050) scope0311 := by decide

theorem reject05925 : Rejected (base 1 10 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 21) _ validLayout0050) (by decide) scope0311 (by rw [← fastBase_exact]; exact bind05925_0) certificate0316

private theorem bind05926_0 : Agrees (spec (fastBase 1 10 22) layout0049) scope0569 := by decide

theorem reject05926 : Rejected (base 1 10 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 22) _ validLayout0049) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind05926_0) certificate0612

private theorem bind05927_0 : Agrees (spec (fastBase 1 10 23) layout0049) scope0570 := by decide

theorem reject05927 : Rejected (base 1 10 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 23) _ validLayout0049) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind05927_0) certificate0613

private theorem bind05928_0 : Agrees (spec (fastBase 1 10 24) layout0049) scope0571 := by decide

theorem reject05928 : Rejected (base 1 10 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 24) _ validLayout0049) (by decide) scope0571 (by rw [← fastBase_exact]; exact bind05928_0) certificate0614

private theorem bind05929_0 : Agrees (spec (fastBase 1 10 25) layout0049) scope0447 := by decide

theorem reject05929 : Rejected (base 1 10 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 25) _ validLayout0049) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind05929_0) certificate0479

private theorem bind05930_0 : Agrees (spec (fastBase 1 10 26) layout0049) scope0572 := by decide

theorem reject05930 : Rejected (base 1 10 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 26) _ validLayout0049) (by decide) scope0572 (by rw [← fastBase_exact]; exact bind05930_0) certificate0615

private theorem bind05931_0 : Agrees (spec (fastBase 1 10 27) layout0049) scope0449 := by decide

theorem reject05931 : Rejected (base 1 10 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 27) _ validLayout0049) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind05931_0) certificate0481

private theorem bind05932_0 : Agrees (spec (fastBase 1 10 28) layout0049) scope0263 := by decide

theorem reject05932 : Rejected (base 1 10 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 28) _ validLayout0049) (by decide) scope0263 (by rw [← fastBase_exact]; exact bind05932_0) certificate0266

private theorem bind05933_0 : Agrees (spec (fastBase 1 10 29) layout0049) scope0454 := by decide

theorem reject05933 : Rejected (base 1 10 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 29) _ validLayout0049) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind05933_0) certificate0489

private theorem bind05934_0 : Agrees (spec (fastBase 1 10 30) layout0049) scope0453 := by decide

theorem reject05934 : Rejected (base 1 10 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 30) _ validLayout0049) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind05934_0) certificate0488

private theorem bind05935_0 : Agrees (spec (fastBase 1 10 31) layout0049) scope0264 := by decide

theorem reject05935 : Rejected (base 1 10 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 31) _ validLayout0049) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind05935_0) certificate0267

private theorem bind05936_0 : Agrees (spec (fastBase 1 10 32) layout0049) scope0449 := by decide

theorem reject05936 : Rejected (base 1 10 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 32) _ validLayout0049) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind05936_0) certificate0481

private theorem bind05937_0 : Agrees (spec (fastBase 1 10 33) layout0049) scope0447 := by decide

theorem reject05937 : Rejected (base 1 10 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 33) _ validLayout0049) (by decide) scope0447 (by rw [← fastBase_exact]; exact bind05937_0) certificate0479

private theorem bind05938_0 : Agrees (spec (fastBase 1 10 34) layout0049) scope0570 := by decide

theorem reject05938 : Rejected (base 1 10 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 34) _ validLayout0049) (by decide) scope0570 (by rw [← fastBase_exact]; exact bind05938_0) certificate0613

private theorem bind05939_0 : Agrees (spec (fastBase 1 10 35) layout0049) scope0446 := by decide

theorem reject05939 : Rejected (base 1 10 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 35) _ validLayout0049) (by decide) scope0446 (by rw [← fastBase_exact]; exact bind05939_0) certificate0478

private theorem bind05940_0 : Agrees (spec (fastBase 1 10 36) layout0049) scope0263 := by decide

theorem reject05940 : Rejected (base 1 10 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 36) _ validLayout0049) (by decide) scope0263 (by rw [← fastBase_exact]; exact bind05940_0) certificate0266

private theorem bind05941_0 : Agrees (spec (fastBase 1 10 37) layout0050) scope0299 := by decide

theorem reject05941 : Rejected (base 1 10 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 37) _ validLayout0050) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind05941_0) certificate0304

private theorem bind05942_0 : Agrees (spec (fastBase 1 10 38) layout0050) scope0299 := by decide

theorem reject05942 : Rejected (base 1 10 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 38) _ validLayout0050) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind05942_0) certificate0304

private theorem bind05943_0 : Agrees (spec (fastBase 1 10 39) layout0050) scope0299 := by decide

theorem reject05943 : Rejected (base 1 10 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 39) _ validLayout0050) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind05943_0) certificate0304

private theorem bind05944_0 : Agrees (spec (fastBase 1 10 40) layout0050) scope0304 := by decide

theorem reject05944 : Rejected (base 1 10 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 40) _ validLayout0050) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind05944_0) certificate0309

private theorem bind05945_0 : Agrees (spec (fastBase 1 10 41) layout0050) scope0305 := by decide

theorem reject05945 : Rejected (base 1 10 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 41) _ validLayout0050) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind05945_0) certificate0310

private theorem bind05946_0 : Agrees (spec (fastBase 1 10 42) layout0049) scope0448 := by decide

theorem reject05946 : Rejected (base 1 10 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 42) _ validLayout0049) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind05946_0) certificate0480

private theorem bind05947_0 : Agrees (spec (fastBase 1 10 43) layout0049) scope0448 := by decide

theorem reject05947 : Rejected (base 1 10 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 43) _ validLayout0049) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind05947_0) certificate0480

private theorem bind05948_0 : Agrees (spec (fastBase 1 10 44) layout0049) scope0448 := by decide

theorem reject05948 : Rejected (base 1 10 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 44) _ validLayout0049) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind05948_0) certificate0480

private theorem bind05949_0 : Agrees (spec (fastBase 1 10 45) layout0049) scope0448 := by decide

theorem reject05949 : Rejected (base 1 10 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 45) _ validLayout0049) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind05949_0) certificate0480

private theorem bind05950_0 : Agrees (spec (fastBase 1 10 46) layout0049) scope0448 := by decide

theorem reject05950 : Rejected (base 1 10 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 46) _ validLayout0049) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind05950_0) certificate0480

private theorem bind05951_0 : Agrees (spec (fastBase 1 10 47) layout0050) scope0309 := by decide

theorem reject05951 : Rejected (base 1 10 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 47) _ validLayout0050) (by decide) scope0309 (by rw [← fastBase_exact]; exact bind05951_0) certificate0314

private theorem bind05952_0 : Agrees (spec (fastBase 1 10 48) layout0049) scope0573 := by decide

theorem reject05952 : Rejected (base 1 10 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 48) _ validLayout0049) (by decide) scope0573 (by rw [← fastBase_exact]; exact bind05952_0) certificate0616

private theorem bind05953_0 : Agrees (spec (fastBase 1 10 49) layout0049) scope0450 := by decide

theorem reject05953 : Rejected (base 1 10 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 49) _ validLayout0049) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind05953_0) certificate0483

private theorem bind05954_0 : Agrees (spec (fastBase 1 10 50) layout0050) scope0304 := by decide

theorem reject05954 : Rejected (base 1 10 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 50) _ validLayout0050) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind05954_0) certificate0309

private theorem bind05955_0 : Agrees (spec (fastBase 1 10 51) layout0049) scope0259 := by decide

theorem reject05955 : Rejected (base 1 10 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 51) _ validLayout0049) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind05955_0) certificate0262

private theorem bind05956_0 : Agrees (spec (fastBase 1 10 52) layout0049) scope0569 := by decide

theorem reject05956 : Rejected (base 1 10 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 52) _ validLayout0049) (by decide) scope0569 (by rw [← fastBase_exact]; exact bind05956_0) certificate0612

private theorem bind05957_0 : Agrees (spec (fastBase 1 10 53) layout0049) scope0572 := by decide

theorem reject05957 : Rejected (base 1 10 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 53) _ validLayout0049) (by decide) scope0572 (by rw [← fastBase_exact]; exact bind05957_0) certificate0615

private theorem bind05958_0 : Agrees (spec (fastBase 1 10 54) layout0049) scope0451 := by decide

theorem reject05958 : Rejected (base 1 10 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 54) _ validLayout0049) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind05958_0) certificate0484

private theorem bind05959_0 : Agrees (spec (fastBase 1 10 55) layout0050) scope0317 := by decide

theorem reject05959 : Rejected (base 1 10 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 55) _ validLayout0050) (by decide) scope0317 (by rw [← fastBase_exact]; exact bind05959_0) certificate0323

private theorem bind05960_0 : Agrees (spec (fastBase 1 10 56) layout0049) scope0259 := by decide

theorem reject05960 : Rejected (base 1 10 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 56) _ validLayout0049) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind05960_0) certificate0262

private theorem bind05961_0 : Agrees (spec (fastBase 1 10 57) layout0049) scope0453 := by decide

theorem reject05961 : Rejected (base 1 10 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 57) _ validLayout0049) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind05961_0) certificate0488

private theorem bind05962_0 : Agrees (spec (fastBase 1 10 58) layout0050) scope0299 := by decide

theorem reject05962 : Rejected (base 1 10 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 58) _ validLayout0050) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind05962_0) certificate0304

private theorem bind05963_0 : Agrees (spec (fastBase 1 10 59) layout0049) scope0456 := by decide

theorem reject05963 : Rejected (base 1 10 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 59) _ validLayout0049) (by decide) scope0456 (by rw [← fastBase_exact]; exact bind05963_0) certificate0491

private theorem bind05964_0 : Agrees (spec (fastBase 1 10 60) layout0049) scope0450 := by decide

theorem reject05964 : Rejected (base 1 10 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 60) _ validLayout0049) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind05964_0) certificate0483

private theorem bind05965_0 : Agrees (spec (fastBase 1 10 61) layout0049) scope0264 := by decide

theorem reject05965 : Rejected (base 1 10 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 61) _ validLayout0049) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind05965_0) certificate0267

private theorem bind05966_0 : Agrees (spec (fastBase 1 10 62) layout0049) scope0260 := by decide

theorem reject05966 : Rejected (base 1 10 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 62) _ validLayout0049) (by decide) scope0260 (by rw [← fastBase_exact]; exact bind05966_0) certificate0263

private theorem bind05967_0 : Agrees (spec (fastBase 1 10 63) layout0049) scope0259 := by decide

theorem reject05967 : Rejected (base 1 10 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 63) _ validLayout0049) (by decide) scope0259 (by rw [← fastBase_exact]; exact bind05967_0) certificate0262

private theorem bind05968_0 : Agrees (spec (fastBase 1 10 64) layout0049) scope0450 := by decide

theorem reject05968 : Rejected (base 1 10 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 64) _ validLayout0049) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind05968_0) certificate0483

private theorem bind05969_0 : Agrees (spec (fastBase 1 10 65) layout0049) scope0451 := by decide

theorem reject05969 : Rejected (base 1 10 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 65) _ validLayout0049) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind05969_0) certificate0484

private theorem bind05970_0 : Agrees (spec (fastBase 1 10 66) layout0049) scope0456 := by decide

theorem reject05970 : Rejected (base 1 10 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 66) _ validLayout0049) (by decide) scope0456 (by rw [← fastBase_exact]; exact bind05970_0) certificate0491

private theorem bind05971_0 : Agrees (spec (fastBase 1 10 67) layout0049) scope0454 := by decide

theorem reject05971 : Rejected (base 1 10 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 67) _ validLayout0049) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind05971_0) certificate0489

private theorem bind05972_0 : Agrees (spec (fastBase 1 10 68) layout0051) scope0466 := by decide

theorem reject05972 : Rejected (base 1 10 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 68) _ validLayout0051) (by decide) scope0466 (by rw [← fastBase_exact]; exact bind05972_0) certificate0502

private theorem bind05973_0 : Agrees (spec (fastBase 1 10 69) layout0049) scope0264 := by decide

theorem reject05973 : Rejected (base 1 10 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 69) _ validLayout0049) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind05973_0) certificate0267

private theorem bind05974_0 : Agrees (spec (fastBase 1 10 70) layout0051) scope0415 := by decide

theorem reject05974 : Rejected (base 1 10 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 70) _ validLayout0051) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind05974_0) certificate0438

private theorem bind05975_0 : Agrees (spec (fastBase 1 10 71) layout0049) scope0573 := by decide

theorem reject05975 : Rejected (base 1 10 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 1 10 71) _ validLayout0049) (by decide) scope0573 (by rw [← fastBase_exact]; exact bind05975_0) certificate0616

theorem allCases082 : ∀ y : Fin 72, Rejected (base 1 10 y) := by
  intro y
  fin_cases y

  · exact reject05904

  · exact reject05905

  · exact reject05906

  · exact reject05907

  · exact reject05908

  · exact reject05909

  · exact reject05910

  · exact reject05911

  · exact reject05912

  · exact reject05913

  · exact reject05914

  · exact reject05915

  · exact reject05916

  · exact reject05917

  · exact reject05918

  · exact reject05919

  · exact reject05920

  · exact reject05921

  · exact reject05922

  · exact reject05923

  · exact reject05924

  · exact reject05925

  · exact reject05926

  · exact reject05927

  · exact reject05928

  · exact reject05929

  · exact reject05930

  · exact reject05931

  · exact reject05932

  · exact reject05933

  · exact reject05934

  · exact reject05935

  · exact reject05936

  · exact reject05937

  · exact reject05938

  · exact reject05939

  · exact reject05940

  · exact reject05941

  · exact reject05942

  · exact reject05943

  · exact reject05944

  · exact reject05945

  · exact reject05946

  · exact reject05947

  · exact reject05948

  · exact reject05949

  · exact reject05950

  · exact reject05951

  · exact reject05952

  · exact reject05953

  · exact reject05954

  · exact reject05955

  · exact reject05956

  · exact reject05957

  · exact reject05958

  · exact reject05959

  · exact reject05960

  · exact reject05961

  · exact reject05962

  · exact reject05963

  · exact reject05964

  · exact reject05965

  · exact reject05966

  · exact reject05967

  · exact reject05968

  · exact reject05969

  · exact reject05970

  · exact reject05971

  · exact reject05972

  · exact reject05973

  · exact reject05974

  · exact reject05975

end PricingIntegration.RemainingGWitnesses
