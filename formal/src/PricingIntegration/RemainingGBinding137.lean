import PricingIntegration.RemainingGLayouts031

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks019

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks031

import PricingIntegration.RemainingGScopeChecks032

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind09864_0 : Agrees (spec (fastBase 1 65 0) layout0249) scope0316 := by decide

theorem reject09864 : Rejected (base 1 65 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 0) _ validLayout0249) (by decide) scope0316 (by rw [← fastBase_exact]; exact bind09864_0) certificate0321

private theorem bind09865_0 : Agrees (spec (fastBase 1 65 1) layout0249) scope0415 := by decide

theorem reject09865 : Rejected (base 1 65 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 1) _ validLayout0249) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind09865_0) certificate0438

private theorem bind09866_0 : Agrees (spec (fastBase 1 65 2) layout0249) scope0560 := by decide

theorem reject09866 : Rejected (base 1 65 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 2) _ validLayout0249) (by decide) scope0560 (by rw [← fastBase_exact]; exact bind09866_0) certificate0603

private theorem bind09867_0 : Agrees (spec (fastBase 1 65 3) layout0249) scope0468 := by decide

theorem reject09867 : Rejected (base 1 65 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 3) _ validLayout0249) (by decide) scope0468 (by rw [← fastBase_exact]; exact bind09867_0) certificate0504

private theorem bind09868_0 : Agrees (spec (fastBase 1 65 4) layout0250) scope0295 := by decide

theorem reject09868 : Rejected (base 1 65 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 4) _ validLayout0250) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind09868_0) certificate0300

private theorem bind09869_0 : Agrees (spec (fastBase 1 65 5) layout0249) scope0315 := by decide

theorem reject09869 : Rejected (base 1 65 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 5) _ validLayout0249) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind09869_0) certificate0320

private theorem bind09870_0 : Agrees (spec (fastBase 1 65 6) layout0249) scope0473 := by decide

theorem reject09870 : Rejected (base 1 65 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 6) _ validLayout0249) (by decide) scope0473 (by rw [← fastBase_exact]; exact bind09870_0) certificate0512

private theorem bind09871_0 : Agrees (spec (fastBase 1 65 7) layout0249) scope0474 := by decide

theorem reject09871 : Rejected (base 1 65 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 7) _ validLayout0249) (by decide) scope0474 (by rw [← fastBase_exact]; exact bind09871_0) certificate0513

private theorem bind09872_0 : Agrees (spec (fastBase 1 65 8) layout0250) scope0300 := by decide

private theorem bind09872_1 : Agrees (spec (fastBase 1 65 8) layout0251) scope0301 := by decide

theorem reject09872 : Rejected (base 1 65 8) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0250 layout0251 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 8) _ validLayout0250) (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 8) _ validLayout0251) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind09872_0) (by rw [← fastBase_exact]; exact bind09872_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind09873_0 : Agrees (spec (fastBase 1 65 9) layout0249) scope0414 := by decide

theorem reject09873 : Rejected (base 1 65 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 9) _ validLayout0249) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind09873_0) certificate0436

private theorem bind09874_0 : Agrees (spec (fastBase 1 65 10) layout0249) scope0475 := by decide

theorem reject09874 : Rejected (base 1 65 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 10) _ validLayout0249) (by decide) scope0475 (by rw [← fastBase_exact]; exact bind09874_0) certificate0514

private theorem bind09875_0 : Agrees (spec (fastBase 1 65 11) layout0249) scope0472 := by decide

theorem reject09875 : Rejected (base 1 65 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 11) _ validLayout0249) (by decide) scope0472 (by rw [← fastBase_exact]; exact bind09875_0) certificate0511

private theorem bind09876_0 : Agrees (spec (fastBase 1 65 12) layout0249) scope0415 := by decide

theorem reject09876 : Rejected (base 1 65 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 12) _ validLayout0249) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind09876_0) certificate0438

private theorem bind09877_0 : Agrees (spec (fastBase 1 65 13) layout0249) scope0560 := by decide

theorem reject09877 : Rejected (base 1 65 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 13) _ validLayout0249) (by decide) scope0560 (by rw [← fastBase_exact]; exact bind09877_0) certificate0603

private theorem bind09878_0 : Agrees (spec (fastBase 1 65 14) layout0249) scope0471 := by decide

theorem reject09878 : Rejected (base 1 65 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 14) _ validLayout0249) (by decide) scope0471 (by rw [← fastBase_exact]; exact bind09878_0) certificate0509

private theorem bind09879_0 : Agrees (spec (fastBase 1 65 15) layout0249) scope0319 := by decide

theorem reject09879 : Rejected (base 1 65 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 15) _ validLayout0249) (by decide) scope0319 (by rw [← fastBase_exact]; exact bind09879_0) certificate0325

private theorem bind09880_0 : Agrees (spec (fastBase 1 65 16) layout0249) scope0316 := by decide

theorem reject09880 : Rejected (base 1 65 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 16) _ validLayout0249) (by decide) scope0316 (by rw [← fastBase_exact]; exact bind09880_0) certificate0321

private theorem bind09881_0 : Agrees (spec (fastBase 1 65 17) layout0249) scope0316 := by decide

theorem reject09881 : Rejected (base 1 65 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 17) _ validLayout0249) (by decide) scope0316 (by rw [← fastBase_exact]; exact bind09881_0) certificate0321

private theorem bind09882_0 : Agrees (spec (fastBase 1 65 18) layout0249) scope0415 := by decide

theorem reject09882 : Rejected (base 1 65 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 18) _ validLayout0249) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind09882_0) certificate0438

private theorem bind09883_0 : Agrees (spec (fastBase 1 65 19) layout0250) scope0295 := by decide

theorem reject09883 : Rejected (base 1 65 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 19) _ validLayout0250) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind09883_0) certificate0300

private theorem bind09884_0 : Agrees (spec (fastBase 1 65 20) layout0250) scope0312 := by decide

theorem reject09884 : Rejected (base 1 65 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 20) _ validLayout0250) (by decide) scope0312 (by rw [← fastBase_exact]; exact bind09884_0) certificate0317

private theorem bind09885_0 : Agrees (spec (fastBase 1 65 21) layout0249) scope0467 := by decide

theorem reject09885 : Rejected (base 1 65 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 21) _ validLayout0249) (by decide) scope0467 (by rw [← fastBase_exact]; exact bind09885_0) certificate0503

private theorem bind09886_0 : Agrees (spec (fastBase 1 65 22) layout0249) scope0316 := by decide

theorem reject09886 : Rejected (base 1 65 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 22) _ validLayout0249) (by decide) scope0316 (by rw [← fastBase_exact]; exact bind09886_0) certificate0321

private theorem bind09887_0 : Agrees (spec (fastBase 1 65 23) layout0250) scope0308 := by decide

theorem reject09887 : Rejected (base 1 65 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 23) _ validLayout0250) (by decide) scope0308 (by rw [← fastBase_exact]; exact bind09887_0) certificate0313

private theorem bind09888_0 : Agrees (spec (fastBase 1 65 24) layout0249) scope0560 := by decide

theorem reject09888 : Rejected (base 1 65 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 24) _ validLayout0249) (by decide) scope0560 (by rw [← fastBase_exact]; exact bind09888_0) certificate0603

private theorem bind09889_0 : Agrees (spec (fastBase 1 65 25) layout0249) scope0473 := by decide

theorem reject09889 : Rejected (base 1 65 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 25) _ validLayout0249) (by decide) scope0473 (by rw [← fastBase_exact]; exact bind09889_0) certificate0512

private theorem bind09890_0 : Agrees (spec (fastBase 1 65 26) layout0249) scope0561 := by decide

theorem reject09890 : Rejected (base 1 65 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 26) _ validLayout0249) (by decide) scope0561 (by rw [← fastBase_exact]; exact bind09890_0) certificate0604

private theorem bind09891_0 : Agrees (spec (fastBase 1 65 27) layout0249) scope0468 := by decide

theorem reject09891 : Rejected (base 1 65 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 27) _ validLayout0249) (by decide) scope0468 (by rw [← fastBase_exact]; exact bind09891_0) certificate0504

private theorem bind09892_0 : Agrees (spec (fastBase 1 65 28) layout0249) scope0468 := by decide

theorem reject09892 : Rejected (base 1 65 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 28) _ validLayout0249) (by decide) scope0468 (by rw [← fastBase_exact]; exact bind09892_0) certificate0504

private theorem bind09893_0 : Agrees (spec (fastBase 1 65 29) layout0249) scope0468 := by decide

theorem reject09893 : Rejected (base 1 65 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 29) _ validLayout0249) (by decide) scope0468 (by rw [← fastBase_exact]; exact bind09893_0) certificate0504

private theorem bind09894_0 : Agrees (spec (fastBase 1 65 30) layout0249) scope0468 := by decide

theorem reject09894 : Rejected (base 1 65 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 30) _ validLayout0249) (by decide) scope0468 (by rw [← fastBase_exact]; exact bind09894_0) certificate0504

private theorem bind09895_0 : Agrees (spec (fastBase 1 65 31) layout0249) scope0468 := by decide

theorem reject09895 : Rejected (base 1 65 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 31) _ validLayout0249) (by decide) scope0468 (by rw [← fastBase_exact]; exact bind09895_0) certificate0504

private theorem bind09896_0 : Agrees (spec (fastBase 1 65 32) layout0249) scope0415 := by decide

theorem reject09896 : Rejected (base 1 65 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 32) _ validLayout0249) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind09896_0) certificate0438

private theorem bind09897_0 : Agrees (spec (fastBase 1 65 33) layout0249) scope0471 := by decide

theorem reject09897 : Rejected (base 1 65 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 33) _ validLayout0249) (by decide) scope0471 (by rw [← fastBase_exact]; exact bind09897_0) certificate0509

private theorem bind09898_0 : Agrees (spec (fastBase 1 65 34) layout0249) scope0315 := by decide

theorem reject09898 : Rejected (base 1 65 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 34) _ validLayout0249) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind09898_0) certificate0320

private theorem bind09899_0 : Agrees (spec (fastBase 1 65 35) layout0251) scope0414 := by decide

theorem reject09899 : Rejected (base 1 65 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0251 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 35) _ validLayout0251) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind09899_0) certificate0436

private theorem bind09900_0 : Agrees (spec (fastBase 1 65 36) layout0249) scope0466 := by decide

theorem reject09900 : Rejected (base 1 65 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 36) _ validLayout0249) (by decide) scope0466 (by rw [← fastBase_exact]; exact bind09900_0) certificate0502

private theorem bind09901_0 : Agrees (spec (fastBase 1 65 37) layout0249) scope0467 := by decide

theorem reject09901 : Rejected (base 1 65 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 37) _ validLayout0249) (by decide) scope0467 (by rw [← fastBase_exact]; exact bind09901_0) certificate0503

private theorem bind09902_0 : Agrees (spec (fastBase 1 65 38) layout0250) scope0297 := by decide

theorem reject09902 : Rejected (base 1 65 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 38) _ validLayout0250) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind09902_0) certificate0302

private theorem bind09903_0 : Agrees (spec (fastBase 1 65 39) layout0249) scope0315 := by decide

theorem reject09903 : Rejected (base 1 65 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 39) _ validLayout0249) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind09903_0) certificate0320

private theorem bind09904_0 : Agrees (spec (fastBase 1 65 40) layout0249) scope0414 := by decide

theorem reject09904 : Rejected (base 1 65 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 40) _ validLayout0249) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind09904_0) certificate0436

private theorem bind09905_0 : Agrees (spec (fastBase 1 65 41) layout0250) scope0318 := by decide

theorem reject09905 : Rejected (base 1 65 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 41) _ validLayout0250) (by decide) scope0318 (by rw [← fastBase_exact]; exact bind09905_0) certificate0324

private theorem bind09906_0 : Agrees (spec (fastBase 1 65 42) layout0249) scope0319 := by decide

theorem reject09906 : Rejected (base 1 65 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 42) _ validLayout0249) (by decide) scope0319 (by rw [← fastBase_exact]; exact bind09906_0) certificate0325

private theorem bind09907_0 : Agrees (spec (fastBase 1 65 43) layout0249) scope0560 := by decide

theorem reject09907 : Rejected (base 1 65 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 43) _ validLayout0249) (by decide) scope0560 (by rw [← fastBase_exact]; exact bind09907_0) certificate0603

private theorem bind09908_0 : Agrees (spec (fastBase 1 65 44) layout0249) scope0473 := by decide

theorem reject09908 : Rejected (base 1 65 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 44) _ validLayout0249) (by decide) scope0473 (by rw [← fastBase_exact]; exact bind09908_0) certificate0512

private theorem bind09909_0 : Agrees (spec (fastBase 1 65 45) layout0249) scope0474 := by decide

theorem reject09909 : Rejected (base 1 65 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 45) _ validLayout0249) (by decide) scope0474 (by rw [← fastBase_exact]; exact bind09909_0) certificate0513

private theorem bind09910_0 : Agrees (spec (fastBase 1 65 46) layout0249) scope0477 := by decide

theorem reject09910 : Rejected (base 1 65 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 46) _ validLayout0249) (by decide) scope0477 (by rw [← fastBase_exact]; exact bind09910_0) certificate0516

private theorem bind09911_0 : Agrees (spec (fastBase 1 65 47) layout0249) scope0561 := by decide

theorem reject09911 : Rejected (base 1 65 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 47) _ validLayout0249) (by decide) scope0561 (by rw [← fastBase_exact]; exact bind09911_0) certificate0604

private theorem bind09912_0 : Agrees (spec (fastBase 1 65 48) layout0249) scope0474 := by decide

theorem reject09912 : Rejected (base 1 65 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 48) _ validLayout0249) (by decide) scope0474 (by rw [← fastBase_exact]; exact bind09912_0) certificate0513

private theorem bind09913_0 : Agrees (spec (fastBase 1 65 49) layout0249) scope0473 := by decide

theorem reject09913 : Rejected (base 1 65 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 49) _ validLayout0249) (by decide) scope0473 (by rw [← fastBase_exact]; exact bind09913_0) certificate0512

private theorem bind09914_0 : Agrees (spec (fastBase 1 65 50) layout0249) scope0476 := by decide

theorem reject09914 : Rejected (base 1 65 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 50) _ validLayout0249) (by decide) scope0476 (by rw [← fastBase_exact]; exact bind09914_0) certificate0515

private theorem bind09915_0 : Agrees (spec (fastBase 1 65 51) layout0249) scope0475 := by decide

theorem reject09915 : Rejected (base 1 65 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 51) _ validLayout0249) (by decide) scope0475 (by rw [← fastBase_exact]; exact bind09915_0) certificate0514

private theorem bind09916_0 : Agrees (spec (fastBase 1 65 52) layout0250) scope0296 := by decide

theorem reject09916 : Rejected (base 1 65 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 52) _ validLayout0250) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind09916_0) certificate0301

private theorem bind09917_0 : Agrees (spec (fastBase 1 65 53) layout0250) scope0295 := by decide

theorem reject09917 : Rejected (base 1 65 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 53) _ validLayout0250) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind09917_0) certificate0300

private theorem bind09918_0 : Agrees (spec (fastBase 1 65 54) layout0250) scope0300 := by decide

private theorem bind09918_1 : Agrees (spec (fastBase 1 65 54) layout0251) scope0301 := by decide

theorem reject09918 : Rejected (base 1 65 54) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0250 layout0251 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 54) _ validLayout0250) (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 54) _ validLayout0251) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind09918_0) (by rw [← fastBase_exact]; exact bind09918_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind09919_0 : Agrees (spec (fastBase 1 65 55) layout0250) scope0300 := by decide

private theorem bind09919_1 : Agrees (spec (fastBase 1 65 55) layout0251) scope0306 := by decide

theorem reject09919 : Rejected (base 1 65 55) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0250 layout0251 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 55) _ validLayout0250) (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 55) _ validLayout0251) (by decide) (by decide) scope0300 scope0306 (by rw [← fastBase_exact]; exact bind09919_0) (by rw [← fastBase_exact]; exact bind09919_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0322 (by decide)

private theorem bind09920_0 : Agrees (spec (fastBase 1 65 56) layout0251) scope0316 := by decide

theorem reject09920 : Rejected (base 1 65 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0251 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 56) _ validLayout0251) (by decide) scope0316 (by rw [← fastBase_exact]; exact bind09920_0) certificate0321

private theorem bind09921_0 : Agrees (spec (fastBase 1 65 57) layout0249) scope0466 := by decide

theorem reject09921 : Rejected (base 1 65 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 57) _ validLayout0249) (by decide) scope0466 (by rw [← fastBase_exact]; exact bind09921_0) certificate0502

private theorem bind09922_0 : Agrees (spec (fastBase 1 65 58) layout0249) scope0315 := by decide

theorem reject09922 : Rejected (base 1 65 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 58) _ validLayout0249) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind09922_0) certificate0320

private theorem bind09923_0 : Agrees (spec (fastBase 1 65 59) layout0249) scope0414 := by decide

theorem reject09923 : Rejected (base 1 65 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 59) _ validLayout0249) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind09923_0) certificate0436

private theorem bind09924_0 : Agrees (spec (fastBase 1 65 60) layout0249) scope0313 := by decide

theorem reject09924 : Rejected (base 1 65 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 60) _ validLayout0249) (by decide) scope0313 (by rw [← fastBase_exact]; exact bind09924_0) certificate0318

private theorem bind09925_0 : Agrees (spec (fastBase 1 65 61) layout0249) scope0472 := by decide

theorem reject09925 : Rejected (base 1 65 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 61) _ validLayout0249) (by decide) scope0472 (by rw [← fastBase_exact]; exact bind09925_0) certificate0511

private theorem bind09926_0 : Agrees (spec (fastBase 1 65 62) layout0249) scope0477 := by decide

theorem reject09926 : Rejected (base 1 65 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 62) _ validLayout0249) (by decide) scope0477 (by rw [← fastBase_exact]; exact bind09926_0) certificate0516

private theorem bind09927_0 : Agrees (spec (fastBase 1 65 63) layout0249) scope0313 := by decide

theorem reject09927 : Rejected (base 1 65 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 63) _ validLayout0249) (by decide) scope0313 (by rw [← fastBase_exact]; exact bind09927_0) certificate0318

private theorem bind09928_0 : Agrees (spec (fastBase 1 65 64) layout0249) scope0474 := by decide

theorem reject09928 : Rejected (base 1 65 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 64) _ validLayout0249) (by decide) scope0474 (by rw [← fastBase_exact]; exact bind09928_0) certificate0513

private theorem bind09929_0 : Agrees (spec (fastBase 1 65 65) layout0249) scope0475 := by decide

theorem reject09929 : Rejected (base 1 65 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 65) _ validLayout0249) (by decide) scope0475 (by rw [← fastBase_exact]; exact bind09929_0) certificate0514

private theorem bind09930_0 : Agrees (spec (fastBase 1 65 66) layout0249) scope0472 := by decide

theorem reject09930 : Rejected (base 1 65 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 66) _ validLayout0249) (by decide) scope0472 (by rw [← fastBase_exact]; exact bind09930_0) certificate0511

private theorem bind09931_0 : Agrees (spec (fastBase 1 65 67) layout0249) scope0472 := by decide

theorem reject09931 : Rejected (base 1 65 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 67) _ validLayout0249) (by decide) scope0472 (by rw [← fastBase_exact]; exact bind09931_0) certificate0511

private theorem bind09932_0 : Agrees (spec (fastBase 1 65 68) layout0250) scope0314 := by decide

theorem reject09932 : Rejected (base 1 65 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0250 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 68) _ validLayout0250) (by decide) scope0314 (by rw [← fastBase_exact]; exact bind09932_0) certificate0319

private theorem bind09933_0 : Agrees (spec (fastBase 1 65 69) layout0249) scope0476 := by decide

theorem reject09933 : Rejected (base 1 65 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 69) _ validLayout0249) (by decide) scope0476 (by rw [← fastBase_exact]; exact bind09933_0) certificate0515

private theorem bind09934_0 : Agrees (spec (fastBase 1 65 70) layout0249) scope0414 := by decide

theorem reject09934 : Rejected (base 1 65 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 70) _ validLayout0249) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind09934_0) certificate0436

private theorem bind09935_0 : Agrees (spec (fastBase 1 65 71) layout0249) scope0475 := by decide

theorem reject09935 : Rejected (base 1 65 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0249 (layoutValid_of_refines _ _ (base_refines_skeleton 1 65 71) _ validLayout0249) (by decide) scope0475 (by rw [← fastBase_exact]; exact bind09935_0) certificate0514

theorem allCases137 : ∀ y : Fin 72, Rejected (base 1 65 y) := by
  intro y
  fin_cases y

  · exact reject09864

  · exact reject09865

  · exact reject09866

  · exact reject09867

  · exact reject09868

  · exact reject09869

  · exact reject09870

  · exact reject09871

  · exact reject09872

  · exact reject09873

  · exact reject09874

  · exact reject09875

  · exact reject09876

  · exact reject09877

  · exact reject09878

  · exact reject09879

  · exact reject09880

  · exact reject09881

  · exact reject09882

  · exact reject09883

  · exact reject09884

  · exact reject09885

  · exact reject09886

  · exact reject09887

  · exact reject09888

  · exact reject09889

  · exact reject09890

  · exact reject09891

  · exact reject09892

  · exact reject09893

  · exact reject09894

  · exact reject09895

  · exact reject09896

  · exact reject09897

  · exact reject09898

  · exact reject09899

  · exact reject09900

  · exact reject09901

  · exact reject09902

  · exact reject09903

  · exact reject09904

  · exact reject09905

  · exact reject09906

  · exact reject09907

  · exact reject09908

  · exact reject09909

  · exact reject09910

  · exact reject09911

  · exact reject09912

  · exact reject09913

  · exact reject09914

  · exact reject09915

  · exact reject09916

  · exact reject09917

  · exact reject09918

  · exact reject09919

  · exact reject09920

  · exact reject09921

  · exact reject09922

  · exact reject09923

  · exact reject09924

  · exact reject09925

  · exact reject09926

  · exact reject09927

  · exact reject09928

  · exact reject09929

  · exact reject09930

  · exact reject09931

  · exact reject09932

  · exact reject09933

  · exact reject09934

  · exact reject09935

end PricingIntegration.RemainingGWitnesses
