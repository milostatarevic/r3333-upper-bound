import PricingIntegration.RemainingGLayouts019

import PricingIntegration.RemainingGLayouts020

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks017

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks026

import PricingIntegration.RemainingGScopeChecks027


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02880_0 : Agrees (spec (fastBase 0 40 0) layout0156) scope0274 := by decide

theorem reject02880 : Rejected (base 0 40 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 0) _ validLayout0156) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind02880_0) certificate0277

private theorem bind02881_0 : Agrees (spec (fastBase 0 40 1) layout0156) scope0269 := by decide

theorem reject02881 : Rejected (base 0 40 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 1) _ validLayout0156) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind02881_0) certificate0272

private theorem bind02882_0 : Agrees (spec (fastBase 0 40 2) layout0156) scope0271 := by decide

theorem reject02882 : Rejected (base 0 40 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 2) _ validLayout0156) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind02882_0) certificate0274

private theorem bind02883_0 : Agrees (spec (fastBase 0 40 3) layout0156) scope0278 := by decide

theorem reject02883 : Rejected (base 0 40 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 3) _ validLayout0156) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind02883_0) certificate0281

private theorem bind02884_0 : Agrees (spec (fastBase 0 40 4) layout0156) scope0266 := by decide

theorem reject02884 : Rejected (base 0 40 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 4) _ validLayout0156) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind02884_0) certificate0269

private theorem bind02885_0 : Agrees (spec (fastBase 0 40 5) layout0156) scope0275 := by decide

theorem reject02885 : Rejected (base 0 40 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 5) _ validLayout0156) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind02885_0) certificate0278

private theorem bind02886_0 : Agrees (spec (fastBase 0 40 6) layout0156) scope0267 := by decide

theorem reject02886 : Rejected (base 0 40 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 6) _ validLayout0156) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind02886_0) certificate0270

private theorem bind02887_0 : Agrees (spec (fastBase 0 40 7) layout0156) scope0290 := by decide

private theorem bind02887_1 : Agrees (spec (fastBase 0 40 7) layout0157) scope0273 := by decide

theorem reject02887 : Rejected (base 0 40 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0156 layout0157 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 7) _ validLayout0156) (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 7) _ validLayout0157) (by decide) (by decide) scope0290 scope0273 (by rw [← fastBase_exact]; exact bind02887_0) (by rw [← fastBase_exact]; exact bind02887_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0293 certificate0276 (by decide)

private theorem bind02888_0 : Agrees (spec (fastBase 0 40 8) layout0156) scope0265 := by decide

theorem reject02888 : Rejected (base 0 40 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 8) _ validLayout0156) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind02888_0) certificate0268

private theorem bind02889_0 : Agrees (spec (fastBase 0 40 9) layout0156) scope0270 := by decide

theorem reject02889 : Rejected (base 0 40 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 9) _ validLayout0156) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind02889_0) certificate0273

private theorem bind02890_0 : Agrees (spec (fastBase 0 40 10) layout0156) scope0272 := by decide

private theorem bind02890_1 : Agrees (spec (fastBase 0 40 10) layout0157) scope0276 := by decide

theorem reject02890 : Rejected (base 0 40 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0156 layout0157 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 10) _ validLayout0156) (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 10) _ validLayout0157) (by decide) (by decide) scope0272 scope0276 (by rw [← fastBase_exact]; exact bind02890_0) (by rw [← fastBase_exact]; exact bind02890_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0295 certificate0296 (by decide)

private theorem bind02891_0 : Agrees (spec (fastBase 0 40 11) layout0156) scope0268 := by decide

theorem reject02891 : Rejected (base 0 40 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 11) _ validLayout0156) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind02891_0) certificate0271

private theorem bind02892_0 : Agrees (spec (fastBase 0 40 12) layout0156) scope0274 := by decide

theorem reject02892 : Rejected (base 0 40 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 12) _ validLayout0156) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind02892_0) certificate0277

private theorem bind02893_0 : Agrees (spec (fastBase 0 40 13) layout0156) scope0271 := by decide

theorem reject02893 : Rejected (base 0 40 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 13) _ validLayout0156) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind02893_0) certificate0274

private theorem bind02894_0 : Agrees (spec (fastBase 0 40 14) layout0158) scope0408 := by decide

theorem reject02894 : Rejected (base 0 40 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0158 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 14) _ validLayout0158) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind02894_0) certificate0428

private theorem bind02895_0 : Agrees (spec (fastBase 0 40 15) layout0158) scope0411 := by decide

theorem reject02895 : Rejected (base 0 40 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0158 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 15) _ validLayout0158) (by decide) scope0411 (by rw [← fastBase_exact]; exact bind02895_0) certificate0431

private theorem bind02896_0 : Agrees (spec (fastBase 0 40 16) layout0156) scope0283 := by decide

theorem reject02896 : Rejected (base 0 40 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 16) _ validLayout0156) (by decide) scope0283 (by rw [← fastBase_exact]; exact bind02896_0) certificate0286

private theorem bind02897_0 : Agrees (spec (fastBase 0 40 17) layout0156) scope0269 := by decide

theorem reject02897 : Rejected (base 0 40 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 17) _ validLayout0156) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind02897_0) certificate0272

private theorem bind02898_0 : Agrees (spec (fastBase 0 40 18) layout0156) scope0269 := by decide

theorem reject02898 : Rejected (base 0 40 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 18) _ validLayout0156) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind02898_0) certificate0272

private theorem bind02899_0 : Agrees (spec (fastBase 0 40 19) layout0156) scope0269 := by decide

theorem reject02899 : Rejected (base 0 40 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 19) _ validLayout0156) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind02899_0) certificate0272

private theorem bind02900_0 : Agrees (spec (fastBase 0 40 20) layout0156) scope0269 := by decide

theorem reject02900 : Rejected (base 0 40 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 20) _ validLayout0156) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind02900_0) certificate0272

private theorem bind02901_0 : Agrees (spec (fastBase 0 40 21) layout0156) scope0269 := by decide

theorem reject02901 : Rejected (base 0 40 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 21) _ validLayout0156) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind02901_0) certificate0272

private theorem bind02902_0 : Agrees (spec (fastBase 0 40 22) layout0156) scope0274 := by decide

theorem reject02902 : Rejected (base 0 40 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 22) _ validLayout0156) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind02902_0) certificate0277

private theorem bind02903_0 : Agrees (spec (fastBase 0 40 23) layout0156) scope0286 := by decide

theorem reject02903 : Rejected (base 0 40 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 23) _ validLayout0156) (by decide) scope0286 (by rw [← fastBase_exact]; exact bind02903_0) certificate0289

private theorem bind02904_0 : Agrees (spec (fastBase 0 40 24) layout0156) scope0278 := by decide

theorem reject02904 : Rejected (base 0 40 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 24) _ validLayout0156) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind02904_0) certificate0281

private theorem bind02905_0 : Agrees (spec (fastBase 0 40 25) layout0156) scope0287 := by decide

theorem reject02905 : Rejected (base 0 40 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 25) _ validLayout0156) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind02905_0) certificate0290

private theorem bind02906_0 : Agrees (spec (fastBase 0 40 26) layout0156) scope0271 := by decide

theorem reject02906 : Rejected (base 0 40 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 26) _ validLayout0156) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind02906_0) certificate0274

private theorem bind02907_0 : Agrees (spec (fastBase 0 40 27) layout0156) scope0278 := by decide

theorem reject02907 : Rejected (base 0 40 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 27) _ validLayout0156) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind02907_0) certificate0281

private theorem bind02908_0 : Agrees (spec (fastBase 0 40 28) layout0156) scope0271 := by decide

theorem reject02908 : Rejected (base 0 40 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 28) _ validLayout0156) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind02908_0) certificate0274

private theorem bind02909_0 : Agrees (spec (fastBase 0 40 29) layout0156) scope0275 := by decide

theorem reject02909 : Rejected (base 0 40 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 29) _ validLayout0156) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind02909_0) certificate0278

private theorem bind02910_0 : Agrees (spec (fastBase 0 40 30) layout0158) scope0408 := by decide

theorem reject02910 : Rejected (base 0 40 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0158 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 30) _ validLayout0158) (by decide) scope0408 (by rw [← fastBase_exact]; exact bind02910_0) certificate0428

private theorem bind02911_0 : Agrees (spec (fastBase 0 40 31) layout0156) scope0282 := by decide

theorem reject02911 : Rejected (base 0 40 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 31) _ validLayout0156) (by decide) scope0282 (by rw [← fastBase_exact]; exact bind02911_0) certificate0285

private theorem bind02912_0 : Agrees (spec (fastBase 0 40 32) layout0156) scope0266 := by decide

theorem reject02912 : Rejected (base 0 40 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 32) _ validLayout0156) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind02912_0) certificate0269

private theorem bind02913_0 : Agrees (spec (fastBase 0 40 33) layout0156) scope0282 := by decide

theorem reject02913 : Rejected (base 0 40 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 33) _ validLayout0156) (by decide) scope0282 (by rw [← fastBase_exact]; exact bind02913_0) certificate0285

private theorem bind02914_0 : Agrees (spec (fastBase 0 40 34) layout0156) scope0275 := by decide

theorem reject02914 : Rejected (base 0 40 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 34) _ validLayout0156) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind02914_0) certificate0278

private theorem bind02915_0 : Agrees (spec (fastBase 0 40 35) layout0156) scope0281 := by decide

theorem reject02915 : Rejected (base 0 40 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 35) _ validLayout0156) (by decide) scope0281 (by rw [← fastBase_exact]; exact bind02915_0) certificate0284

private theorem bind02916_0 : Agrees (spec (fastBase 0 40 36) layout0156) scope0268 := by decide

theorem reject02916 : Rejected (base 0 40 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 36) _ validLayout0156) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind02916_0) certificate0271

private theorem bind02917_0 : Agrees (spec (fastBase 0 40 37) layout0156) scope0286 := by decide

theorem reject02917 : Rejected (base 0 40 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 37) _ validLayout0156) (by decide) scope0286 (by rw [← fastBase_exact]; exact bind02917_0) certificate0289

private theorem bind02918_0 : Agrees (spec (fastBase 0 40 38) layout0156) scope0266 := by decide

theorem reject02918 : Rejected (base 0 40 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 38) _ validLayout0156) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind02918_0) certificate0269

private theorem bind02919_0 : Agrees (spec (fastBase 0 40 39) layout0156) scope0278 := by decide

theorem reject02919 : Rejected (base 0 40 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 39) _ validLayout0156) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind02919_0) certificate0281

private theorem bind02920_0 : Agrees (spec (fastBase 0 40 40) layout0156) scope0284 := by decide

theorem reject02920 : Rejected (base 0 40 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 40) _ validLayout0156) (by decide) scope0284 (by rw [← fastBase_exact]; exact bind02920_0) certificate0287

private theorem bind02921_0 : Agrees (spec (fastBase 0 40 41) layout0156) scope0275 := by decide

theorem reject02921 : Rejected (base 0 40 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 41) _ validLayout0156) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind02921_0) certificate0278

private theorem bind02922_0 : Agrees (spec (fastBase 0 40 42) layout0156) scope0267 := by decide

theorem reject02922 : Rejected (base 0 40 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 42) _ validLayout0156) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind02922_0) certificate0270

private theorem bind02923_0 : Agrees (spec (fastBase 0 40 43) layout0156) scope0283 := by decide

theorem reject02923 : Rejected (base 0 40 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 43) _ validLayout0156) (by decide) scope0283 (by rw [← fastBase_exact]; exact bind02923_0) certificate0286

private theorem bind02924_0 : Agrees (spec (fastBase 0 40 44) layout0156) scope0265 := by decide

theorem reject02924 : Rejected (base 0 40 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 44) _ validLayout0156) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind02924_0) certificate0268

private theorem bind02925_0 : Agrees (spec (fastBase 0 40 45) layout0157) scope0288 := by decide

theorem reject02925 : Rejected (base 0 40 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0157 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 45) _ validLayout0157) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind02925_0) certificate0291

private theorem bind02926_0 : Agrees (spec (fastBase 0 40 46) layout0158) scope0412 := by decide

theorem reject02926 : Rejected (base 0 40 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0158 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 46) _ validLayout0158) (by decide) scope0412 (by rw [← fastBase_exact]; exact bind02926_0) certificate0432

private theorem bind02927_0 : Agrees (spec (fastBase 0 40 47) layout0156) scope0274 := by decide

theorem reject02927 : Rejected (base 0 40 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 47) _ validLayout0156) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind02927_0) certificate0277

private theorem bind02928_0 : Agrees (spec (fastBase 0 40 48) layout0156) scope0287 := by decide

theorem reject02928 : Rejected (base 0 40 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 48) _ validLayout0156) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind02928_0) certificate0290

private theorem bind02929_0 : Agrees (spec (fastBase 0 40 49) layout0156) scope0267 := by decide

theorem reject02929 : Rejected (base 0 40 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 49) _ validLayout0156) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind02929_0) certificate0270

private theorem bind02930_0 : Agrees (spec (fastBase 0 40 50) layout0156) scope0280 := by decide

theorem reject02930 : Rejected (base 0 40 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 50) _ validLayout0156) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind02930_0) certificate0283

private theorem bind02931_0 : Agrees (spec (fastBase 0 40 51) layout0157) scope0276 := by decide

private theorem bind02931_1 : Agrees (spec (fastBase 0 40 51) layout0159) scope0404 := by decide

theorem reject02931 : Rejected (base 0 40 51) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0157 layout0159 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 51) _ validLayout0157) (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 51) _ validLayout0159) (by decide) (by decide) scope0276 scope0404 (by rw [← fastBase_exact]; exact bind02931_0) (by rw [← fastBase_exact]; exact bind02931_1) 4 9 4 9 (by decide) (by decide) 3 2 (by decide) certificate0433 certificate0434 (by decide)

private theorem bind02932_0 : Agrees (spec (fastBase 0 40 52) layout0156) scope0280 := by decide

theorem reject02932 : Rejected (base 0 40 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 52) _ validLayout0156) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind02932_0) certificate0283

private theorem bind02933_0 : Agrees (spec (fastBase 0 40 53) layout0156) scope0279 := by decide

theorem reject02933 : Rejected (base 0 40 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 53) _ validLayout0156) (by decide) scope0279 (by rw [← fastBase_exact]; exact bind02933_0) certificate0282

private theorem bind02934_0 : Agrees (spec (fastBase 0 40 54) layout0156) scope0267 := by decide

theorem reject02934 : Rejected (base 0 40 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 54) _ validLayout0156) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind02934_0) certificate0270

private theorem bind02935_0 : Agrees (spec (fastBase 0 40 55) layout0156) scope0270 := by decide

theorem reject02935 : Rejected (base 0 40 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 55) _ validLayout0156) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind02935_0) certificate0273

private theorem bind02936_0 : Agrees (spec (fastBase 0 40 56) layout0156) scope0265 := by decide

theorem reject02936 : Rejected (base 0 40 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 56) _ validLayout0156) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind02936_0) certificate0268

private theorem bind02937_0 : Agrees (spec (fastBase 0 40 57) layout0156) scope0270 := by decide

theorem reject02937 : Rejected (base 0 40 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 57) _ validLayout0156) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind02937_0) certificate0273

private theorem bind02938_0 : Agrees (spec (fastBase 0 40 58) layout0156) scope0281 := by decide

theorem reject02938 : Rejected (base 0 40 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 58) _ validLayout0156) (by decide) scope0281 (by rw [← fastBase_exact]; exact bind02938_0) certificate0284

private theorem bind02939_0 : Agrees (spec (fastBase 0 40 59) layout0156) scope0265 := by decide

theorem reject02939 : Rejected (base 0 40 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 59) _ validLayout0156) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind02939_0) certificate0268

private theorem bind02940_0 : Agrees (spec (fastBase 0 40 60) layout0158) scope0413 := by decide

theorem reject02940 : Rejected (base 0 40 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0158 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 60) _ validLayout0158) (by decide) scope0413 (by rw [← fastBase_exact]; exact bind02940_0) certificate0435

private theorem bind02941_0 : Agrees (spec (fastBase 0 40 61) layout0156) scope0268 := by decide

theorem reject02941 : Rejected (base 0 40 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 61) _ validLayout0156) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind02941_0) certificate0271

private theorem bind02942_0 : Agrees (spec (fastBase 0 40 62) layout0157) scope0291 := by decide

theorem reject02942 : Rejected (base 0 40 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0157 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 62) _ validLayout0157) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind02942_0) certificate0294

private theorem bind02943_0 : Agrees (spec (fastBase 0 40 63) layout0160) scope0157 := by decide

theorem reject02943 : Rejected (base 0 40 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0160 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 63) _ validLayout0160) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind02943_0) certificate0160

private theorem bind02944_0 : Agrees (spec (fastBase 0 40 64) layout0156) scope0272 := by decide

private theorem bind02944_1 : Agrees (spec (fastBase 0 40 64) layout0157) scope0273 := by decide

theorem reject02944 : Rejected (base 0 40 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0156 layout0157 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 64) _ validLayout0156) (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 64) _ validLayout0157) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind02944_0) (by rw [← fastBase_exact]; exact bind02944_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind02945_0 : Agrees (spec (fastBase 0 40 65) layout0160) scope0150 := by decide

theorem reject02945 : Rejected (base 0 40 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0160 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 65) _ validLayout0160) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02945_0) certificate0153

private theorem bind02946_0 : Agrees (spec (fastBase 0 40 66) layout0160) scope0168 := by decide

theorem reject02946 : Rejected (base 0 40 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0160 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 66) _ validLayout0160) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind02946_0) certificate0171

private theorem bind02947_0 : Agrees (spec (fastBase 0 40 67) layout0156) scope0284 := by decide

theorem reject02947 : Rejected (base 0 40 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 67) _ validLayout0156) (by decide) scope0284 (by rw [← fastBase_exact]; exact bind02947_0) certificate0287

private theorem bind02948_0 : Agrees (spec (fastBase 0 40 68) layout0156) scope0266 := by decide

theorem reject02948 : Rejected (base 0 40 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 68) _ validLayout0156) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind02948_0) certificate0269

private theorem bind02949_0 : Agrees (spec (fastBase 0 40 69) layout0156) scope0279 := by decide

theorem reject02949 : Rejected (base 0 40 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 69) _ validLayout0156) (by decide) scope0279 (by rw [← fastBase_exact]; exact bind02949_0) certificate0282

private theorem bind02950_0 : Agrees (spec (fastBase 0 40 70) layout0156) scope0270 := by decide

theorem reject02950 : Rejected (base 0 40 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 70) _ validLayout0156) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind02950_0) certificate0273

private theorem bind02951_0 : Agrees (spec (fastBase 0 40 71) layout0156) scope0268 := by decide

theorem reject02951 : Rejected (base 0 40 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0156 (layoutValid_of_refines _ _ (base_refines_skeleton 0 40 71) _ validLayout0156) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind02951_0) certificate0271

theorem allCases040 : ∀ y : Fin 72, Rejected (base 0 40 y) := by
  intro y
  fin_cases y

  · exact reject02880

  · exact reject02881

  · exact reject02882

  · exact reject02883

  · exact reject02884

  · exact reject02885

  · exact reject02886

  · exact reject02887

  · exact reject02888

  · exact reject02889

  · exact reject02890

  · exact reject02891

  · exact reject02892

  · exact reject02893

  · exact reject02894

  · exact reject02895

  · exact reject02896

  · exact reject02897

  · exact reject02898

  · exact reject02899

  · exact reject02900

  · exact reject02901

  · exact reject02902

  · exact reject02903

  · exact reject02904

  · exact reject02905

  · exact reject02906

  · exact reject02907

  · exact reject02908

  · exact reject02909

  · exact reject02910

  · exact reject02911

  · exact reject02912

  · exact reject02913

  · exact reject02914

  · exact reject02915

  · exact reject02916

  · exact reject02917

  · exact reject02918

  · exact reject02919

  · exact reject02920

  · exact reject02921

  · exact reject02922

  · exact reject02923

  · exact reject02924

  · exact reject02925

  · exact reject02926

  · exact reject02927

  · exact reject02928

  · exact reject02929

  · exact reject02930

  · exact reject02931

  · exact reject02932

  · exact reject02933

  · exact reject02934

  · exact reject02935

  · exact reject02936

  · exact reject02937

  · exact reject02938

  · exact reject02939

  · exact reject02940

  · exact reject02941

  · exact reject02942

  · exact reject02943

  · exact reject02944

  · exact reject02945

  · exact reject02946

  · exact reject02947

  · exact reject02948

  · exact reject02949

  · exact reject02950

  · exact reject02951

end PricingIntegration.RemainingGWitnesses
