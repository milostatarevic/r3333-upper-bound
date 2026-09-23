import PricingIntegration.RemainingGLayouts026

import PricingIntegration.RemainingGLayouts027

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks015

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks030


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03888_0 : Agrees (spec (fastBase 0 54 0) layout0212) scope0176 := by decide

theorem reject03888 : Rejected (base 0 54 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 0) _ validLayout0212) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03888_0) certificate0179

private theorem bind03889_0 : Agrees (spec (fastBase 0 54 1) layout0213) scope0449 := by decide

theorem reject03889 : Rejected (base 0 54 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 1) _ validLayout0213) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind03889_0) certificate0481

private theorem bind03890_0 : Agrees (spec (fastBase 0 54 2) layout0212) scope0184 := by decide

theorem reject03890 : Rejected (base 0 54 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 2) _ validLayout0212) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03890_0) certificate0187

private theorem bind03891_0 : Agrees (spec (fastBase 0 54 3) layout0212) scope0185 := by decide

theorem reject03891 : Rejected (base 0 54 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 3) _ validLayout0212) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03891_0) certificate0188

private theorem bind03892_0 : Agrees (spec (fastBase 0 54 4) layout0212) scope0186 := by decide

theorem reject03892 : Rejected (base 0 54 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 4) _ validLayout0212) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03892_0) certificate0189

private theorem bind03893_0 : Agrees (spec (fastBase 0 54 5) layout0214) scope0206 := by decide

private theorem bind03893_1 : Agrees (spec (fastBase 0 54 5) layout0213) scope0245 := by decide

theorem reject03893 : Rejected (base 0 54 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 5) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 5) _ validLayout0213) (by decide) (by decide) scope0206 scope0245 (by rw [← fastBase_exact]; exact bind03893_0) (by rw [← fastBase_exact]; exact bind03893_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0482 certificate0248 (by decide)

private theorem bind03894_0 : Agrees (spec (fastBase 0 54 6) layout0212) scope0177 := by decide

theorem reject03894 : Rejected (base 0 54 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 6) _ validLayout0212) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03894_0) certificate0180

private theorem bind03895_0 : Agrees (spec (fastBase 0 54 7) layout0213) scope0450 := by decide

theorem reject03895 : Rejected (base 0 54 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 7) _ validLayout0213) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind03895_0) certificate0483

private theorem bind03896_0 : Agrees (spec (fastBase 0 54 8) layout0213) scope0451 := by decide

theorem reject03896 : Rejected (base 0 54 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 8) _ validLayout0213) (by decide) scope0451 (by rw [← fastBase_exact]; exact bind03896_0) certificate0484

private theorem bind03897_0 : Agrees (spec (fastBase 0 54 9) layout0214) scope0182 := by decide

private theorem bind03897_1 : Agrees (spec (fastBase 0 54 9) layout0213) scope0250 := by decide

theorem reject03897 : Rejected (base 0 54 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 9) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 9) _ validLayout0213) (by decide) (by decide) scope0182 scope0250 (by rw [← fastBase_exact]; exact bind03897_0) (by rw [← fastBase_exact]; exact bind03897_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0253 (by decide)

private theorem bind03898_0 : Agrees (spec (fastBase 0 54 10) layout0212) scope0191 := by decide

theorem reject03898 : Rejected (base 0 54 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 10) _ validLayout0212) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03898_0) certificate0194

private theorem bind03899_0 : Agrees (spec (fastBase 0 54 11) layout0213) scope0264 := by decide

theorem reject03899 : Rejected (base 0 54 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 11) _ validLayout0213) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind03899_0) certificate0267

private theorem bind03900_0 : Agrees (spec (fastBase 0 54 12) layout0212) scope0194 := by decide

theorem reject03900 : Rejected (base 0 54 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 12) _ validLayout0212) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind03900_0) certificate0197

private theorem bind03901_0 : Agrees (spec (fastBase 0 54 13) layout0212) scope0176 := by decide

theorem reject03901 : Rejected (base 0 54 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 13) _ validLayout0212) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03901_0) certificate0179

private theorem bind03902_0 : Agrees (spec (fastBase 0 54 14) layout0212) scope0196 := by decide

theorem reject03902 : Rejected (base 0 54 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 14) _ validLayout0212) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind03902_0) certificate0199

private theorem bind03903_0 : Agrees (spec (fastBase 0 54 15) layout0214) scope0178 := by decide

private theorem bind03903_1 : Agrees (spec (fastBase 0 54 15) layout0213) scope0452 := by decide

theorem reject03903 : Rejected (base 0 54 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 15) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 15) _ validLayout0213) (by decide) (by decide) scope0178 scope0452 (by rw [← fastBase_exact]; exact bind03903_0) (by rw [← fastBase_exact]; exact bind03903_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0486 certificate0487 (by decide)

private theorem bind03904_0 : Agrees (spec (fastBase 0 54 16) layout0214) scope0176 := by decide

theorem reject03904 : Rejected (base 0 54 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 16) _ validLayout0214) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03904_0) certificate0179

private theorem bind03905_0 : Agrees (spec (fastBase 0 54 17) layout0212) scope0192 := by decide

theorem reject03905 : Rejected (base 0 54 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 17) _ validLayout0212) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind03905_0) certificate0195

private theorem bind03906_0 : Agrees (spec (fastBase 0 54 18) layout0212) scope0193 := by decide

theorem reject03906 : Rejected (base 0 54 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 18) _ validLayout0212) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind03906_0) certificate0196

private theorem bind03907_0 : Agrees (spec (fastBase 0 54 19) layout0212) scope0186 := by decide

theorem reject03907 : Rejected (base 0 54 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 19) _ validLayout0212) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03907_0) certificate0189

private theorem bind03908_0 : Agrees (spec (fastBase 0 54 20) layout0212) scope0177 := by decide

theorem reject03908 : Rejected (base 0 54 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 20) _ validLayout0212) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03908_0) certificate0180

private theorem bind03909_0 : Agrees (spec (fastBase 0 54 21) layout0215) scope0453 := by decide

theorem reject03909 : Rejected (base 0 54 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0215 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 21) _ validLayout0215) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind03909_0) certificate0488

private theorem bind03910_0 : Agrees (spec (fastBase 0 54 22) layout0212) scope0184 := by decide

theorem reject03910 : Rejected (base 0 54 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 22) _ validLayout0212) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03910_0) certificate0187

private theorem bind03911_0 : Agrees (spec (fastBase 0 54 23) layout0212) scope0184 := by decide

theorem reject03911 : Rejected (base 0 54 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 23) _ validLayout0212) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03911_0) certificate0187

private theorem bind03912_0 : Agrees (spec (fastBase 0 54 24) layout0212) scope0184 := by decide

theorem reject03912 : Rejected (base 0 54 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 24) _ validLayout0212) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03912_0) certificate0187

private theorem bind03913_0 : Agrees (spec (fastBase 0 54 25) layout0212) scope0184 := by decide

theorem reject03913 : Rejected (base 0 54 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 25) _ validLayout0212) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03913_0) certificate0187

private theorem bind03914_0 : Agrees (spec (fastBase 0 54 26) layout0212) scope0184 := by decide

theorem reject03914 : Rejected (base 0 54 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 26) _ validLayout0212) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind03914_0) certificate0187

private theorem bind03915_0 : Agrees (spec (fastBase 0 54 27) layout0212) scope0202 := by decide

theorem reject03915 : Rejected (base 0 54 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 27) _ validLayout0212) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind03915_0) certificate0205

private theorem bind03916_0 : Agrees (spec (fastBase 0 54 28) layout0212) scope0185 := by decide

theorem reject03916 : Rejected (base 0 54 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 28) _ validLayout0212) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03916_0) certificate0188

private theorem bind03917_0 : Agrees (spec (fastBase 0 54 29) layout0213) scope0454 := by decide

theorem reject03917 : Rejected (base 0 54 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 29) _ validLayout0213) (by decide) scope0454 (by rw [← fastBase_exact]; exact bind03917_0) certificate0489

private theorem bind03918_0 : Agrees (spec (fastBase 0 54 30) layout0212) scope0203 := by decide

theorem reject03918 : Rejected (base 0 54 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 30) _ validLayout0212) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03918_0) certificate0206

private theorem bind03919_0 : Agrees (spec (fastBase 0 54 31) layout0214) scope0185 := by decide

theorem reject03919 : Rejected (base 0 54 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 31) _ validLayout0214) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03919_0) certificate0188

private theorem bind03920_0 : Agrees (spec (fastBase 0 54 32) layout0214) scope0186 := by decide

theorem reject03920 : Rejected (base 0 54 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 32) _ validLayout0214) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03920_0) certificate0189

private theorem bind03921_0 : Agrees (spec (fastBase 0 54 33) layout0212) scope0186 := by decide

theorem reject03921 : Rejected (base 0 54 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 33) _ validLayout0212) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03921_0) certificate0189

private theorem bind03922_0 : Agrees (spec (fastBase 0 54 34) layout0212) scope0202 := by decide

theorem reject03922 : Rejected (base 0 54 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 34) _ validLayout0212) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind03922_0) certificate0205

private theorem bind03923_0 : Agrees (spec (fastBase 0 54 35) layout0212) scope0199 := by decide

theorem reject03923 : Rejected (base 0 54 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 35) _ validLayout0212) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind03923_0) certificate0202

private theorem bind03924_0 : Agrees (spec (fastBase 0 54 36) layout0216) scope0455 := by decide

theorem reject03924 : Rejected (base 0 54 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0216 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 36) _ validLayout0216) (by decide) scope0455 (by rw [← fastBase_exact]; exact bind03924_0) certificate0490

private theorem bind03925_0 : Agrees (spec (fastBase 0 54 37) layout0212) scope0201 := by decide

theorem reject03925 : Rejected (base 0 54 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 37) _ validLayout0212) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind03925_0) certificate0204

private theorem bind03926_0 : Agrees (spec (fastBase 0 54 38) layout0212) scope0207 := by decide

theorem reject03926 : Rejected (base 0 54 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 38) _ validLayout0212) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind03926_0) certificate0210

private theorem bind03927_0 : Agrees (spec (fastBase 0 54 39) layout0212) scope0185 := by decide

theorem reject03927 : Rejected (base 0 54 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 39) _ validLayout0212) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03927_0) certificate0188

private theorem bind03928_0 : Agrees (spec (fastBase 0 54 40) layout0214) scope0206 := by decide

private theorem bind03928_1 : Agrees (spec (fastBase 0 54 40) layout0213) scope0250 := by decide

theorem reject03928 : Rejected (base 0 54 40) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 40) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 40) _ validLayout0213) (by decide) (by decide) scope0206 scope0250 (by rw [← fastBase_exact]; exact bind03928_0) (by rw [← fastBase_exact]; exact bind03928_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0482 certificate0253 (by decide)

private theorem bind03929_0 : Agrees (spec (fastBase 0 54 41) layout0212) scope0191 := by decide

theorem reject03929 : Rejected (base 0 54 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 41) _ validLayout0212) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03929_0) certificate0194

private theorem bind03930_0 : Agrees (spec (fastBase 0 54 42) layout0213) scope0449 := by decide

theorem reject03930 : Rejected (base 0 54 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 42) _ validLayout0213) (by decide) scope0449 (by rw [← fastBase_exact]; exact bind03930_0) certificate0481

private theorem bind03931_0 : Agrees (spec (fastBase 0 54 43) layout0212) scope0177 := by decide

theorem reject03931 : Rejected (base 0 54 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 43) _ validLayout0212) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03931_0) certificate0180

private theorem bind03932_0 : Agrees (spec (fastBase 0 54 44) layout0213) scope0448 := by decide

theorem reject03932 : Rejected (base 0 54 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 44) _ validLayout0213) (by decide) scope0448 (by rw [← fastBase_exact]; exact bind03932_0) certificate0480

private theorem bind03933_0 : Agrees (spec (fastBase 0 54 45) layout0212) scope0194 := by decide

theorem reject03933 : Rejected (base 0 54 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 45) _ validLayout0212) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind03933_0) certificate0197

private theorem bind03934_0 : Agrees (spec (fastBase 0 54 46) layout0212) scope0199 := by decide

theorem reject03934 : Rejected (base 0 54 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 46) _ validLayout0212) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind03934_0) certificate0202

private theorem bind03935_0 : Agrees (spec (fastBase 0 54 47) layout0212) scope0176 := by decide

theorem reject03935 : Rejected (base 0 54 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 47) _ validLayout0212) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03935_0) certificate0179

private theorem bind03936_0 : Agrees (spec (fastBase 0 54 48) layout0212) scope0201 := by decide

theorem reject03936 : Rejected (base 0 54 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 48) _ validLayout0212) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind03936_0) certificate0204

private theorem bind03937_0 : Agrees (spec (fastBase 0 54 49) layout0212) scope0200 := by decide

theorem reject03937 : Rejected (base 0 54 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 49) _ validLayout0212) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind03937_0) certificate0203

private theorem bind03938_0 : Agrees (spec (fastBase 0 54 50) layout0214) scope0178 := by decide

private theorem bind03938_1 : Agrees (spec (fastBase 0 54 50) layout0213) scope0250 := by decide

theorem reject03938 : Rejected (base 0 54 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 50) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 50) _ validLayout0213) (by decide) (by decide) scope0178 scope0250 (by rw [← fastBase_exact]; exact bind03938_0) (by rw [← fastBase_exact]; exact bind03938_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0486 certificate0253 (by decide)

private theorem bind03939_0 : Agrees (spec (fastBase 0 54 51) layout0212) scope0191 := by decide

theorem reject03939 : Rejected (base 0 54 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 51) _ validLayout0212) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03939_0) certificate0194

private theorem bind03940_0 : Agrees (spec (fastBase 0 54 52) layout0212) scope0176 := by decide

theorem reject03940 : Rejected (base 0 54 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 52) _ validLayout0212) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind03940_0) certificate0179

private theorem bind03941_0 : Agrees (spec (fastBase 0 54 53) layout0212) scope0192 := by decide

theorem reject03941 : Rejected (base 0 54 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 53) _ validLayout0212) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind03941_0) certificate0195

private theorem bind03942_0 : Agrees (spec (fastBase 0 54 54) layout0212) scope0177 := by decide

theorem reject03942 : Rejected (base 0 54 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 54) _ validLayout0212) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03942_0) certificate0180

private theorem bind03943_0 : Agrees (spec (fastBase 0 54 55) layout0214) scope0182 := by decide

private theorem bind03943_1 : Agrees (spec (fastBase 0 54 55) layout0213) scope0452 := by decide

theorem reject03943 : Rejected (base 0 54 55) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 55) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 55) _ validLayout0213) (by decide) (by decide) scope0182 scope0452 (by rw [← fastBase_exact]; exact bind03943_0) (by rw [← fastBase_exact]; exact bind03943_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0487 (by decide)

private theorem bind03944_0 : Agrees (spec (fastBase 0 54 56) layout0212) scope0200 := by decide

theorem reject03944 : Rejected (base 0 54 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 56) _ validLayout0212) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind03944_0) certificate0203

private theorem bind03945_0 : Agrees (spec (fastBase 0 54 57) layout0213) scope0453 := by decide

theorem reject03945 : Rejected (base 0 54 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 57) _ validLayout0213) (by decide) scope0453 (by rw [← fastBase_exact]; exact bind03945_0) certificate0488

private theorem bind03946_0 : Agrees (spec (fastBase 0 54 58) layout0214) scope0182 := by decide

private theorem bind03946_1 : Agrees (spec (fastBase 0 54 58) layout0213) scope0245 := by decide

theorem reject03946 : Rejected (base 0 54 58) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 58) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 58) _ validLayout0213) (by decide) (by decide) scope0182 scope0245 (by rw [← fastBase_exact]; exact bind03946_0) (by rw [← fastBase_exact]; exact bind03946_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0248 (by decide)

private theorem bind03947_0 : Agrees (spec (fastBase 0 54 59) layout0213) scope0456 := by decide

theorem reject03947 : Rejected (base 0 54 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 59) _ validLayout0213) (by decide) scope0456 (by rw [← fastBase_exact]; exact bind03947_0) certificate0491

private theorem bind03948_0 : Agrees (spec (fastBase 0 54 60) layout0213) scope0450 := by decide

theorem reject03948 : Rejected (base 0 54 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 60) _ validLayout0213) (by decide) scope0450 (by rw [← fastBase_exact]; exact bind03948_0) certificate0483

private theorem bind03949_0 : Agrees (spec (fastBase 0 54 61) layout0214) scope0182 := by decide

private theorem bind03949_1 : Agrees (spec (fastBase 0 54 61) layout0213) scope0250 := by decide

theorem reject03949 : Rejected (base 0 54 61) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 61) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 61) _ validLayout0213) (by decide) (by decide) scope0182 scope0250 (by rw [← fastBase_exact]; exact bind03949_0) (by rw [← fastBase_exact]; exact bind03949_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0485 certificate0253 (by decide)

private theorem bind03950_0 : Agrees (spec (fastBase 0 54 62) layout0212) scope0191 := by decide

theorem reject03950 : Rejected (base 0 54 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 62) _ validLayout0212) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03950_0) certificate0194

private theorem bind03951_0 : Agrees (spec (fastBase 0 54 63) layout0214) scope0206 := by decide

private theorem bind03951_1 : Agrees (spec (fastBase 0 54 63) layout0213) scope0245 := by decide

theorem reject03951 : Rejected (base 0 54 63) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0214 layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 63) _ validLayout0214) (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 63) _ validLayout0213) (by decide) (by decide) scope0206 scope0245 (by rw [← fastBase_exact]; exact bind03951_0) (by rw [← fastBase_exact]; exact bind03951_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0482 certificate0248 (by decide)

private theorem bind03952_0 : Agrees (spec (fastBase 0 54 64) layout0214) scope0191 := by decide

theorem reject03952 : Rejected (base 0 54 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0214 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 64) _ validLayout0214) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind03952_0) certificate0194

private theorem bind03953_0 : Agrees (spec (fastBase 0 54 65) layout0212) scope0196 := by decide

theorem reject03953 : Rejected (base 0 54 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 65) _ validLayout0212) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind03953_0) certificate0199

private theorem bind03954_0 : Agrees (spec (fastBase 0 54 66) layout0212) scope0203 := by decide

theorem reject03954 : Rejected (base 0 54 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 66) _ validLayout0212) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind03954_0) certificate0206

private theorem bind03955_0 : Agrees (spec (fastBase 0 54 67) layout0212) scope0185 := by decide

theorem reject03955 : Rejected (base 0 54 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 67) _ validLayout0212) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind03955_0) certificate0188

private theorem bind03956_0 : Agrees (spec (fastBase 0 54 68) layout0212) scope0186 := by decide

theorem reject03956 : Rejected (base 0 54 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 68) _ validLayout0212) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind03956_0) certificate0189

private theorem bind03957_0 : Agrees (spec (fastBase 0 54 69) layout0212) scope0193 := by decide

theorem reject03957 : Rejected (base 0 54 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 69) _ validLayout0212) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind03957_0) certificate0196

private theorem bind03958_0 : Agrees (spec (fastBase 0 54 70) layout0213) scope0264 := by decide

theorem reject03958 : Rejected (base 0 54 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0213 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 70) _ validLayout0213) (by decide) scope0264 (by rw [← fastBase_exact]; exact bind03958_0) certificate0267

private theorem bind03959_0 : Agrees (spec (fastBase 0 54 71) layout0212) scope0207 := by decide

theorem reject03959 : Rejected (base 0 54 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0212 (layoutValid_of_refines _ _ (base_refines_skeleton 0 54 71) _ validLayout0212) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind03959_0) certificate0210

theorem allCases054 : ∀ y : Fin 72, Rejected (base 0 54 y) := by
  intro y
  fin_cases y

  · exact reject03888

  · exact reject03889

  · exact reject03890

  · exact reject03891

  · exact reject03892

  · exact reject03893

  · exact reject03894

  · exact reject03895

  · exact reject03896

  · exact reject03897

  · exact reject03898

  · exact reject03899

  · exact reject03900

  · exact reject03901

  · exact reject03902

  · exact reject03903

  · exact reject03904

  · exact reject03905

  · exact reject03906

  · exact reject03907

  · exact reject03908

  · exact reject03909

  · exact reject03910

  · exact reject03911

  · exact reject03912

  · exact reject03913

  · exact reject03914

  · exact reject03915

  · exact reject03916

  · exact reject03917

  · exact reject03918

  · exact reject03919

  · exact reject03920

  · exact reject03921

  · exact reject03922

  · exact reject03923

  · exact reject03924

  · exact reject03925

  · exact reject03926

  · exact reject03927

  · exact reject03928

  · exact reject03929

  · exact reject03930

  · exact reject03931

  · exact reject03932

  · exact reject03933

  · exact reject03934

  · exact reject03935

  · exact reject03936

  · exact reject03937

  · exact reject03938

  · exact reject03939

  · exact reject03940

  · exact reject03941

  · exact reject03942

  · exact reject03943

  · exact reject03944

  · exact reject03945

  · exact reject03946

  · exact reject03947

  · exact reject03948

  · exact reject03949

  · exact reject03950

  · exact reject03951

  · exact reject03952

  · exact reject03953

  · exact reject03954

  · exact reject03955

  · exact reject03956

  · exact reject03957

  · exact reject03958

  · exact reject03959

end PricingIntegration.RemainingGWitnesses
