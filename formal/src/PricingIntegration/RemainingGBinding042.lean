import PricingIntegration.RemainingGLayouts020

import PricingIntegration.RemainingGLayouts021

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks002

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks027


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03024_0 : Agrees (spec (fastBase 0 42 0) layout0166) scope0032 := by decide

private theorem bind03024_1 : Agrees (spec (fastBase 0 42 0) layout0167) scope0034 := by decide

theorem reject03024 : Rejected (base 0 42 0) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0166 layout0167 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 0) _ validLayout0166) (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 0) _ validLayout0167) (by decide) (by decide) scope0032 scope0034 (by rw [← fastBase_exact]; exact bind03024_0) (by rw [← fastBase_exact]; exact bind03024_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0050 certificate0051 (by decide)

private theorem bind03025_0 : Agrees (spec (fastBase 0 42 1) layout0166) scope0036 := by decide

theorem reject03025 : Rejected (base 0 42 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 1) _ validLayout0166) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind03025_0) certificate0036

private theorem bind03026_0 : Agrees (spec (fastBase 0 42 2) layout0166) scope0027 := by decide

theorem reject03026 : Rejected (base 0 42 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 2) _ validLayout0166) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind03026_0) certificate0027

private theorem bind03027_0 : Agrees (spec (fastBase 0 42 3) layout0166) scope0037 := by decide

theorem reject03027 : Rejected (base 0 42 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 3) _ validLayout0166) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind03027_0) certificate0037

private theorem bind03028_0 : Agrees (spec (fastBase 0 42 4) layout0166) scope0026 := by decide

theorem reject03028 : Rejected (base 0 42 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 4) _ validLayout0166) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind03028_0) certificate0026

private theorem bind03029_0 : Agrees (spec (fastBase 0 42 5) layout0166) scope0048 := by decide

private theorem bind03029_1 : Agrees (spec (fastBase 0 42 5) layout0167) scope0033 := by decide

theorem reject03029 : Rejected (base 0 42 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0166 layout0167 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 5) _ validLayout0166) (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 5) _ validLayout0167) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind03029_0) (by rw [← fastBase_exact]; exact bind03029_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind03030_0 : Agrees (spec (fastBase 0 42 6) layout0166) scope0030 := by decide

theorem reject03030 : Rejected (base 0 42 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 6) _ validLayout0166) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind03030_0) certificate0030

private theorem bind03031_0 : Agrees (spec (fastBase 0 42 7) layout0166) scope0039 := by decide

theorem reject03031 : Rejected (base 0 42 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 7) _ validLayout0166) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind03031_0) certificate0039

private theorem bind03032_0 : Agrees (spec (fastBase 0 42 8) layout0166) scope0028 := by decide

theorem reject03032 : Rejected (base 0 42 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 8) _ validLayout0166) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind03032_0) certificate0028

private theorem bind03033_0 : Agrees (spec (fastBase 0 42 9) layout0166) scope0038 := by decide

theorem reject03033 : Rejected (base 0 42 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 9) _ validLayout0166) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind03033_0) certificate0038

private theorem bind03034_0 : Agrees (spec (fastBase 0 42 10) layout0166) scope0029 := by decide

theorem reject03034 : Rejected (base 0 42 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 10) _ validLayout0166) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind03034_0) certificate0029

private theorem bind03035_0 : Agrees (spec (fastBase 0 42 11) layout0166) scope0031 := by decide

theorem reject03035 : Rejected (base 0 42 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 11) _ validLayout0166) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind03035_0) certificate0031

private theorem bind03036_0 : Agrees (spec (fastBase 0 42 12) layout0168) scope0192 := by decide

theorem reject03036 : Rejected (base 0 42 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0168 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 12) _ validLayout0168) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind03036_0) certificate0195

private theorem bind03037_0 : Agrees (spec (fastBase 0 42 13) layout0168) scope0177 := by decide

theorem reject03037 : Rejected (base 0 42 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0168 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 13) _ validLayout0168) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind03037_0) certificate0180

private theorem bind03038_0 : Agrees (spec (fastBase 0 42 14) layout0166) scope0032 := by decide

private theorem bind03038_1 : Agrees (spec (fastBase 0 42 14) layout0167) scope0033 := by decide

theorem reject03038 : Rejected (base 0 42 14) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0166 layout0167 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 14) _ validLayout0166) (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 14) _ validLayout0167) (by decide) (by decide) scope0032 scope0033 (by rw [← fastBase_exact]; exact bind03038_0) (by rw [← fastBase_exact]; exact bind03038_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0032 certificate0033 (by decide)

private theorem bind03039_0 : Agrees (spec (fastBase 0 42 15) layout0168) scope0193 := by decide

theorem reject03039 : Rejected (base 0 42 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0168 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 15) _ validLayout0168) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind03039_0) certificate0196

private theorem bind03040_0 : Agrees (spec (fastBase 0 42 16) layout0166) scope0032 := by decide

private theorem bind03040_1 : Agrees (spec (fastBase 0 42 16) layout0167) scope0034 := by decide

theorem reject03040 : Rejected (base 0 42 16) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0166 layout0167 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 16) _ validLayout0166) (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 16) _ validLayout0167) (by decide) (by decide) scope0032 scope0034 (by rw [← fastBase_exact]; exact bind03040_0) (by rw [← fastBase_exact]; exact bind03040_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0050 certificate0051 (by decide)

private theorem bind03041_0 : Agrees (spec (fastBase 0 42 17) layout0166) scope0036 := by decide

theorem reject03041 : Rejected (base 0 42 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 17) _ validLayout0166) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind03041_0) certificate0036

private theorem bind03042_0 : Agrees (spec (fastBase 0 42 18) layout0166) scope0037 := by decide

theorem reject03042 : Rejected (base 0 42 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 18) _ validLayout0166) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind03042_0) certificate0037

private theorem bind03043_0 : Agrees (spec (fastBase 0 42 19) layout0166) scope0041 := by decide

theorem reject03043 : Rejected (base 0 42 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 19) _ validLayout0166) (by decide) scope0041 (by rw [← fastBase_exact]; exact bind03043_0) certificate0041

private theorem bind03044_0 : Agrees (spec (fastBase 0 42 20) layout0166) scope0030 := by decide

theorem reject03044 : Rejected (base 0 42 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 20) _ validLayout0166) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind03044_0) certificate0030

private theorem bind03045_0 : Agrees (spec (fastBase 0 42 21) layout0166) scope0050 := by decide

theorem reject03045 : Rejected (base 0 42 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 21) _ validLayout0166) (by decide) scope0050 (by rw [← fastBase_exact]; exact bind03045_0) certificate0052

private theorem bind03046_0 : Agrees (spec (fastBase 0 42 22) layout0166) scope0027 := by decide

theorem reject03046 : Rejected (base 0 42 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 22) _ validLayout0166) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind03046_0) certificate0027

private theorem bind03047_0 : Agrees (spec (fastBase 0 42 23) layout0166) scope0026 := by decide

theorem reject03047 : Rejected (base 0 42 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 23) _ validLayout0166) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind03047_0) certificate0026

private theorem bind03048_0 : Agrees (spec (fastBase 0 42 24) layout0166) scope0037 := by decide

theorem reject03048 : Rejected (base 0 42 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 24) _ validLayout0166) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind03048_0) certificate0037

private theorem bind03049_0 : Agrees (spec (fastBase 0 42 25) layout0166) scope0041 := by decide

theorem reject03049 : Rejected (base 0 42 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 25) _ validLayout0166) (by decide) scope0041 (by rw [← fastBase_exact]; exact bind03049_0) certificate0041

private theorem bind03050_0 : Agrees (spec (fastBase 0 42 26) layout0166) scope0042 := by decide

theorem reject03050 : Rejected (base 0 42 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 26) _ validLayout0166) (by decide) scope0042 (by rw [← fastBase_exact]; exact bind03050_0) certificate0042

private theorem bind03051_0 : Agrees (spec (fastBase 0 42 27) layout0166) scope0036 := by decide

theorem reject03051 : Rejected (base 0 42 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 27) _ validLayout0166) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind03051_0) certificate0036

private theorem bind03052_0 : Agrees (spec (fastBase 0 42 28) layout0166) scope0027 := by decide

theorem reject03052 : Rejected (base 0 42 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 28) _ validLayout0166) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind03052_0) certificate0027

private theorem bind03053_0 : Agrees (spec (fastBase 0 42 29) layout0169) scope0418 := by decide

theorem reject03053 : Rejected (base 0 42 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0169 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 29) _ validLayout0169) (by decide) scope0418 (by rw [← fastBase_exact]; exact bind03053_0) certificate0441

private theorem bind03054_0 : Agrees (spec (fastBase 0 42 30) layout0166) scope0046 := by decide

theorem reject03054 : Rejected (base 0 42 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 30) _ validLayout0166) (by decide) scope0046 (by rw [← fastBase_exact]; exact bind03054_0) certificate0046

private theorem bind03055_0 : Agrees (spec (fastBase 0 42 31) layout0166) scope0037 := by decide

theorem reject03055 : Rejected (base 0 42 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 31) _ validLayout0166) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind03055_0) certificate0037

private theorem bind03056_0 : Agrees (spec (fastBase 0 42 32) layout0169) scope0418 := by decide

theorem reject03056 : Rejected (base 0 42 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0169 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 32) _ validLayout0169) (by decide) scope0418 (by rw [← fastBase_exact]; exact bind03056_0) certificate0441

private theorem bind03057_0 : Agrees (spec (fastBase 0 42 33) layout0166) scope0027 := by decide

theorem reject03057 : Rejected (base 0 42 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 33) _ validLayout0166) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind03057_0) certificate0027

private theorem bind03058_0 : Agrees (spec (fastBase 0 42 34) layout0169) scope0197 := by decide

theorem reject03058 : Rejected (base 0 42 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0169 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 34) _ validLayout0169) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind03058_0) certificate0200

private theorem bind03059_0 : Agrees (spec (fastBase 0 42 35) layout0166) scope0040 := by decide

theorem reject03059 : Rejected (base 0 42 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 35) _ validLayout0166) (by decide) scope0040 (by rw [← fastBase_exact]; exact bind03059_0) certificate0040

private theorem bind03060_0 : Agrees (spec (fastBase 0 42 36) layout0166) scope0026 := by decide

theorem reject03060 : Rejected (base 0 42 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 36) _ validLayout0166) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind03060_0) certificate0026

private theorem bind03061_0 : Agrees (spec (fastBase 0 42 37) layout0167) scope0034 := by decide

private theorem bind03061_1 : Agrees (spec (fastBase 0 42 37) layout0170) scope0419 := by decide

theorem reject03061 : Rejected (base 0 42 37) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0167 layout0170 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 37) _ validLayout0167) (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 37) _ validLayout0170) (by decide) (by decide) scope0034 scope0419 (by rw [← fastBase_exact]; exact bind03061_0) (by rw [← fastBase_exact]; exact bind03061_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0034 certificate0442 (by decide)

private theorem bind03062_0 : Agrees (spec (fastBase 0 42 38) layout0166) scope0026 := by decide

theorem reject03062 : Rejected (base 0 42 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 38) _ validLayout0166) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind03062_0) certificate0026

private theorem bind03063_0 : Agrees (spec (fastBase 0 42 39) layout0166) scope0042 := by decide

theorem reject03063 : Rejected (base 0 42 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 39) _ validLayout0166) (by decide) scope0042 (by rw [← fastBase_exact]; exact bind03063_0) certificate0042

private theorem bind03064_0 : Agrees (spec (fastBase 0 42 40) layout0166) scope0043 := by decide

theorem reject03064 : Rejected (base 0 42 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 40) _ validLayout0166) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind03064_0) certificate0043

private theorem bind03065_0 : Agrees (spec (fastBase 0 42 41) layout0166) scope0029 := by decide

theorem reject03065 : Rejected (base 0 42 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 41) _ validLayout0166) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind03065_0) certificate0029

private theorem bind03066_0 : Agrees (spec (fastBase 0 42 42) layout0166) scope0036 := by decide

theorem reject03066 : Rejected (base 0 42 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 42) _ validLayout0166) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind03066_0) certificate0036

private theorem bind03067_0 : Agrees (spec (fastBase 0 42 43) layout0166) scope0046 := by decide

theorem reject03067 : Rejected (base 0 42 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 43) _ validLayout0166) (by decide) scope0046 (by rw [← fastBase_exact]; exact bind03067_0) certificate0046

private theorem bind03068_0 : Agrees (spec (fastBase 0 42 44) layout0166) scope0047 := by decide

theorem reject03068 : Rejected (base 0 42 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 44) _ validLayout0166) (by decide) scope0047 (by rw [← fastBase_exact]; exact bind03068_0) certificate0047

private theorem bind03069_0 : Agrees (spec (fastBase 0 42 45) layout0166) scope0039 := by decide

theorem reject03069 : Rejected (base 0 42 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 45) _ validLayout0166) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind03069_0) certificate0039

private theorem bind03070_0 : Agrees (spec (fastBase 0 42 46) layout0166) scope0030 := by decide

theorem reject03070 : Rejected (base 0 42 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 46) _ validLayout0166) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind03070_0) certificate0030

private theorem bind03071_0 : Agrees (spec (fastBase 0 42 47) layout0166) scope0039 := by decide

theorem reject03071 : Rejected (base 0 42 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 47) _ validLayout0166) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind03071_0) certificate0039

private theorem bind03072_0 : Agrees (spec (fastBase 0 42 48) layout0166) scope0050 := by decide

theorem reject03072 : Rejected (base 0 42 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 48) _ validLayout0166) (by decide) scope0050 (by rw [← fastBase_exact]; exact bind03072_0) certificate0052

private theorem bind03073_0 : Agrees (spec (fastBase 0 42 49) layout0166) scope0030 := by decide

theorem reject03073 : Rejected (base 0 42 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 49) _ validLayout0166) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind03073_0) certificate0030

private theorem bind03074_0 : Agrees (spec (fastBase 0 42 50) layout0166) scope0038 := by decide

theorem reject03074 : Rejected (base 0 42 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 50) _ validLayout0166) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind03074_0) certificate0038

private theorem bind03075_0 : Agrees (spec (fastBase 0 42 51) layout0166) scope0044 := by decide

theorem reject03075 : Rejected (base 0 42 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 51) _ validLayout0166) (by decide) scope0044 (by rw [← fastBase_exact]; exact bind03075_0) certificate0044

private theorem bind03076_0 : Agrees (spec (fastBase 0 42 52) layout0166) scope0028 := by decide

theorem reject03076 : Rejected (base 0 42 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 52) _ validLayout0166) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind03076_0) certificate0028

private theorem bind03077_0 : Agrees (spec (fastBase 0 42 53) layout0166) scope0043 := by decide

theorem reject03077 : Rejected (base 0 42 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 53) _ validLayout0166) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind03077_0) certificate0043

private theorem bind03078_0 : Agrees (spec (fastBase 0 42 54) layout0166) scope0044 := by decide

theorem reject03078 : Rejected (base 0 42 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 54) _ validLayout0166) (by decide) scope0044 (by rw [← fastBase_exact]; exact bind03078_0) certificate0044

private theorem bind03079_0 : Agrees (spec (fastBase 0 42 55) layout0166) scope0038 := by decide

theorem reject03079 : Rejected (base 0 42 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 55) _ validLayout0166) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind03079_0) certificate0038

private theorem bind03080_0 : Agrees (spec (fastBase 0 42 56) layout0166) scope0029 := by decide

theorem reject03080 : Rejected (base 0 42 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 56) _ validLayout0166) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind03080_0) certificate0029

private theorem bind03081_0 : Agrees (spec (fastBase 0 42 57) layout0166) scope0047 := by decide

theorem reject03081 : Rejected (base 0 42 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 57) _ validLayout0166) (by decide) scope0047 (by rw [← fastBase_exact]; exact bind03081_0) certificate0047

private theorem bind03082_0 : Agrees (spec (fastBase 0 42 58) layout0169) scope0420 := by decide

theorem reject03082 : Rejected (base 0 42 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0169 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 58) _ validLayout0169) (by decide) scope0420 (by rw [← fastBase_exact]; exact bind03082_0) certificate0443

private theorem bind03083_0 : Agrees (spec (fastBase 0 42 59) layout0166) scope0028 := by decide

theorem reject03083 : Rejected (base 0 42 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 59) _ validLayout0166) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind03083_0) certificate0028

private theorem bind03084_0 : Agrees (spec (fastBase 0 42 60) layout0166) scope0039 := by decide

theorem reject03084 : Rejected (base 0 42 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 60) _ validLayout0166) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind03084_0) certificate0039

private theorem bind03085_0 : Agrees (spec (fastBase 0 42 61) layout0166) scope0038 := by decide

theorem reject03085 : Rejected (base 0 42 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 61) _ validLayout0166) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind03085_0) certificate0038

private theorem bind03086_0 : Agrees (spec (fastBase 0 42 62) layout0166) scope0040 := by decide

theorem reject03086 : Rejected (base 0 42 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 62) _ validLayout0166) (by decide) scope0040 (by rw [← fastBase_exact]; exact bind03086_0) certificate0040

private theorem bind03087_0 : Agrees (spec (fastBase 0 42 63) layout0166) scope0048 := by decide

private theorem bind03087_1 : Agrees (spec (fastBase 0 42 63) layout0167) scope0033 := by decide

theorem reject03087 : Rejected (base 0 42 63) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0166 layout0167 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 63) _ validLayout0166) (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 63) _ validLayout0167) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind03087_0) (by rw [← fastBase_exact]; exact bind03087_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind03088_0 : Agrees (spec (fastBase 0 42 64) layout0169) scope0421 := by decide

theorem reject03088 : Rejected (base 0 42 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0169 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 64) _ validLayout0169) (by decide) scope0421 (by rw [← fastBase_exact]; exact bind03088_0) certificate0444

private theorem bind03089_0 : Agrees (spec (fastBase 0 42 65) layout0166) scope0028 := by decide

theorem reject03089 : Rejected (base 0 42 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 65) _ validLayout0166) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind03089_0) certificate0028

private theorem bind03090_0 : Agrees (spec (fastBase 0 42 66) layout0166) scope0029 := by decide

theorem reject03090 : Rejected (base 0 42 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 66) _ validLayout0166) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind03090_0) certificate0029

private theorem bind03091_0 : Agrees (spec (fastBase 0 42 67) layout0166) scope0031 := by decide

theorem reject03091 : Rejected (base 0 42 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 67) _ validLayout0166) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind03091_0) certificate0031

private theorem bind03092_0 : Agrees (spec (fastBase 0 42 68) layout0166) scope0031 := by decide

theorem reject03092 : Rejected (base 0 42 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 68) _ validLayout0166) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind03092_0) certificate0031

private theorem bind03093_0 : Agrees (spec (fastBase 0 42 69) layout0166) scope0031 := by decide

theorem reject03093 : Rejected (base 0 42 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 69) _ validLayout0166) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind03093_0) certificate0031

private theorem bind03094_0 : Agrees (spec (fastBase 0 42 70) layout0166) scope0031 := by decide

theorem reject03094 : Rejected (base 0 42 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 70) _ validLayout0166) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind03094_0) certificate0031

private theorem bind03095_0 : Agrees (spec (fastBase 0 42 71) layout0166) scope0031 := by decide

theorem reject03095 : Rejected (base 0 42 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0166 (layoutValid_of_refines _ _ (base_refines_skeleton 0 42 71) _ validLayout0166) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind03095_0) certificate0031

theorem allCases042 : ∀ y : Fin 72, Rejected (base 0 42 y) := by
  intro y
  fin_cases y

  · exact reject03024

  · exact reject03025

  · exact reject03026

  · exact reject03027

  · exact reject03028

  · exact reject03029

  · exact reject03030

  · exact reject03031

  · exact reject03032

  · exact reject03033

  · exact reject03034

  · exact reject03035

  · exact reject03036

  · exact reject03037

  · exact reject03038

  · exact reject03039

  · exact reject03040

  · exact reject03041

  · exact reject03042

  · exact reject03043

  · exact reject03044

  · exact reject03045

  · exact reject03046

  · exact reject03047

  · exact reject03048

  · exact reject03049

  · exact reject03050

  · exact reject03051

  · exact reject03052

  · exact reject03053

  · exact reject03054

  · exact reject03055

  · exact reject03056

  · exact reject03057

  · exact reject03058

  · exact reject03059

  · exact reject03060

  · exact reject03061

  · exact reject03062

  · exact reject03063

  · exact reject03064

  · exact reject03065

  · exact reject03066

  · exact reject03067

  · exact reject03068

  · exact reject03069

  · exact reject03070

  · exact reject03071

  · exact reject03072

  · exact reject03073

  · exact reject03074

  · exact reject03075

  · exact reject03076

  · exact reject03077

  · exact reject03078

  · exact reject03079

  · exact reject03080

  · exact reject03081

  · exact reject03082

  · exact reject03083

  · exact reject03084

  · exact reject03085

  · exact reject03086

  · exact reject03087

  · exact reject03088

  · exact reject03089

  · exact reject03090

  · exact reject03091

  · exact reject03092

  · exact reject03093

  · exact reject03094

  · exact reject03095

end PricingIntegration.RemainingGWitnesses
