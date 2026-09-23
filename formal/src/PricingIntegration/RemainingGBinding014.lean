import PricingIntegration.RemainingGLayouts008

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks000

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks022


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind01008_0 : Agrees (spec (fastBase 0 14 0) layout0065) scope0006 := by decide

private theorem bind01008_1 : Agrees (spec (fastBase 0 14 0) layout0066) scope0001 := by decide

theorem reject01008 : Rejected (base 0 14 0) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0065 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 0) _ validLayout0065) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 0) _ validLayout0066) (by decide) (by decide) scope0006 scope0001 (by rw [← fastBase_exact]; exact bind01008_0) (by rw [← fastBase_exact]; exact bind01008_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0001 (by decide)

private theorem bind01009_0 : Agrees (spec (fastBase 0 14 1) layout0065) scope0011 := by decide

theorem reject01009 : Rejected (base 0 14 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 1) _ validLayout0065) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind01009_0) certificate0011

private theorem bind01010_0 : Agrees (spec (fastBase 0 14 2) layout0065) scope0012 := by decide

theorem reject01010 : Rejected (base 0 14 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 2) _ validLayout0065) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind01010_0) certificate0012

private theorem bind01011_0 : Agrees (spec (fastBase 0 14 3) layout0067) scope0145 := by decide

theorem reject01011 : Rejected (base 0 14 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 3) _ validLayout0067) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind01011_0) certificate0148

private theorem bind01012_0 : Agrees (spec (fastBase 0 14 4) layout0067) scope0150 := by decide

theorem reject01012 : Rejected (base 0 14 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 4) _ validLayout0067) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind01012_0) certificate0153

private theorem bind01013_0 : Agrees (spec (fastBase 0 14 5) layout0068) scope0356 := by decide

private theorem bind01013_1 : Agrees (spec (fastBase 0 14 5) layout0066) scope0007 := by decide

theorem reject01013 : Rejected (base 0 14 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0068 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 5) _ validLayout0068) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 5) _ validLayout0066) (by decide) (by decide) scope0356 scope0007 (by rw [← fastBase_exact]; exact bind01013_0) (by rw [← fastBase_exact]; exact bind01013_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0363 certificate0007 (by decide)

private theorem bind01014_0 : Agrees (spec (fastBase 0 14 6) layout0067) scope0155 := by decide

theorem reject01014 : Rejected (base 0 14 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 6) _ validLayout0067) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind01014_0) certificate0158

private theorem bind01015_0 : Agrees (spec (fastBase 0 14 7) layout0065) scope0004 := by decide

theorem reject01015 : Rejected (base 0 14 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 7) _ validLayout0065) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind01015_0) certificate0004

private theorem bind01016_0 : Agrees (spec (fastBase 0 14 8) layout0065) scope0005 := by decide

theorem reject01016 : Rejected (base 0 14 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 8) _ validLayout0065) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind01016_0) certificate0005

private theorem bind01017_0 : Agrees (spec (fastBase 0 14 9) layout0067) scope0141 := by decide

theorem reject01017 : Rejected (base 0 14 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 9) _ validLayout0067) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind01017_0) certificate0144

private theorem bind01018_0 : Agrees (spec (fastBase 0 14 10) layout0067) scope0140 := by decide

theorem reject01018 : Rejected (base 0 14 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 10) _ validLayout0067) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind01018_0) certificate0143

private theorem bind01019_0 : Agrees (spec (fastBase 0 14 11) layout0067) scope0144 := by decide

theorem reject01019 : Rejected (base 0 14 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 11) _ validLayout0067) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind01019_0) certificate0147

private theorem bind01020_0 : Agrees (spec (fastBase 0 14 12) layout0065) scope0011 := by decide

theorem reject01020 : Rejected (base 0 14 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 12) _ validLayout0065) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind01020_0) certificate0011

private theorem bind01021_0 : Agrees (spec (fastBase 0 14 13) layout0069) scope0023 := by decide

theorem reject01021 : Rejected (base 0 14 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0069 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 13) _ validLayout0069) (by decide) scope0023 (by rw [← fastBase_exact]; exact bind01021_0) certificate0023

private theorem bind01022_0 : Agrees (spec (fastBase 0 14 14) layout0065) scope0006 := by decide

private theorem bind01022_1 : Agrees (spec (fastBase 0 14 14) layout0066) scope0007 := by decide

theorem reject01022 : Rejected (base 0 14 14) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0065 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 14) _ validLayout0065) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 14) _ validLayout0066) (by decide) (by decide) scope0006 scope0007 (by rw [← fastBase_exact]; exact bind01022_0) (by rw [← fastBase_exact]; exact bind01022_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0007 (by decide)

private theorem bind01023_0 : Agrees (spec (fastBase 0 14 15) layout0065) scope0006 := by decide

private theorem bind01023_1 : Agrees (spec (fastBase 0 14 15) layout0066) scope0001 := by decide

theorem reject01023 : Rejected (base 0 14 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0065 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 15) _ validLayout0065) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 15) _ validLayout0066) (by decide) (by decide) scope0006 scope0001 (by rw [← fastBase_exact]; exact bind01023_0) (by rw [← fastBase_exact]; exact bind01023_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0001 (by decide)

private theorem bind01024_0 : Agrees (spec (fastBase 0 14 16) layout0065) scope0005 := by decide

theorem reject01024 : Rejected (base 0 14 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 16) _ validLayout0065) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind01024_0) certificate0005

private theorem bind01025_0 : Agrees (spec (fastBase 0 14 17) layout0065) scope0006 := by decide

private theorem bind01025_1 : Agrees (spec (fastBase 0 14 17) layout0066) scope0001 := by decide

theorem reject01025 : Rejected (base 0 14 17) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0065 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 17) _ validLayout0065) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 17) _ validLayout0066) (by decide) (by decide) scope0006 scope0001 (by rw [← fastBase_exact]; exact bind01025_0) (by rw [← fastBase_exact]; exact bind01025_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0001 (by decide)

private theorem bind01026_0 : Agrees (spec (fastBase 0 14 18) layout0067) scope0157 := by decide

theorem reject01026 : Rejected (base 0 14 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 18) _ validLayout0067) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind01026_0) certificate0160

private theorem bind01027_0 : Agrees (spec (fastBase 0 14 19) layout0067) scope0150 := by decide

theorem reject01027 : Rejected (base 0 14 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 19) _ validLayout0067) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind01027_0) certificate0153

private theorem bind01028_0 : Agrees (spec (fastBase 0 14 20) layout0067) scope0168 := by decide

theorem reject01028 : Rejected (base 0 14 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 20) _ validLayout0067) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind01028_0) certificate0171

private theorem bind01029_0 : Agrees (spec (fastBase 0 14 21) layout0067) scope0141 := by decide

theorem reject01029 : Rejected (base 0 14 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 21) _ validLayout0067) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind01029_0) certificate0144

private theorem bind01030_0 : Agrees (spec (fastBase 0 14 22) layout0065) scope0012 := by decide

theorem reject01030 : Rejected (base 0 14 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 22) _ validLayout0065) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind01030_0) certificate0012

private theorem bind01031_0 : Agrees (spec (fastBase 0 14 23) layout0067) scope0167 := by decide

theorem reject01031 : Rejected (base 0 14 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 23) _ validLayout0067) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind01031_0) certificate0170

private theorem bind01032_0 : Agrees (spec (fastBase 0 14 24) layout0067) scope0165 := by decide

theorem reject01032 : Rejected (base 0 14 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 24) _ validLayout0067) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind01032_0) certificate0168

private theorem bind01033_0 : Agrees (spec (fastBase 0 14 25) layout0067) scope0155 := by decide

theorem reject01033 : Rejected (base 0 14 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 25) _ validLayout0067) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind01033_0) certificate0158

private theorem bind01034_0 : Agrees (spec (fastBase 0 14 26) layout0067) scope0140 := by decide

theorem reject01034 : Rejected (base 0 14 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 26) _ validLayout0067) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind01034_0) certificate0143

private theorem bind01035_0 : Agrees (spec (fastBase 0 14 27) layout0067) scope0162 := by decide

theorem reject01035 : Rejected (base 0 14 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 27) _ validLayout0067) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind01035_0) certificate0165

private theorem bind01036_0 : Agrees (spec (fastBase 0 14 28) layout0067) scope0158 := by decide

theorem reject01036 : Rejected (base 0 14 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 28) _ validLayout0067) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind01036_0) certificate0161

private theorem bind01037_0 : Agrees (spec (fastBase 0 14 29) layout0065) scope0009 := by decide

theorem reject01037 : Rejected (base 0 14 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 29) _ validLayout0065) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind01037_0) certificate0009

private theorem bind01038_0 : Agrees (spec (fastBase 0 14 30) layout0065) scope0004 := by decide

theorem reject01038 : Rejected (base 0 14 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 30) _ validLayout0065) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind01038_0) certificate0004

private theorem bind01039_0 : Agrees (spec (fastBase 0 14 31) layout0067) scope0145 := by decide

theorem reject01039 : Rejected (base 0 14 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 31) _ validLayout0067) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind01039_0) certificate0148

private theorem bind01040_0 : Agrees (spec (fastBase 0 14 32) layout0065) scope0011 := by decide

theorem reject01040 : Rejected (base 0 14 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 32) _ validLayout0065) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind01040_0) certificate0011

private theorem bind01041_0 : Agrees (spec (fastBase 0 14 33) layout0067) scope0171 := by decide

theorem reject01041 : Rejected (base 0 14 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 33) _ validLayout0067) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind01041_0) certificate0174

private theorem bind01042_0 : Agrees (spec (fastBase 0 14 34) layout0067) scope0163 := by decide

theorem reject01042 : Rejected (base 0 14 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 34) _ validLayout0067) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind01042_0) certificate0166

private theorem bind01043_0 : Agrees (spec (fastBase 0 14 35) layout0065) scope0005 := by decide

theorem reject01043 : Rejected (base 0 14 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 35) _ validLayout0065) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind01043_0) certificate0005

private theorem bind01044_0 : Agrees (spec (fastBase 0 14 36) layout0067) scope0150 := by decide

theorem reject01044 : Rejected (base 0 14 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 36) _ validLayout0067) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind01044_0) certificate0153

private theorem bind01045_0 : Agrees (spec (fastBase 0 14 37) layout0068) scope0356 := by decide

private theorem bind01045_1 : Agrees (spec (fastBase 0 14 37) layout0066) scope0001 := by decide

theorem reject01045 : Rejected (base 0 14 37) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0068 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 37) _ validLayout0068) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 37) _ validLayout0066) (by decide) (by decide) scope0356 scope0001 (by rw [← fastBase_exact]; exact bind01045_0) (by rw [← fastBase_exact]; exact bind01045_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0363 certificate0001 (by decide)

private theorem bind01046_0 : Agrees (spec (fastBase 0 14 38) layout0067) scope0157 := by decide

theorem reject01046 : Rejected (base 0 14 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 38) _ validLayout0067) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind01046_0) certificate0160

private theorem bind01047_0 : Agrees (spec (fastBase 0 14 39) layout0067) scope0145 := by decide

theorem reject01047 : Rejected (base 0 14 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 39) _ validLayout0067) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind01047_0) certificate0148

private theorem bind01048_0 : Agrees (spec (fastBase 0 14 40) layout0067) scope0141 := by decide

theorem reject01048 : Rejected (base 0 14 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 40) _ validLayout0067) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind01048_0) certificate0144

private theorem bind01049_0 : Agrees (spec (fastBase 0 14 41) layout0067) scope0156 := by decide

theorem reject01049 : Rejected (base 0 14 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 41) _ validLayout0067) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind01049_0) certificate0159

private theorem bind01050_0 : Agrees (spec (fastBase 0 14 42) layout0067) scope0171 := by decide

theorem reject01050 : Rejected (base 0 14 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 42) _ validLayout0067) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind01050_0) certificate0174

private theorem bind01051_0 : Agrees (spec (fastBase 0 14 43) layout0065) scope0012 := by decide

theorem reject01051 : Rejected (base 0 14 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 43) _ validLayout0065) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind01051_0) certificate0012

private theorem bind01052_0 : Agrees (spec (fastBase 0 14 44) layout0065) scope0013 := by decide

theorem reject01052 : Rejected (base 0 14 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 44) _ validLayout0065) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind01052_0) certificate0013

private theorem bind01053_0 : Agrees (spec (fastBase 0 14 45) layout0067) scope0160 := by decide

theorem reject01053 : Rejected (base 0 14 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 45) _ validLayout0067) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind01053_0) certificate0163

private theorem bind01054_0 : Agrees (spec (fastBase 0 14 46) layout0067) scope0155 := by decide

theorem reject01054 : Rejected (base 0 14 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 46) _ validLayout0067) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind01054_0) certificate0158

private theorem bind01055_0 : Agrees (spec (fastBase 0 14 47) layout0065) scope0004 := by decide

theorem reject01055 : Rejected (base 0 14 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 47) _ validLayout0065) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind01055_0) certificate0004

private theorem bind01056_0 : Agrees (spec (fastBase 0 14 48) layout0067) scope0145 := by decide

theorem reject01056 : Rejected (base 0 14 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 48) _ validLayout0067) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind01056_0) certificate0148

private theorem bind01057_0 : Agrees (spec (fastBase 0 14 49) layout0067) scope0165 := by decide

theorem reject01057 : Rejected (base 0 14 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 49) _ validLayout0067) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind01057_0) certificate0168

private theorem bind01058_0 : Agrees (spec (fastBase 0 14 50) layout0067) scope0156 := by decide

theorem reject01058 : Rejected (base 0 14 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 50) _ validLayout0067) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind01058_0) certificate0159

private theorem bind01059_0 : Agrees (spec (fastBase 0 14 51) layout0067) scope0140 := by decide

theorem reject01059 : Rejected (base 0 14 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 51) _ validLayout0067) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind01059_0) certificate0143

private theorem bind01060_0 : Agrees (spec (fastBase 0 14 52) layout0069) scope0357 := by decide

theorem reject01060 : Rejected (base 0 14 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0069 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 52) _ validLayout0069) (by decide) scope0357 (by rw [← fastBase_exact]; exact bind01060_0) certificate0364

private theorem bind01061_0 : Agrees (spec (fastBase 0 14 53) layout0067) scope0150 := by decide

theorem reject01061 : Rejected (base 0 14 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 53) _ validLayout0067) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind01061_0) certificate0153

private theorem bind01062_0 : Agrees (spec (fastBase 0 14 54) layout0067) scope0155 := by decide

theorem reject01062 : Rejected (base 0 14 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 54) _ validLayout0067) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind01062_0) certificate0158

private theorem bind01063_0 : Agrees (spec (fastBase 0 14 55) layout0067) scope0168 := by decide

theorem reject01063 : Rejected (base 0 14 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 55) _ validLayout0067) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind01063_0) certificate0171

private theorem bind01064_0 : Agrees (spec (fastBase 0 14 56) layout0067) scope0167 := by decide

theorem reject01064 : Rejected (base 0 14 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 56) _ validLayout0067) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind01064_0) certificate0170

private theorem bind01065_0 : Agrees (spec (fastBase 0 14 57) layout0065) scope0002 := by decide

theorem reject01065 : Rejected (base 0 14 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 57) _ validLayout0065) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind01065_0) certificate0002

private theorem bind01066_0 : Agrees (spec (fastBase 0 14 58) layout0068) scope0356 := by decide

private theorem bind01066_1 : Agrees (spec (fastBase 0 14 58) layout0066) scope0007 := by decide

theorem reject01066 : Rejected (base 0 14 58) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0068 layout0066 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 58) _ validLayout0068) (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 58) _ validLayout0066) (by decide) (by decide) scope0356 scope0007 (by rw [← fastBase_exact]; exact bind01066_0) (by rw [← fastBase_exact]; exact bind01066_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0363 certificate0007 (by decide)

private theorem bind01067_0 : Agrees (spec (fastBase 0 14 59) layout0067) scope0163 := by decide

theorem reject01067 : Rejected (base 0 14 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 59) _ validLayout0067) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind01067_0) certificate0166

private theorem bind01068_0 : Agrees (spec (fastBase 0 14 60) layout0067) scope0162 := by decide

theorem reject01068 : Rejected (base 0 14 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 60) _ validLayout0067) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind01068_0) certificate0165

private theorem bind01069_0 : Agrees (spec (fastBase 0 14 61) layout0067) scope0141 := by decide

theorem reject01069 : Rejected (base 0 14 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 61) _ validLayout0067) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind01069_0) certificate0144

private theorem bind01070_0 : Agrees (spec (fastBase 0 14 62) layout0065) scope0003 := by decide

theorem reject01070 : Rejected (base 0 14 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 62) _ validLayout0065) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind01070_0) certificate0003

private theorem bind01071_0 : Agrees (spec (fastBase 0 14 63) layout0067) scope0158 := by decide

theorem reject01071 : Rejected (base 0 14 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 63) _ validLayout0067) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind01071_0) certificate0161

private theorem bind01072_0 : Agrees (spec (fastBase 0 14 64) layout0065) scope0004 := by decide

theorem reject01072 : Rejected (base 0 14 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0065 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 64) _ validLayout0065) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind01072_0) certificate0004

private theorem bind01073_0 : Agrees (spec (fastBase 0 14 65) layout0067) scope0160 := by decide

theorem reject01073 : Rejected (base 0 14 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 65) _ validLayout0067) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind01073_0) certificate0163

private theorem bind01074_0 : Agrees (spec (fastBase 0 14 66) layout0067) scope0140 := by decide

theorem reject01074 : Rejected (base 0 14 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 66) _ validLayout0067) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind01074_0) certificate0143

private theorem bind01075_0 : Agrees (spec (fastBase 0 14 67) layout0067) scope0144 := by decide

theorem reject01075 : Rejected (base 0 14 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 67) _ validLayout0067) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind01075_0) certificate0147

private theorem bind01076_0 : Agrees (spec (fastBase 0 14 68) layout0067) scope0144 := by decide

theorem reject01076 : Rejected (base 0 14 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 68) _ validLayout0067) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind01076_0) certificate0147

private theorem bind01077_0 : Agrees (spec (fastBase 0 14 69) layout0067) scope0144 := by decide

theorem reject01077 : Rejected (base 0 14 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 69) _ validLayout0067) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind01077_0) certificate0147

private theorem bind01078_0 : Agrees (spec (fastBase 0 14 70) layout0067) scope0144 := by decide

theorem reject01078 : Rejected (base 0 14 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 70) _ validLayout0067) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind01078_0) certificate0147

private theorem bind01079_0 : Agrees (spec (fastBase 0 14 71) layout0067) scope0144 := by decide

theorem reject01079 : Rejected (base 0 14 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0067 (layoutValid_of_refines _ _ (base_refines_skeleton 0 14 71) _ validLayout0067) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind01079_0) certificate0147

theorem allCases014 : ∀ y : Fin 72, Rejected (base 0 14 y) := by
  intro y
  fin_cases y

  · exact reject01008

  · exact reject01009

  · exact reject01010

  · exact reject01011

  · exact reject01012

  · exact reject01013

  · exact reject01014

  · exact reject01015

  · exact reject01016

  · exact reject01017

  · exact reject01018

  · exact reject01019

  · exact reject01020

  · exact reject01021

  · exact reject01022

  · exact reject01023

  · exact reject01024

  · exact reject01025

  · exact reject01026

  · exact reject01027

  · exact reject01028

  · exact reject01029

  · exact reject01030

  · exact reject01031

  · exact reject01032

  · exact reject01033

  · exact reject01034

  · exact reject01035

  · exact reject01036

  · exact reject01037

  · exact reject01038

  · exact reject01039

  · exact reject01040

  · exact reject01041

  · exact reject01042

  · exact reject01043

  · exact reject01044

  · exact reject01045

  · exact reject01046

  · exact reject01047

  · exact reject01048

  · exact reject01049

  · exact reject01050

  · exact reject01051

  · exact reject01052

  · exact reject01053

  · exact reject01054

  · exact reject01055

  · exact reject01056

  · exact reject01057

  · exact reject01058

  · exact reject01059

  · exact reject01060

  · exact reject01061

  · exact reject01062

  · exact reject01063

  · exact reject01064

  · exact reject01065

  · exact reject01066

  · exact reject01067

  · exact reject01068

  · exact reject01069

  · exact reject01070

  · exact reject01071

  · exact reject01072

  · exact reject01073

  · exact reject01074

  · exact reject01075

  · exact reject01076

  · exact reject01077

  · exact reject01078

  · exact reject01079

end PricingIntegration.RemainingGWitnesses
