import PricingIntegration.RemainingGLayouts000

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks000

import PricingIntegration.RemainingGScopeChecks001


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00000_0 : Agrees (spec (fastBase 0 0 0) layout0000) scope0000 := by decide

private theorem bind00000_1 : Agrees (spec (fastBase 0 0 0) layout0001) scope0001 := by decide

theorem reject00000 : Rejected (base 0 0 0) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0000 layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 0) _ validLayout0000) (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 0) _ validLayout0001) (by decide) (by decide) scope0000 scope0001 (by rw [← fastBase_exact]; exact bind00000_0) (by rw [← fastBase_exact]; exact bind00000_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0000 certificate0001 (by decide)

private theorem bind00001_0 : Agrees (spec (fastBase 0 0 1) layout0002) scope0002 := by decide

theorem reject00001 : Rejected (base 0 0 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 1) _ validLayout0002) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind00001_0) certificate0002

private theorem bind00002_0 : Agrees (spec (fastBase 0 0 2) layout0002) scope0003 := by decide

theorem reject00002 : Rejected (base 0 0 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 2) _ validLayout0002) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind00002_0) certificate0003

private theorem bind00003_0 : Agrees (spec (fastBase 0 0 3) layout0002) scope0004 := by decide

theorem reject00003 : Rejected (base 0 0 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 3) _ validLayout0002) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind00003_0) certificate0004

private theorem bind00004_0 : Agrees (spec (fastBase 0 0 4) layout0002) scope0005 := by decide

theorem reject00004 : Rejected (base 0 0 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 4) _ validLayout0002) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind00004_0) certificate0005

private theorem bind00005_0 : Agrees (spec (fastBase 0 0 5) layout0003) scope0006 := by decide

private theorem bind00005_1 : Agrees (spec (fastBase 0 0 5) layout0001) scope0007 := by decide

theorem reject00005 : Rejected (base 0 0 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0003 layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 5) _ validLayout0003) (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 5) _ validLayout0001) (by decide) (by decide) scope0006 scope0007 (by rw [← fastBase_exact]; exact bind00005_0) (by rw [← fastBase_exact]; exact bind00005_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0007 (by decide)

private theorem bind00006_0 : Agrees (spec (fastBase 0 0 6) layout0002) scope0008 := by decide

theorem reject00006 : Rejected (base 0 0 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 6) _ validLayout0002) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind00006_0) certificate0008

private theorem bind00007_0 : Agrees (spec (fastBase 0 0 7) layout0002) scope0009 := by decide

theorem reject00007 : Rejected (base 0 0 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 7) _ validLayout0002) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind00007_0) certificate0009

private theorem bind00008_0 : Agrees (spec (fastBase 0 0 8) layout0002) scope0010 := by decide

theorem reject00008 : Rejected (base 0 0 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 8) _ validLayout0002) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind00008_0) certificate0010

private theorem bind00009_0 : Agrees (spec (fastBase 0 0 9) layout0002) scope0011 := by decide

theorem reject00009 : Rejected (base 0 0 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 9) _ validLayout0002) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind00009_0) certificate0011

private theorem bind00010_0 : Agrees (spec (fastBase 0 0 10) layout0002) scope0012 := by decide

theorem reject00010 : Rejected (base 0 0 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 10) _ validLayout0002) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind00010_0) certificate0012

private theorem bind00011_0 : Agrees (spec (fastBase 0 0 11) layout0002) scope0013 := by decide

theorem reject00011 : Rejected (base 0 0 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 11) _ validLayout0002) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind00011_0) certificate0013

private theorem bind00012_0 : Agrees (spec (fastBase 0 0 12) layout0002) scope0002 := by decide

theorem reject00012 : Rejected (base 0 0 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 12) _ validLayout0002) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind00012_0) certificate0002

private theorem bind00013_0 : Agrees (spec (fastBase 0 0 13) layout0002) scope0014 := by decide

theorem reject00013 : Rejected (base 0 0 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 13) _ validLayout0002) (by decide) scope0014 (by rw [← fastBase_exact]; exact bind00013_0) certificate0014

private theorem bind00014_0 : Agrees (spec (fastBase 0 0 14) layout0000) scope0000 := by decide

private theorem bind00014_1 : Agrees (spec (fastBase 0 0 14) layout0001) scope0007 := by decide

theorem reject00014 : Rejected (base 0 0 14) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0000 layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 14) _ validLayout0000) (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 14) _ validLayout0001) (by decide) (by decide) scope0000 scope0007 (by rw [← fastBase_exact]; exact bind00014_0) (by rw [← fastBase_exact]; exact bind00014_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0000 certificate0007 (by decide)

private theorem bind00015_0 : Agrees (spec (fastBase 0 0 15) layout0002) scope0009 := by decide

theorem reject00015 : Rejected (base 0 0 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 15) _ validLayout0002) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind00015_0) certificate0009

private theorem bind00016_0 : Agrees (spec (fastBase 0 0 16) layout0002) scope0015 := by decide

theorem reject00016 : Rejected (base 0 0 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 16) _ validLayout0002) (by decide) scope0015 (by rw [← fastBase_exact]; exact bind00016_0) certificate0015

private theorem bind00017_0 : Agrees (spec (fastBase 0 0 17) layout0000) scope0000 := by decide

private theorem bind00017_1 : Agrees (spec (fastBase 0 0 17) layout0001) scope0001 := by decide

theorem reject00017 : Rejected (base 0 0 17) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0000 layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 17) _ validLayout0000) (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 17) _ validLayout0001) (by decide) (by decide) scope0000 scope0001 (by rw [← fastBase_exact]; exact bind00017_0) (by rw [← fastBase_exact]; exact bind00017_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0000 certificate0001 (by decide)

private theorem bind00018_0 : Agrees (spec (fastBase 0 0 18) layout0002) scope0016 := by decide

theorem reject00018 : Rejected (base 0 0 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 18) _ validLayout0002) (by decide) scope0016 (by rw [← fastBase_exact]; exact bind00018_0) certificate0016

private theorem bind00019_0 : Agrees (spec (fastBase 0 0 19) layout0001) scope0017 := by decide

theorem reject00019 : Rejected (base 0 0 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 19) _ validLayout0001) (by decide) scope0017 (by rw [← fastBase_exact]; exact bind00019_0) certificate0017

private theorem bind00020_0 : Agrees (spec (fastBase 0 0 20) layout0002) scope0002 := by decide

theorem reject00020 : Rejected (base 0 0 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 20) _ validLayout0002) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind00020_0) certificate0002

private theorem bind00021_0 : Agrees (spec (fastBase 0 0 21) layout0002) scope0011 := by decide

theorem reject00021 : Rejected (base 0 0 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 21) _ validLayout0002) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind00021_0) certificate0011

private theorem bind00022_0 : Agrees (spec (fastBase 0 0 22) layout0000) scope0018 := by decide

theorem reject00022 : Rejected (base 0 0 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0000 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 22) _ validLayout0000) (by decide) scope0018 (by rw [← fastBase_exact]; exact bind00022_0) certificate0018

private theorem bind00023_0 : Agrees (spec (fastBase 0 0 23) layout0002) scope0019 := by decide

theorem reject00023 : Rejected (base 0 0 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 23) _ validLayout0002) (by decide) scope0019 (by rw [← fastBase_exact]; exact bind00023_0) certificate0019

private theorem bind00024_0 : Agrees (spec (fastBase 0 0 24) layout0002) scope0004 := by decide

theorem reject00024 : Rejected (base 0 0 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 24) _ validLayout0002) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind00024_0) certificate0004

private theorem bind00025_0 : Agrees (spec (fastBase 0 0 25) layout0002) scope0003 := by decide

theorem reject00025 : Rejected (base 0 0 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 25) _ validLayout0002) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind00025_0) certificate0003

private theorem bind00026_0 : Agrees (spec (fastBase 0 0 26) layout0002) scope0012 := by decide

theorem reject00026 : Rejected (base 0 0 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 26) _ validLayout0002) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind00026_0) certificate0012

private theorem bind00027_0 : Agrees (spec (fastBase 0 0 27) layout0002) scope0014 := by decide

theorem reject00027 : Rejected (base 0 0 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 27) _ validLayout0002) (by decide) scope0014 (by rw [← fastBase_exact]; exact bind00027_0) certificate0014

private theorem bind00028_0 : Agrees (spec (fastBase 0 0 28) layout0002) scope0003 := by decide

theorem reject00028 : Rejected (base 0 0 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 28) _ validLayout0002) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind00028_0) certificate0003

private theorem bind00029_0 : Agrees (spec (fastBase 0 0 29) layout0002) scope0004 := by decide

theorem reject00029 : Rejected (base 0 0 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 29) _ validLayout0002) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind00029_0) certificate0004

private theorem bind00030_0 : Agrees (spec (fastBase 0 0 30) layout0002) scope0009 := by decide

theorem reject00030 : Rejected (base 0 0 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 30) _ validLayout0002) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind00030_0) certificate0009

private theorem bind00031_0 : Agrees (spec (fastBase 0 0 31) layout0002) scope0020 := by decide

theorem reject00031 : Rejected (base 0 0 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 31) _ validLayout0002) (by decide) scope0020 (by rw [← fastBase_exact]; exact bind00031_0) certificate0020

private theorem bind00032_0 : Agrees (spec (fastBase 0 0 32) layout0002) scope0021 := by decide

theorem reject00032 : Rejected (base 0 0 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 32) _ validLayout0002) (by decide) scope0021 (by rw [← fastBase_exact]; exact bind00032_0) certificate0021

private theorem bind00033_0 : Agrees (spec (fastBase 0 0 33) layout0002) scope0022 := by decide

theorem reject00033 : Rejected (base 0 0 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 33) _ validLayout0002) (by decide) scope0022 (by rw [← fastBase_exact]; exact bind00033_0) certificate0022

private theorem bind00034_0 : Agrees (spec (fastBase 0 0 34) layout0002) scope0005 := by decide

theorem reject00034 : Rejected (base 0 0 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 34) _ validLayout0002) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind00034_0) certificate0005

private theorem bind00035_0 : Agrees (spec (fastBase 0 0 35) layout0002) scope0010 := by decide

theorem reject00035 : Rejected (base 0 0 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 35) _ validLayout0002) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind00035_0) certificate0010

private theorem bind00036_0 : Agrees (spec (fastBase 0 0 36) layout0002) scope0013 := by decide

theorem reject00036 : Rejected (base 0 0 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 36) _ validLayout0002) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind00036_0) certificate0013

private theorem bind00037_0 : Agrees (spec (fastBase 0 0 37) layout0003) scope0006 := by decide

private theorem bind00037_1 : Agrees (spec (fastBase 0 0 37) layout0001) scope0001 := by decide

theorem reject00037 : Rejected (base 0 0 37) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0003 layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 37) _ validLayout0003) (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 37) _ validLayout0001) (by decide) (by decide) scope0006 scope0001 (by rw [← fastBase_exact]; exact bind00037_0) (by rw [← fastBase_exact]; exact bind00037_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0001 (by decide)

private theorem bind00038_0 : Agrees (spec (fastBase 0 0 38) layout0003) scope0005 := by decide

theorem reject00038 : Rejected (base 0 0 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0003 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 38) _ validLayout0003) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind00038_0) certificate0005

private theorem bind00039_0 : Agrees (spec (fastBase 0 0 39) layout0003) scope0006 := by decide

private theorem bind00039_1 : Agrees (spec (fastBase 0 0 39) layout0001) scope0007 := by decide

theorem reject00039 : Rejected (base 0 0 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0003 layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 39) _ validLayout0003) (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 39) _ validLayout0001) (by decide) (by decide) scope0006 scope0007 (by rw [← fastBase_exact]; exact bind00039_0) (by rw [← fastBase_exact]; exact bind00039_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0006 certificate0007 (by decide)

private theorem bind00040_0 : Agrees (spec (fastBase 0 0 40) layout0003) scope0011 := by decide

theorem reject00040 : Rejected (base 0 0 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0003 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 40) _ validLayout0003) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind00040_0) certificate0011

private theorem bind00041_0 : Agrees (spec (fastBase 0 0 41) layout0000) scope0023 := by decide

theorem reject00041 : Rejected (base 0 0 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0000 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 41) _ validLayout0000) (by decide) scope0023 (by rw [← fastBase_exact]; exact bind00041_0) certificate0023

private theorem bind00042_0 : Agrees (spec (fastBase 0 0 42) layout0002) scope0008 := by decide

theorem reject00042 : Rejected (base 0 0 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 42) _ validLayout0002) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind00042_0) certificate0008

private theorem bind00043_0 : Agrees (spec (fastBase 0 0 43) layout0002) scope0008 := by decide

theorem reject00043 : Rejected (base 0 0 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 43) _ validLayout0002) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind00043_0) certificate0008

private theorem bind00044_0 : Agrees (spec (fastBase 0 0 44) layout0002) scope0008 := by decide

theorem reject00044 : Rejected (base 0 0 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 44) _ validLayout0002) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind00044_0) certificate0008

private theorem bind00045_0 : Agrees (spec (fastBase 0 0 45) layout0002) scope0008 := by decide

theorem reject00045 : Rejected (base 0 0 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 45) _ validLayout0002) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind00045_0) certificate0008

private theorem bind00046_0 : Agrees (spec (fastBase 0 0 46) layout0002) scope0008 := by decide

theorem reject00046 : Rejected (base 0 0 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 46) _ validLayout0002) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind00046_0) certificate0008

private theorem bind00047_0 : Agrees (spec (fastBase 0 0 47) layout0003) scope0009 := by decide

theorem reject00047 : Rejected (base 0 0 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0003 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 47) _ validLayout0003) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind00047_0) certificate0009

private theorem bind00048_0 : Agrees (spec (fastBase 0 0 48) layout0002) scope0004 := by decide

theorem reject00048 : Rejected (base 0 0 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 48) _ validLayout0002) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind00048_0) certificate0004

private theorem bind00049_0 : Agrees (spec (fastBase 0 0 49) layout0002) scope0009 := by decide

theorem reject00049 : Rejected (base 0 0 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 49) _ validLayout0002) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind00049_0) certificate0009

private theorem bind00050_0 : Agrees (spec (fastBase 0 0 50) layout0002) scope0016 := by decide

theorem reject00050 : Rejected (base 0 0 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 50) _ validLayout0002) (by decide) scope0016 (by rw [← fastBase_exact]; exact bind00050_0) certificate0016

private theorem bind00051_0 : Agrees (spec (fastBase 0 0 51) layout0001) scope0024 := by decide

theorem reject00051 : Rejected (base 0 0 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0001 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 51) _ validLayout0001) (by decide) scope0024 (by rw [← fastBase_exact]; exact bind00051_0) certificate0024

private theorem bind00052_0 : Agrees (spec (fastBase 0 0 52) layout0003) scope0015 := by decide

theorem reject00052 : Rejected (base 0 0 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0003 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 52) _ validLayout0003) (by decide) scope0015 (by rw [← fastBase_exact]; exact bind00052_0) certificate0015

private theorem bind00053_0 : Agrees (spec (fastBase 0 0 53) layout0002) scope0005 := by decide

theorem reject00053 : Rejected (base 0 0 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 53) _ validLayout0002) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind00053_0) certificate0005

private theorem bind00054_0 : Agrees (spec (fastBase 0 0 54) layout0002) scope0010 := by decide

theorem reject00054 : Rejected (base 0 0 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 54) _ validLayout0002) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind00054_0) certificate0010

private theorem bind00055_0 : Agrees (spec (fastBase 0 0 55) layout0002) scope0011 := by decide

theorem reject00055 : Rejected (base 0 0 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 55) _ validLayout0002) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind00055_0) certificate0011

private theorem bind00056_0 : Agrees (spec (fastBase 0 0 56) layout0002) scope0025 := by decide

theorem reject00056 : Rejected (base 0 0 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 56) _ validLayout0002) (by decide) scope0025 (by rw [← fastBase_exact]; exact bind00056_0) certificate0025

private theorem bind00057_0 : Agrees (spec (fastBase 0 0 57) layout0002) scope0002 := by decide

theorem reject00057 : Rejected (base 0 0 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 57) _ validLayout0002) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind00057_0) certificate0002

private theorem bind00058_0 : Agrees (spec (fastBase 0 0 58) layout0002) scope0011 := by decide

theorem reject00058 : Rejected (base 0 0 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 58) _ validLayout0002) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind00058_0) certificate0011

private theorem bind00059_0 : Agrees (spec (fastBase 0 0 59) layout0002) scope0010 := by decide

theorem reject00059 : Rejected (base 0 0 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 59) _ validLayout0002) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind00059_0) certificate0010

private theorem bind00060_0 : Agrees (spec (fastBase 0 0 60) layout0002) scope0015 := by decide

theorem reject00060 : Rejected (base 0 0 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 60) _ validLayout0002) (by decide) scope0015 (by rw [← fastBase_exact]; exact bind00060_0) certificate0015

private theorem bind00061_0 : Agrees (spec (fastBase 0 0 61) layout0002) scope0021 := by decide

theorem reject00061 : Rejected (base 0 0 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 61) _ validLayout0002) (by decide) scope0021 (by rw [← fastBase_exact]; exact bind00061_0) certificate0021

private theorem bind00062_0 : Agrees (spec (fastBase 0 0 62) layout0002) scope0003 := by decide

theorem reject00062 : Rejected (base 0 0 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 62) _ validLayout0002) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind00062_0) certificate0003

private theorem bind00063_0 : Agrees (spec (fastBase 0 0 63) layout0002) scope0012 := by decide

theorem reject00063 : Rejected (base 0 0 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 63) _ validLayout0002) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind00063_0) certificate0012

private theorem bind00064_0 : Agrees (spec (fastBase 0 0 64) layout0002) scope0020 := by decide

theorem reject00064 : Rejected (base 0 0 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 64) _ validLayout0002) (by decide) scope0020 (by rw [← fastBase_exact]; exact bind00064_0) certificate0020

private theorem bind00065_0 : Agrees (spec (fastBase 0 0 65) layout0002) scope0022 := by decide

theorem reject00065 : Rejected (base 0 0 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 65) _ validLayout0002) (by decide) scope0022 (by rw [← fastBase_exact]; exact bind00065_0) certificate0022

private theorem bind00066_0 : Agrees (spec (fastBase 0 0 66) layout0002) scope0013 := by decide

theorem reject00066 : Rejected (base 0 0 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 66) _ validLayout0002) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind00066_0) certificate0013

private theorem bind00067_0 : Agrees (spec (fastBase 0 0 67) layout0002) scope0019 := by decide

theorem reject00067 : Rejected (base 0 0 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 67) _ validLayout0002) (by decide) scope0019 (by rw [← fastBase_exact]; exact bind00067_0) certificate0019

private theorem bind00068_0 : Agrees (spec (fastBase 0 0 68) layout0002) scope0005 := by decide

theorem reject00068 : Rejected (base 0 0 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 68) _ validLayout0002) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind00068_0) certificate0005

private theorem bind00069_0 : Agrees (spec (fastBase 0 0 69) layout0002) scope0013 := by decide

theorem reject00069 : Rejected (base 0 0 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 69) _ validLayout0002) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind00069_0) certificate0013

private theorem bind00070_0 : Agrees (spec (fastBase 0 0 70) layout0002) scope0025 := by decide

theorem reject00070 : Rejected (base 0 0 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 70) _ validLayout0002) (by decide) scope0025 (by rw [← fastBase_exact]; exact bind00070_0) certificate0025

private theorem bind00071_0 : Agrees (spec (fastBase 0 0 71) layout0002) scope0012 := by decide

theorem reject00071 : Rejected (base 0 0 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0002 (layoutValid_of_refines _ _ (base_refines_skeleton 0 0 71) _ validLayout0002) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind00071_0) certificate0012

theorem allCases000 : ∀ y : Fin 72, Rejected (base 0 0 y) := by
  intro y
  fin_cases y

  · exact reject00000

  · exact reject00001

  · exact reject00002

  · exact reject00003

  · exact reject00004

  · exact reject00005

  · exact reject00006

  · exact reject00007

  · exact reject00008

  · exact reject00009

  · exact reject00010

  · exact reject00011

  · exact reject00012

  · exact reject00013

  · exact reject00014

  · exact reject00015

  · exact reject00016

  · exact reject00017

  · exact reject00018

  · exact reject00019

  · exact reject00020

  · exact reject00021

  · exact reject00022

  · exact reject00023

  · exact reject00024

  · exact reject00025

  · exact reject00026

  · exact reject00027

  · exact reject00028

  · exact reject00029

  · exact reject00030

  · exact reject00031

  · exact reject00032

  · exact reject00033

  · exact reject00034

  · exact reject00035

  · exact reject00036

  · exact reject00037

  · exact reject00038

  · exact reject00039

  · exact reject00040

  · exact reject00041

  · exact reject00042

  · exact reject00043

  · exact reject00044

  · exact reject00045

  · exact reject00046

  · exact reject00047

  · exact reject00048

  · exact reject00049

  · exact reject00050

  · exact reject00051

  · exact reject00052

  · exact reject00053

  · exact reject00054

  · exact reject00055

  · exact reject00056

  · exact reject00057

  · exact reject00058

  · exact reject00059

  · exact reject00060

  · exact reject00061

  · exact reject00062

  · exact reject00063

  · exact reject00064

  · exact reject00065

  · exact reject00066

  · exact reject00067

  · exact reject00068

  · exact reject00069

  · exact reject00070

  · exact reject00071

end PricingIntegration.RemainingGWitnesses
