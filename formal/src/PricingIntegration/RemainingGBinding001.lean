import PricingIntegration.RemainingGLayouts000

import PricingIntegration.RemainingGLayouts001

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks002

import PricingIntegration.RemainingGScopeChecks003


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00072_0 : Agrees (spec (fastBase 0 1 0) layout0004) scope0026 := by decide

theorem reject00072 : Rejected (base 0 1 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 0) _ validLayout0004) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind00072_0) certificate0026

private theorem bind00073_0 : Agrees (spec (fastBase 0 1 1) layout0004) scope0027 := by decide

theorem reject00073 : Rejected (base 0 1 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 1) _ validLayout0004) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind00073_0) certificate0027

private theorem bind00074_0 : Agrees (spec (fastBase 0 1 2) layout0004) scope0028 := by decide

theorem reject00074 : Rejected (base 0 1 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 2) _ validLayout0004) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind00074_0) certificate0028

private theorem bind00075_0 : Agrees (spec (fastBase 0 1 3) layout0004) scope0029 := by decide

theorem reject00075 : Rejected (base 0 1 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 3) _ validLayout0004) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind00075_0) certificate0029

private theorem bind00076_0 : Agrees (spec (fastBase 0 1 4) layout0004) scope0030 := by decide

theorem reject00076 : Rejected (base 0 1 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 4) _ validLayout0004) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind00076_0) certificate0030

private theorem bind00077_0 : Agrees (spec (fastBase 0 1 5) layout0004) scope0031 := by decide

theorem reject00077 : Rejected (base 0 1 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 5) _ validLayout0004) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind00077_0) certificate0031

private theorem bind00078_0 : Agrees (spec (fastBase 0 1 6) layout0005) scope0032 := by decide

private theorem bind00078_1 : Agrees (spec (fastBase 0 1 6) layout0006) scope0033 := by decide

theorem reject00078 : Rejected (base 0 1 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0005 layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 6) _ validLayout0005) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 6) _ validLayout0006) (by decide) (by decide) scope0032 scope0033 (by rw [← fastBase_exact]; exact bind00078_0) (by rw [← fastBase_exact]; exact bind00078_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0032 certificate0033 (by decide)

private theorem bind00079_0 : Agrees (spec (fastBase 0 1 7) layout0007) scope0034 := by decide

private theorem bind00079_1 : Agrees (spec (fastBase 0 1 7) layout0008) scope0035 := by decide

theorem reject00079 : Rejected (base 0 1 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0007 layout0008 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 7) _ validLayout0007) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 7) _ validLayout0008) (by decide) (by decide) scope0034 scope0035 (by rw [← fastBase_exact]; exact bind00079_0) (by rw [← fastBase_exact]; exact bind00079_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0034 certificate0035 (by decide)

private theorem bind00080_0 : Agrees (spec (fastBase 0 1 8) layout0004) scope0036 := by decide

theorem reject00080 : Rejected (base 0 1 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 8) _ validLayout0004) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind00080_0) certificate0036

private theorem bind00081_0 : Agrees (spec (fastBase 0 1 9) layout0004) scope0037 := by decide

theorem reject00081 : Rejected (base 0 1 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 9) _ validLayout0004) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind00081_0) certificate0037

private theorem bind00082_0 : Agrees (spec (fastBase 0 1 10) layout0004) scope0038 := by decide

theorem reject00082 : Rejected (base 0 1 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 10) _ validLayout0004) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind00082_0) certificate0038

private theorem bind00083_0 : Agrees (spec (fastBase 0 1 11) layout0004) scope0039 := by decide

theorem reject00083 : Rejected (base 0 1 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 11) _ validLayout0004) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind00083_0) certificate0039

private theorem bind00084_0 : Agrees (spec (fastBase 0 1 12) layout0004) scope0027 := by decide

theorem reject00084 : Rejected (base 0 1 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 12) _ validLayout0004) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind00084_0) certificate0027

private theorem bind00085_0 : Agrees (spec (fastBase 0 1 13) layout0004) scope0040 := by decide

theorem reject00085 : Rejected (base 0 1 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 13) _ validLayout0004) (by decide) scope0040 (by rw [← fastBase_exact]; exact bind00085_0) certificate0040

private theorem bind00086_0 : Agrees (spec (fastBase 0 1 14) layout0004) scope0026 := by decide

theorem reject00086 : Rejected (base 0 1 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 14) _ validLayout0004) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind00086_0) certificate0026

private theorem bind00087_0 : Agrees (spec (fastBase 0 1 15) layout0005) scope0026 := by decide

theorem reject00087 : Rejected (base 0 1 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 15) _ validLayout0005) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind00087_0) certificate0026

private theorem bind00088_0 : Agrees (spec (fastBase 0 1 16) layout0005) scope0041 := by decide

theorem reject00088 : Rejected (base 0 1 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 16) _ validLayout0005) (by decide) scope0041 (by rw [← fastBase_exact]; exact bind00088_0) certificate0041

private theorem bind00089_0 : Agrees (spec (fastBase 0 1 17) layout0004) scope0026 := by decide

theorem reject00089 : Rejected (base 0 1 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 17) _ validLayout0004) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind00089_0) certificate0026

private theorem bind00090_0 : Agrees (spec (fastBase 0 1 18) layout0004) scope0042 := by decide

theorem reject00090 : Rejected (base 0 1 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 18) _ validLayout0004) (by decide) scope0042 (by rw [← fastBase_exact]; exact bind00090_0) certificate0042

private theorem bind00091_0 : Agrees (spec (fastBase 0 1 19) layout0004) scope0041 := by decide

theorem reject00091 : Rejected (base 0 1 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 19) _ validLayout0004) (by decide) scope0041 (by rw [← fastBase_exact]; exact bind00091_0) certificate0041

private theorem bind00092_0 : Agrees (spec (fastBase 0 1 20) layout0004) scope0027 := by decide

theorem reject00092 : Rejected (base 0 1 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 20) _ validLayout0004) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind00092_0) certificate0027

private theorem bind00093_0 : Agrees (spec (fastBase 0 1 21) layout0004) scope0037 := by decide

theorem reject00093 : Rejected (base 0 1 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 21) _ validLayout0004) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind00093_0) certificate0037

private theorem bind00094_0 : Agrees (spec (fastBase 0 1 22) layout0004) scope0043 := by decide

theorem reject00094 : Rejected (base 0 1 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 22) _ validLayout0004) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind00094_0) certificate0043

private theorem bind00095_0 : Agrees (spec (fastBase 0 1 23) layout0004) scope0044 := by decide

theorem reject00095 : Rejected (base 0 1 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 23) _ validLayout0004) (by decide) scope0044 (by rw [← fastBase_exact]; exact bind00095_0) certificate0044

private theorem bind00096_0 : Agrees (spec (fastBase 0 1 24) layout0004) scope0029 := by decide

theorem reject00096 : Rejected (base 0 1 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 24) _ validLayout0004) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind00096_0) certificate0029

private theorem bind00097_0 : Agrees (spec (fastBase 0 1 25) layout0004) scope0028 := by decide

theorem reject00097 : Rejected (base 0 1 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 25) _ validLayout0004) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind00097_0) certificate0028

private theorem bind00098_0 : Agrees (spec (fastBase 0 1 26) layout0004) scope0038 := by decide

theorem reject00098 : Rejected (base 0 1 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 26) _ validLayout0004) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind00098_0) certificate0038

private theorem bind00099_0 : Agrees (spec (fastBase 0 1 27) layout0004) scope0040 := by decide

theorem reject00099 : Rejected (base 0 1 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 27) _ validLayout0004) (by decide) scope0040 (by rw [← fastBase_exact]; exact bind00099_0) certificate0040

private theorem bind00100_0 : Agrees (spec (fastBase 0 1 28) layout0004) scope0028 := by decide

theorem reject00100 : Rejected (base 0 1 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 28) _ validLayout0004) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind00100_0) certificate0028

private theorem bind00101_0 : Agrees (spec (fastBase 0 1 29) layout0004) scope0029 := by decide

theorem reject00101 : Rejected (base 0 1 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 29) _ validLayout0004) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind00101_0) certificate0029

private theorem bind00102_0 : Agrees (spec (fastBase 0 1 30) layout0009) scope0045 := by decide

theorem reject00102 : Rejected (base 0 1 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0009 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 30) _ validLayout0009) (by decide) scope0045 (by rw [← fastBase_exact]; exact bind00102_0) certificate0045

private theorem bind00103_0 : Agrees (spec (fastBase 0 1 31) layout0005) scope0044 := by decide

theorem reject00103 : Rejected (base 0 1 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 31) _ validLayout0005) (by decide) scope0044 (by rw [← fastBase_exact]; exact bind00103_0) certificate0044

private theorem bind00104_0 : Agrees (spec (fastBase 0 1 32) layout0004) scope0046 := by decide

theorem reject00104 : Rejected (base 0 1 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 32) _ validLayout0004) (by decide) scope0046 (by rw [← fastBase_exact]; exact bind00104_0) certificate0046

private theorem bind00105_0 : Agrees (spec (fastBase 0 1 33) layout0004) scope0047 := by decide

theorem reject00105 : Rejected (base 0 1 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 33) _ validLayout0004) (by decide) scope0047 (by rw [← fastBase_exact]; exact bind00105_0) certificate0047

private theorem bind00106_0 : Agrees (spec (fastBase 0 1 34) layout0004) scope0030 := by decide

theorem reject00106 : Rejected (base 0 1 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 34) _ validLayout0004) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind00106_0) certificate0030

private theorem bind00107_0 : Agrees (spec (fastBase 0 1 35) layout0004) scope0036 := by decide

theorem reject00107 : Rejected (base 0 1 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 35) _ validLayout0004) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind00107_0) certificate0036

private theorem bind00108_0 : Agrees (spec (fastBase 0 1 36) layout0004) scope0039 := by decide

theorem reject00108 : Rejected (base 0 1 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 36) _ validLayout0004) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind00108_0) certificate0039

private theorem bind00109_0 : Agrees (spec (fastBase 0 1 37) layout0004) scope0031 := by decide

theorem reject00109 : Rejected (base 0 1 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 37) _ validLayout0004) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind00109_0) certificate0031

private theorem bind00110_0 : Agrees (spec (fastBase 0 1 38) layout0004) scope0031 := by decide

theorem reject00110 : Rejected (base 0 1 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 38) _ validLayout0004) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind00110_0) certificate0031

private theorem bind00111_0 : Agrees (spec (fastBase 0 1 39) layout0004) scope0031 := by decide

theorem reject00111 : Rejected (base 0 1 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 39) _ validLayout0004) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind00111_0) certificate0031

private theorem bind00112_0 : Agrees (spec (fastBase 0 1 40) layout0004) scope0031 := by decide

theorem reject00112 : Rejected (base 0 1 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 40) _ validLayout0004) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind00112_0) certificate0031

private theorem bind00113_0 : Agrees (spec (fastBase 0 1 41) layout0004) scope0031 := by decide

theorem reject00113 : Rejected (base 0 1 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 41) _ validLayout0004) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind00113_0) certificate0031

private theorem bind00114_0 : Agrees (spec (fastBase 0 1 42) layout0005) scope0032 := by decide

private theorem bind00114_1 : Agrees (spec (fastBase 0 1 42) layout0006) scope0033 := by decide

theorem reject00114 : Rejected (base 0 1 42) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0005 layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 42) _ validLayout0005) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 42) _ validLayout0006) (by decide) (by decide) scope0032 scope0033 (by rw [← fastBase_exact]; exact bind00114_0) (by rw [← fastBase_exact]; exact bind00114_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0032 certificate0033 (by decide)

private theorem bind00115_0 : Agrees (spec (fastBase 0 1 43) layout0005) scope0028 := by decide

theorem reject00115 : Rejected (base 0 1 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 43) _ validLayout0005) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind00115_0) certificate0028

private theorem bind00116_0 : Agrees (spec (fastBase 0 1 44) layout0005) scope0032 := by decide

private theorem bind00116_1 : Agrees (spec (fastBase 0 1 44) layout0006) scope0033 := by decide

theorem reject00116 : Rejected (base 0 1 44) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0005 layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 44) _ validLayout0005) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 44) _ validLayout0006) (by decide) (by decide) scope0032 scope0033 (by rw [← fastBase_exact]; exact bind00116_0) (by rw [← fastBase_exact]; exact bind00116_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0032 certificate0033 (by decide)

private theorem bind00117_0 : Agrees (spec (fastBase 0 1 45) layout0005) scope0048 := by decide

private theorem bind00117_1 : Agrees (spec (fastBase 0 1 45) layout0006) scope0033 := by decide

theorem reject00117 : Rejected (base 0 1 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0005 layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 45) _ validLayout0005) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 45) _ validLayout0006) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind00117_0) (by rw [← fastBase_exact]; exact bind00117_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind00118_0 : Agrees (spec (fastBase 0 1 46) layout0006) scope0049 := by decide

theorem reject00118 : Rejected (base 0 1 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 46) _ validLayout0006) (by decide) scope0049 (by rw [← fastBase_exact]; exact bind00118_0) certificate0049

private theorem bind00119_0 : Agrees (spec (fastBase 0 1 47) layout0004) scope0026 := by decide

theorem reject00119 : Rejected (base 0 1 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 47) _ validLayout0004) (by decide) scope0026 (by rw [← fastBase_exact]; exact bind00119_0) certificate0026

private theorem bind00120_0 : Agrees (spec (fastBase 0 1 48) layout0004) scope0029 := by decide

theorem reject00120 : Rejected (base 0 1 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 48) _ validLayout0004) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind00120_0) certificate0029

private theorem bind00121_0 : Agrees (spec (fastBase 0 1 49) layout0005) scope0032 := by decide

private theorem bind00121_1 : Agrees (spec (fastBase 0 1 49) layout0006) scope0034 := by decide

theorem reject00121 : Rejected (base 0 1 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0005 layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 49) _ validLayout0005) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 49) _ validLayout0006) (by decide) (by decide) scope0032 scope0034 (by rw [← fastBase_exact]; exact bind00121_0) (by rw [← fastBase_exact]; exact bind00121_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0050 certificate0051 (by decide)

private theorem bind00122_0 : Agrees (spec (fastBase 0 1 50) layout0004) scope0042 := by decide

theorem reject00122 : Rejected (base 0 1 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 50) _ validLayout0004) (by decide) scope0042 (by rw [← fastBase_exact]; exact bind00122_0) certificate0042

private theorem bind00123_0 : Agrees (spec (fastBase 0 1 51) layout0004) scope0043 := by decide

theorem reject00123 : Rejected (base 0 1 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 51) _ validLayout0004) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind00123_0) certificate0043

private theorem bind00124_0 : Agrees (spec (fastBase 0 1 52) layout0004) scope0041 := by decide

theorem reject00124 : Rejected (base 0 1 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 52) _ validLayout0004) (by decide) scope0041 (by rw [← fastBase_exact]; exact bind00124_0) certificate0041

private theorem bind00125_0 : Agrees (spec (fastBase 0 1 53) layout0004) scope0030 := by decide

theorem reject00125 : Rejected (base 0 1 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 53) _ validLayout0004) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind00125_0) certificate0030

private theorem bind00126_0 : Agrees (spec (fastBase 0 1 54) layout0004) scope0036 := by decide

theorem reject00126 : Rejected (base 0 1 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 54) _ validLayout0004) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind00126_0) certificate0036

private theorem bind00127_0 : Agrees (spec (fastBase 0 1 55) layout0004) scope0037 := by decide

theorem reject00127 : Rejected (base 0 1 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 55) _ validLayout0004) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind00127_0) certificate0037

private theorem bind00128_0 : Agrees (spec (fastBase 0 1 56) layout0004) scope0050 := by decide

theorem reject00128 : Rejected (base 0 1 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 56) _ validLayout0004) (by decide) scope0050 (by rw [← fastBase_exact]; exact bind00128_0) certificate0052

private theorem bind00129_0 : Agrees (spec (fastBase 0 1 57) layout0004) scope0027 := by decide

theorem reject00129 : Rejected (base 0 1 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 57) _ validLayout0004) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind00129_0) certificate0027

private theorem bind00130_0 : Agrees (spec (fastBase 0 1 58) layout0004) scope0037 := by decide

theorem reject00130 : Rejected (base 0 1 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 58) _ validLayout0004) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind00130_0) certificate0037

private theorem bind00131_0 : Agrees (spec (fastBase 0 1 59) layout0004) scope0036 := by decide

theorem reject00131 : Rejected (base 0 1 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 59) _ validLayout0004) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind00131_0) certificate0036

private theorem bind00132_0 : Agrees (spec (fastBase 0 1 60) layout0005) scope0051 := by decide

private theorem bind00132_1 : Agrees (spec (fastBase 0 1 60) layout0009) scope0052 := by decide

theorem reject00132 : Rejected (base 0 1 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0005 layout0009 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 60) _ validLayout0005) (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 60) _ validLayout0009) (by decide) (by decide) scope0051 scope0052 (by rw [← fastBase_exact]; exact bind00132_0) (by rw [← fastBase_exact]; exact bind00132_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0053 certificate0054 (by decide)

private theorem bind00133_0 : Agrees (spec (fastBase 0 1 61) layout0004) scope0046 := by decide

theorem reject00133 : Rejected (base 0 1 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 61) _ validLayout0004) (by decide) scope0046 (by rw [← fastBase_exact]; exact bind00133_0) certificate0046

private theorem bind00134_0 : Agrees (spec (fastBase 0 1 62) layout0004) scope0028 := by decide

theorem reject00134 : Rejected (base 0 1 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 62) _ validLayout0004) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind00134_0) certificate0028

private theorem bind00135_0 : Agrees (spec (fastBase 0 1 63) layout0004) scope0038 := by decide

theorem reject00135 : Rejected (base 0 1 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 63) _ validLayout0004) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind00135_0) certificate0038

private theorem bind00136_0 : Agrees (spec (fastBase 0 1 64) layout0006) scope0053 := by decide

theorem reject00136 : Rejected (base 0 1 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0006 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 64) _ validLayout0006) (by decide) scope0053 (by rw [← fastBase_exact]; exact bind00136_0) certificate0055

private theorem bind00137_0 : Agrees (spec (fastBase 0 1 65) layout0004) scope0047 := by decide

theorem reject00137 : Rejected (base 0 1 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 65) _ validLayout0004) (by decide) scope0047 (by rw [← fastBase_exact]; exact bind00137_0) certificate0047

private theorem bind00138_0 : Agrees (spec (fastBase 0 1 66) layout0004) scope0039 := by decide

theorem reject00138 : Rejected (base 0 1 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 66) _ validLayout0004) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind00138_0) certificate0039

private theorem bind00139_0 : Agrees (spec (fastBase 0 1 67) layout0004) scope0044 := by decide

theorem reject00139 : Rejected (base 0 1 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 67) _ validLayout0004) (by decide) scope0044 (by rw [← fastBase_exact]; exact bind00139_0) certificate0044

private theorem bind00140_0 : Agrees (spec (fastBase 0 1 68) layout0004) scope0030 := by decide

theorem reject00140 : Rejected (base 0 1 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 68) _ validLayout0004) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind00140_0) certificate0030

private theorem bind00141_0 : Agrees (spec (fastBase 0 1 69) layout0004) scope0039 := by decide

theorem reject00141 : Rejected (base 0 1 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 69) _ validLayout0004) (by decide) scope0039 (by rw [← fastBase_exact]; exact bind00141_0) certificate0039

private theorem bind00142_0 : Agrees (spec (fastBase 0 1 70) layout0004) scope0050 := by decide

theorem reject00142 : Rejected (base 0 1 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 70) _ validLayout0004) (by decide) scope0050 (by rw [← fastBase_exact]; exact bind00142_0) certificate0052

private theorem bind00143_0 : Agrees (spec (fastBase 0 1 71) layout0004) scope0038 := by decide

theorem reject00143 : Rejected (base 0 1 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 0 1 71) _ validLayout0004) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind00143_0) certificate0038

theorem allCases001 : ∀ y : Fin 72, Rejected (base 0 1 y) := by
  intro y
  fin_cases y

  · exact reject00072

  · exact reject00073

  · exact reject00074

  · exact reject00075

  · exact reject00076

  · exact reject00077

  · exact reject00078

  · exact reject00079

  · exact reject00080

  · exact reject00081

  · exact reject00082

  · exact reject00083

  · exact reject00084

  · exact reject00085

  · exact reject00086

  · exact reject00087

  · exact reject00088

  · exact reject00089

  · exact reject00090

  · exact reject00091

  · exact reject00092

  · exact reject00093

  · exact reject00094

  · exact reject00095

  · exact reject00096

  · exact reject00097

  · exact reject00098

  · exact reject00099

  · exact reject00100

  · exact reject00101

  · exact reject00102

  · exact reject00103

  · exact reject00104

  · exact reject00105

  · exact reject00106

  · exact reject00107

  · exact reject00108

  · exact reject00109

  · exact reject00110

  · exact reject00111

  · exact reject00112

  · exact reject00113

  · exact reject00114

  · exact reject00115

  · exact reject00116

  · exact reject00117

  · exact reject00118

  · exact reject00119

  · exact reject00120

  · exact reject00121

  · exact reject00122

  · exact reject00123

  · exact reject00124

  · exact reject00125

  · exact reject00126

  · exact reject00127

  · exact reject00128

  · exact reject00129

  · exact reject00130

  · exact reject00131

  · exact reject00132

  · exact reject00133

  · exact reject00134

  · exact reject00135

  · exact reject00136

  · exact reject00137

  · exact reject00138

  · exact reject00139

  · exact reject00140

  · exact reject00141

  · exact reject00142

  · exact reject00143

end PricingIntegration.RemainingGWitnesses
