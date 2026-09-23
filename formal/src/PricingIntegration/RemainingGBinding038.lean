import PricingIntegration.RemainingGLayouts018

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks007

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks026


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02736_0 : Agrees (spec (fastBase 0 38 0) layout0147) scope0108 := by decide

theorem reject02736 : Rejected (base 0 38 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 0) _ validLayout0147) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02736_0) certificate0111

private theorem bind02737_0 : Agrees (spec (fastBase 0 38 1) layout0147) scope0109 := by decide

theorem reject02737 : Rejected (base 0 38 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 1) _ validLayout0147) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind02737_0) certificate0112

private theorem bind02738_0 : Agrees (spec (fastBase 0 38 2) layout0147) scope0110 := by decide

theorem reject02738 : Rejected (base 0 38 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 2) _ validLayout0147) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind02738_0) certificate0113

private theorem bind02739_0 : Agrees (spec (fastBase 0 38 3) layout0147) scope0111 := by decide

theorem reject02739 : Rejected (base 0 38 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 3) _ validLayout0147) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind02739_0) certificate0114

private theorem bind02740_0 : Agrees (spec (fastBase 0 38 4) layout0147) scope0112 := by decide

theorem reject02740 : Rejected (base 0 38 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 4) _ validLayout0147) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind02740_0) certificate0115

private theorem bind02741_0 : Agrees (spec (fastBase 0 38 5) layout0147) scope0113 := by decide

theorem reject02741 : Rejected (base 0 38 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 5) _ validLayout0147) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02741_0) certificate0116

private theorem bind02742_0 : Agrees (spec (fastBase 0 38 6) layout0148) scope0405 := by decide

private theorem bind02742_1 : Agrees (spec (fastBase 0 38 6) layout0149) scope0115 := by decide

theorem reject02742 : Rejected (base 0 38 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0148 layout0149 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 6) _ validLayout0148) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 6) _ validLayout0149) (by decide) (by decide) scope0405 scope0115 (by rw [← fastBase_exact]; exact bind02742_0) (by rw [← fastBase_exact]; exact bind02742_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0420 certificate0421 (by decide)

private theorem bind02743_0 : Agrees (spec (fastBase 0 38 7) layout0148) scope0148 := by decide

private theorem bind02743_1 : Agrees (spec (fastBase 0 38 7) layout0149) scope0117 := by decide

theorem reject02743 : Rejected (base 0 38 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0148 layout0149 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 7) _ validLayout0148) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 7) _ validLayout0149) (by decide) (by decide) scope0148 scope0117 (by rw [← fastBase_exact]; exact bind02743_0) (by rw [← fastBase_exact]; exact bind02743_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0422 (by decide)

private theorem bind02744_0 : Agrees (spec (fastBase 0 38 8) layout0147) scope0118 := by decide

theorem reject02744 : Rejected (base 0 38 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 8) _ validLayout0147) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind02744_0) certificate0121

private theorem bind02745_0 : Agrees (spec (fastBase 0 38 9) layout0147) scope0119 := by decide

theorem reject02745 : Rejected (base 0 38 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 9) _ validLayout0147) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02745_0) certificate0122

private theorem bind02746_0 : Agrees (spec (fastBase 0 38 10) layout0147) scope0120 := by decide

theorem reject02746 : Rejected (base 0 38 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 10) _ validLayout0147) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02746_0) certificate0123

private theorem bind02747_0 : Agrees (spec (fastBase 0 38 11) layout0147) scope0121 := by decide

theorem reject02747 : Rejected (base 0 38 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 11) _ validLayout0147) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind02747_0) certificate0124

private theorem bind02748_0 : Agrees (spec (fastBase 0 38 12) layout0147) scope0122 := by decide

theorem reject02748 : Rejected (base 0 38 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 12) _ validLayout0147) (by decide) scope0122 (by rw [← fastBase_exact]; exact bind02748_0) certificate0125

private theorem bind02749_0 : Agrees (spec (fastBase 0 38 13) layout0147) scope0110 := by decide

theorem reject02749 : Rejected (base 0 38 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 13) _ validLayout0147) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind02749_0) certificate0113

private theorem bind02750_0 : Agrees (spec (fastBase 0 38 14) layout0147) scope0108 := by decide

theorem reject02750 : Rejected (base 0 38 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 14) _ validLayout0147) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02750_0) certificate0111

private theorem bind02751_0 : Agrees (spec (fastBase 0 38 15) layout0147) scope0123 := by decide

private theorem bind02751_1 : Agrees (spec (fastBase 0 38 15) layout0150) scope0124 := by decide

theorem reject02751 : Rejected (base 0 38 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0147 layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 15) _ validLayout0147) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 15) _ validLayout0150) (by decide) (by decide) scope0123 scope0124 (by rw [← fastBase_exact]; exact bind02751_0) (by rw [← fastBase_exact]; exact bind02751_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0126 certificate0127 (by decide)

private theorem bind02752_0 : Agrees (spec (fastBase 0 38 16) layout0147) scope0118 := by decide

theorem reject02752 : Rejected (base 0 38 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 16) _ validLayout0147) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind02752_0) certificate0121

private theorem bind02753_0 : Agrees (spec (fastBase 0 38 17) layout0147) scope0125 := by decide

theorem reject02753 : Rejected (base 0 38 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 17) _ validLayout0147) (by decide) scope0125 (by rw [← fastBase_exact]; exact bind02753_0) certificate0128

private theorem bind02754_0 : Agrees (spec (fastBase 0 38 18) layout0147) scope0111 := by decide

theorem reject02754 : Rejected (base 0 38 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 18) _ validLayout0147) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind02754_0) certificate0114

private theorem bind02755_0 : Agrees (spec (fastBase 0 38 19) layout0147) scope0112 := by decide

theorem reject02755 : Rejected (base 0 38 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 19) _ validLayout0147) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind02755_0) certificate0115

private theorem bind02756_0 : Agrees (spec (fastBase 0 38 20) layout0147) scope0109 := by decide

theorem reject02756 : Rejected (base 0 38 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 20) _ validLayout0147) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind02756_0) certificate0112

private theorem bind02757_0 : Agrees (spec (fastBase 0 38 21) layout0147) scope0126 := by decide

theorem reject02757 : Rejected (base 0 38 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 21) _ validLayout0147) (by decide) scope0126 (by rw [← fastBase_exact]; exact bind02757_0) certificate0129

private theorem bind02758_0 : Agrees (spec (fastBase 0 38 22) layout0147) scope0108 := by decide

theorem reject02758 : Rejected (base 0 38 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 22) _ validLayout0147) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02758_0) certificate0111

private theorem bind02759_0 : Agrees (spec (fastBase 0 38 23) layout0147) scope0112 := by decide

theorem reject02759 : Rejected (base 0 38 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 23) _ validLayout0147) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind02759_0) certificate0115

private theorem bind02760_0 : Agrees (spec (fastBase 0 38 24) layout0147) scope0125 := by decide

theorem reject02760 : Rejected (base 0 38 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 24) _ validLayout0147) (by decide) scope0125 (by rw [← fastBase_exact]; exact bind02760_0) certificate0128

private theorem bind02761_0 : Agrees (spec (fastBase 0 38 25) layout0147) scope0110 := by decide

theorem reject02761 : Rejected (base 0 38 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 25) _ validLayout0147) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind02761_0) certificate0113

private theorem bind02762_0 : Agrees (spec (fastBase 0 38 26) layout0147) scope0127 := by decide

theorem reject02762 : Rejected (base 0 38 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 26) _ validLayout0147) (by decide) scope0127 (by rw [← fastBase_exact]; exact bind02762_0) certificate0130

private theorem bind02763_0 : Agrees (spec (fastBase 0 38 27) layout0147) scope0109 := by decide

theorem reject02763 : Rejected (base 0 38 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 27) _ validLayout0147) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind02763_0) certificate0112

private theorem bind02764_0 : Agrees (spec (fastBase 0 38 28) layout0147) scope0128 := by decide

theorem reject02764 : Rejected (base 0 38 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 28) _ validLayout0147) (by decide) scope0128 (by rw [← fastBase_exact]; exact bind02764_0) certificate0131

private theorem bind02765_0 : Agrees (spec (fastBase 0 38 29) layout0147) scope0111 := by decide

theorem reject02765 : Rejected (base 0 38 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 29) _ validLayout0147) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind02765_0) certificate0114

private theorem bind02766_0 : Agrees (spec (fastBase 0 38 30) layout0147) scope0129 := by decide

private theorem bind02766_1 : Agrees (spec (fastBase 0 38 30) layout0150) scope0130 := by decide

theorem reject02766 : Rejected (base 0 38 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0147 layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 30) _ validLayout0147) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 30) _ validLayout0150) (by decide) (by decide) scope0129 scope0130 (by rw [← fastBase_exact]; exact bind02766_0) (by rw [← fastBase_exact]; exact bind02766_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0132 certificate0133 (by decide)

private theorem bind02767_0 : Agrees (spec (fastBase 0 38 31) layout0147) scope0121 := by decide

theorem reject02767 : Rejected (base 0 38 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 31) _ validLayout0147) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind02767_0) certificate0124

private theorem bind02768_0 : Agrees (spec (fastBase 0 38 32) layout0147) scope0109 := by decide

theorem reject02768 : Rejected (base 0 38 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 32) _ validLayout0147) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind02768_0) certificate0112

private theorem bind02769_0 : Agrees (spec (fastBase 0 38 33) layout0147) scope0110 := by decide

theorem reject02769 : Rejected (base 0 38 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 33) _ validLayout0147) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind02769_0) certificate0113

private theorem bind02770_0 : Agrees (spec (fastBase 0 38 34) layout0147) scope0112 := by decide

theorem reject02770 : Rejected (base 0 38 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 34) _ validLayout0147) (by decide) scope0112 (by rw [← fastBase_exact]; exact bind02770_0) certificate0115

private theorem bind02771_0 : Agrees (spec (fastBase 0 38 35) layout0147) scope0122 := by decide

theorem reject02771 : Rejected (base 0 38 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 35) _ validLayout0147) (by decide) scope0122 (by rw [← fastBase_exact]; exact bind02771_0) certificate0125

private theorem bind02772_0 : Agrees (spec (fastBase 0 38 36) layout0147) scope0128 := by decide

theorem reject02772 : Rejected (base 0 38 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 36) _ validLayout0147) (by decide) scope0128 (by rw [← fastBase_exact]; exact bind02772_0) certificate0131

private theorem bind02773_0 : Agrees (spec (fastBase 0 38 37) layout0147) scope0113 := by decide

theorem reject02773 : Rejected (base 0 38 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 37) _ validLayout0147) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02773_0) certificate0116

private theorem bind02774_0 : Agrees (spec (fastBase 0 38 38) layout0147) scope0113 := by decide

theorem reject02774 : Rejected (base 0 38 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 38) _ validLayout0147) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02774_0) certificate0116

private theorem bind02775_0 : Agrees (spec (fastBase 0 38 39) layout0147) scope0113 := by decide

theorem reject02775 : Rejected (base 0 38 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 39) _ validLayout0147) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02775_0) certificate0116

private theorem bind02776_0 : Agrees (spec (fastBase 0 38 40) layout0147) scope0113 := by decide

theorem reject02776 : Rejected (base 0 38 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 40) _ validLayout0147) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02776_0) certificate0116

private theorem bind02777_0 : Agrees (spec (fastBase 0 38 41) layout0147) scope0113 := by decide

theorem reject02777 : Rejected (base 0 38 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 41) _ validLayout0147) (by decide) scope0113 (by rw [← fastBase_exact]; exact bind02777_0) certificate0116

private theorem bind02778_0 : Agrees (spec (fastBase 0 38 42) layout0148) scope0167 := by decide

theorem reject02778 : Rejected (base 0 38 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 42) _ validLayout0148) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind02778_0) certificate0170

private theorem bind02779_0 : Agrees (spec (fastBase 0 38 43) layout0148) scope0168 := by decide

theorem reject02779 : Rejected (base 0 38 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 43) _ validLayout0148) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind02779_0) certificate0171

private theorem bind02780_0 : Agrees (spec (fastBase 0 38 44) layout0148) scope0150 := by decide

theorem reject02780 : Rejected (base 0 38 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0148 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 44) _ validLayout0148) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind02780_0) certificate0153

private theorem bind02781_0 : Agrees (spec (fastBase 0 38 45) layout0148) scope0148 := by decide

private theorem bind02781_1 : Agrees (spec (fastBase 0 38 45) layout0149) scope0115 := by decide

theorem reject02781 : Rejected (base 0 38 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0148 layout0149 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 45) _ validLayout0148) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 45) _ validLayout0149) (by decide) (by decide) scope0148 scope0115 (by rw [← fastBase_exact]; exact bind02781_0) (by rw [← fastBase_exact]; exact bind02781_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0151 certificate0421 (by decide)

private theorem bind02782_0 : Agrees (spec (fastBase 0 38 46) layout0151) scope0406 := by decide

theorem reject02782 : Rejected (base 0 38 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0151 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 46) _ validLayout0151) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind02782_0) certificate0423

private theorem bind02783_0 : Agrees (spec (fastBase 0 38 47) layout0147) scope0134 := by decide

theorem reject02783 : Rejected (base 0 38 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 47) _ validLayout0147) (by decide) scope0134 (by rw [← fastBase_exact]; exact bind02783_0) certificate0137

private theorem bind02784_0 : Agrees (spec (fastBase 0 38 48) layout0147) scope0135 := by decide

theorem reject02784 : Rejected (base 0 38 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 48) _ validLayout0147) (by decide) scope0135 (by rw [← fastBase_exact]; exact bind02784_0) certificate0138

private theorem bind02785_0 : Agrees (spec (fastBase 0 38 49) layout0148) scope0405 := by decide

private theorem bind02785_1 : Agrees (spec (fastBase 0 38 49) layout0149) scope0117 := by decide

theorem reject02785 : Rejected (base 0 38 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0148 layout0149 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 49) _ validLayout0148) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 49) _ validLayout0149) (by decide) (by decide) scope0405 scope0117 (by rw [← fastBase_exact]; exact bind02785_0) (by rw [← fastBase_exact]; exact bind02785_1) 2 7 1 6 (by decide) (by decide) 2 3 (by decide) certificate0420 certificate0422 (by decide)

private theorem bind02786_0 : Agrees (spec (fastBase 0 38 50) layout0147) scope0119 := by decide

theorem reject02786 : Rejected (base 0 38 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 50) _ validLayout0147) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02786_0) certificate0122

private theorem bind02787_0 : Agrees (spec (fastBase 0 38 51) layout0147) scope0120 := by decide

theorem reject02787 : Rejected (base 0 38 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 51) _ validLayout0147) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02787_0) certificate0123

private theorem bind02788_0 : Agrees (spec (fastBase 0 38 52) layout0147) scope0108 := by decide

theorem reject02788 : Rejected (base 0 38 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 52) _ validLayout0147) (by decide) scope0108 (by rw [← fastBase_exact]; exact bind02788_0) certificate0111

private theorem bind02789_0 : Agrees (spec (fastBase 0 38 53) layout0147) scope0127 := by decide

theorem reject02789 : Rejected (base 0 38 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 53) _ validLayout0147) (by decide) scope0127 (by rw [← fastBase_exact]; exact bind02789_0) certificate0130

private theorem bind02790_0 : Agrees (spec (fastBase 0 38 54) layout0147) scope0118 := by decide

theorem reject02790 : Rejected (base 0 38 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 54) _ validLayout0147) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind02790_0) certificate0121

private theorem bind02791_0 : Agrees (spec (fastBase 0 38 55) layout0147) scope0134 := by decide

theorem reject02791 : Rejected (base 0 38 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 55) _ validLayout0147) (by decide) scope0134 (by rw [← fastBase_exact]; exact bind02791_0) certificate0137

private theorem bind02792_0 : Agrees (spec (fastBase 0 38 56) layout0147) scope0120 := by decide

theorem reject02792 : Rejected (base 0 38 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 56) _ validLayout0147) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02792_0) certificate0123

private theorem bind02793_0 : Agrees (spec (fastBase 0 38 57) layout0147) scope0129 := by decide

private theorem bind02793_1 : Agrees (spec (fastBase 0 38 57) layout0150) scope0130 := by decide

theorem reject02793 : Rejected (base 0 38 57) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0147 layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 57) _ validLayout0147) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 57) _ validLayout0150) (by decide) (by decide) scope0129 scope0130 (by rw [← fastBase_exact]; exact bind02793_0) (by rw [← fastBase_exact]; exact bind02793_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0132 certificate0133 (by decide)

private theorem bind02794_0 : Agrees (spec (fastBase 0 38 58) layout0147) scope0119 := by decide

theorem reject02794 : Rejected (base 0 38 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 58) _ validLayout0147) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02794_0) certificate0122

private theorem bind02795_0 : Agrees (spec (fastBase 0 38 59) layout0147) scope0136 := by decide

theorem reject02795 : Rejected (base 0 38 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 59) _ validLayout0147) (by decide) scope0136 (by rw [← fastBase_exact]; exact bind02795_0) certificate0139

private theorem bind02796_0 : Agrees (spec (fastBase 0 38 60) layout0150) scope0137 := by decide

theorem reject02796 : Rejected (base 0 38 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 60) _ validLayout0150) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind02796_0) certificate0140

private theorem bind02797_0 : Agrees (spec (fastBase 0 38 61) layout0147) scope0121 := by decide

theorem reject02797 : Rejected (base 0 38 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 61) _ validLayout0147) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind02797_0) certificate0124

private theorem bind02798_0 : Agrees (spec (fastBase 0 38 62) layout0147) scope0123 := by decide

private theorem bind02798_1 : Agrees (spec (fastBase 0 38 62) layout0150) scope0124 := by decide

theorem reject02798 : Rejected (base 0 38 62) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0147 layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 62) _ validLayout0147) (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 62) _ validLayout0150) (by decide) (by decide) scope0123 scope0124 (by rw [← fastBase_exact]; exact bind02798_0) (by rw [← fastBase_exact]; exact bind02798_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0126 certificate0127 (by decide)

private theorem bind02799_0 : Agrees (spec (fastBase 0 38 63) layout0147) scope0120 := by decide

theorem reject02799 : Rejected (base 0 38 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 63) _ validLayout0147) (by decide) scope0120 (by rw [← fastBase_exact]; exact bind02799_0) certificate0123

private theorem bind02800_0 : Agrees (spec (fastBase 0 38 64) layout0150) scope0399 := by decide

theorem reject02800 : Rejected (base 0 38 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0150 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 64) _ validLayout0150) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind02800_0) certificate0412

private theorem bind02801_0 : Agrees (spec (fastBase 0 38 65) layout0147) scope0118 := by decide

theorem reject02801 : Rejected (base 0 38 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 65) _ validLayout0147) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind02801_0) certificate0121

private theorem bind02802_0 : Agrees (spec (fastBase 0 38 66) layout0147) scope0136 := by decide

theorem reject02802 : Rejected (base 0 38 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 66) _ validLayout0147) (by decide) scope0136 (by rw [← fastBase_exact]; exact bind02802_0) certificate0139

private theorem bind02803_0 : Agrees (spec (fastBase 0 38 67) layout0147) scope0111 := by decide

theorem reject02803 : Rejected (base 0 38 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 67) _ validLayout0147) (by decide) scope0111 (by rw [← fastBase_exact]; exact bind02803_0) certificate0114

private theorem bind02804_0 : Agrees (spec (fastBase 0 38 68) layout0147) scope0126 := by decide

theorem reject02804 : Rejected (base 0 38 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 68) _ validLayout0147) (by decide) scope0126 (by rw [← fastBase_exact]; exact bind02804_0) certificate0129

private theorem bind02805_0 : Agrees (spec (fastBase 0 38 69) layout0147) scope0121 := by decide

theorem reject02805 : Rejected (base 0 38 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 69) _ validLayout0147) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind02805_0) certificate0124

private theorem bind02806_0 : Agrees (spec (fastBase 0 38 70) layout0147) scope0119 := by decide

theorem reject02806 : Rejected (base 0 38 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 70) _ validLayout0147) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind02806_0) certificate0122

private theorem bind02807_0 : Agrees (spec (fastBase 0 38 71) layout0147) scope0135 := by decide

theorem reject02807 : Rejected (base 0 38 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0147 (layoutValid_of_refines _ _ (base_refines_skeleton 0 38 71) _ validLayout0147) (by decide) scope0135 (by rw [← fastBase_exact]; exact bind02807_0) certificate0138

theorem allCases038 : ∀ y : Fin 72, Rejected (base 0 38 y) := by
  intro y
  fin_cases y

  · exact reject02736

  · exact reject02737

  · exact reject02738

  · exact reject02739

  · exact reject02740

  · exact reject02741

  · exact reject02742

  · exact reject02743

  · exact reject02744

  · exact reject02745

  · exact reject02746

  · exact reject02747

  · exact reject02748

  · exact reject02749

  · exact reject02750

  · exact reject02751

  · exact reject02752

  · exact reject02753

  · exact reject02754

  · exact reject02755

  · exact reject02756

  · exact reject02757

  · exact reject02758

  · exact reject02759

  · exact reject02760

  · exact reject02761

  · exact reject02762

  · exact reject02763

  · exact reject02764

  · exact reject02765

  · exact reject02766

  · exact reject02767

  · exact reject02768

  · exact reject02769

  · exact reject02770

  · exact reject02771

  · exact reject02772

  · exact reject02773

  · exact reject02774

  · exact reject02775

  · exact reject02776

  · exact reject02777

  · exact reject02778

  · exact reject02779

  · exact reject02780

  · exact reject02781

  · exact reject02782

  · exact reject02783

  · exact reject02784

  · exact reject02785

  · exact reject02786

  · exact reject02787

  · exact reject02788

  · exact reject02789

  · exact reject02790

  · exact reject02791

  · exact reject02792

  · exact reject02793

  · exact reject02794

  · exact reject02795

  · exact reject02796

  · exact reject02797

  · exact reject02798

  · exact reject02799

  · exact reject02800

  · exact reject02801

  · exact reject02802

  · exact reject02803

  · exact reject02804

  · exact reject02805

  · exact reject02806

  · exact reject02807

end PricingIntegration.RemainingGWitnesses
