import PricingIntegration.RemainingGLayouts004

import PricingIntegration.RemainingGLayouts005

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks024

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05688_0 : Agrees (spec (fastBase 1 7 0) layout0038) scope0209 := by decide

theorem reject05688 : Rejected (base 1 7 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 0) _ validLayout0038) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind05688_0) certificate0212

private theorem bind05689_0 : Agrees (spec (fastBase 1 7 1) layout0035) scope0195 := by decide

theorem reject05689 : Rejected (base 1 7 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 1) _ validLayout0035) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind05689_0) certificate0198

private theorem bind05690_0 : Agrees (spec (fastBase 1 7 2) layout0035) scope0197 := by decide

theorem reject05690 : Rejected (base 1 7 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 2) _ validLayout0035) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind05690_0) certificate0200

private theorem bind05691_0 : Agrees (spec (fastBase 1 7 3) layout0036) scope0381 := by decide

private theorem bind05691_1 : Agrees (spec (fastBase 1 7 3) layout0037) scope0213 := by decide

theorem reject05691 : Rejected (base 1 7 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0036 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 3) _ validLayout0036) (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 3) _ validLayout0037) (by decide) (by decide) scope0381 scope0213 (by rw [← fastBase_exact]; exact bind05691_0) (by rw [← fastBase_exact]; exact bind05691_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0390 certificate0216 (by decide)

private theorem bind05692_0 : Agrees (spec (fastBase 1 7 4) layout0038) scope0214 := by decide

theorem reject05692 : Rejected (base 1 7 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 4) _ validLayout0038) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind05692_0) certificate0217

private theorem bind05693_0 : Agrees (spec (fastBase 1 7 5) layout0038) scope0215 := by decide

private theorem bind05693_1 : Agrees (spec (fastBase 1 7 5) layout0037) scope0216 := by decide

theorem reject05693 : Rejected (base 1 7 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0038 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 5) _ validLayout0038) (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 5) _ validLayout0037) (by decide) (by decide) scope0215 scope0216 (by rw [← fastBase_exact]; exact bind05693_0) (by rw [← fastBase_exact]; exact bind05693_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0219 (by decide)

private theorem bind05694_0 : Agrees (spec (fastBase 1 7 6) layout0035) scope0553 := by decide

theorem reject05694 : Rejected (base 1 7 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 6) _ validLayout0035) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind05694_0) certificate0596

private theorem bind05695_0 : Agrees (spec (fastBase 1 7 7) layout0035) scope0423 := by decide

theorem reject05695 : Rejected (base 1 7 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 7) _ validLayout0035) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind05695_0) certificate0447

private theorem bind05696_0 : Agrees (spec (fastBase 1 7 8) layout0035) scope0205 := by decide

theorem reject05696 : Rejected (base 1 7 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 8) _ validLayout0035) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind05696_0) certificate0208

private theorem bind05697_0 : Agrees (spec (fastBase 1 7 9) layout0038) scope0220 := by decide

theorem reject05697 : Rejected (base 1 7 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 9) _ validLayout0038) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind05697_0) certificate0223

private theorem bind05698_0 : Agrees (spec (fastBase 1 7 10) layout0038) scope0221 := by decide

theorem reject05698 : Rejected (base 1 7 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 10) _ validLayout0038) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind05698_0) certificate0224

private theorem bind05699_0 : Agrees (spec (fastBase 1 7 11) layout0035) scope0208 := by decide

theorem reject05699 : Rejected (base 1 7 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 11) _ validLayout0035) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind05699_0) certificate0211

private theorem bind05700_0 : Agrees (spec (fastBase 1 7 12) layout0035) scope0554 := by decide

theorem reject05700 : Rejected (base 1 7 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 12) _ validLayout0035) (by decide) scope0554 (by rw [← fastBase_exact]; exact bind05700_0) certificate0597

private theorem bind05701_0 : Agrees (spec (fastBase 1 7 13) layout0035) scope0197 := by decide

theorem reject05701 : Rejected (base 1 7 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 13) _ validLayout0035) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind05701_0) certificate0200

private theorem bind05702_0 : Agrees (spec (fastBase 1 7 14) layout0038) scope0209 := by decide

theorem reject05702 : Rejected (base 1 7 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 14) _ validLayout0038) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind05702_0) certificate0212

private theorem bind05703_0 : Agrees (spec (fastBase 1 7 15) layout0035) scope0420 := by decide

theorem reject05703 : Rejected (base 1 7 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 15) _ validLayout0035) (by decide) scope0420 (by rw [← fastBase_exact]; exact bind05703_0) certificate0443

private theorem bind05704_0 : Agrees (spec (fastBase 1 7 16) layout0035) scope0205 := by decide

theorem reject05704 : Rejected (base 1 7 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 16) _ validLayout0035) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind05704_0) certificate0208

private theorem bind05705_0 : Agrees (spec (fastBase 1 7 17) layout0035) scope0418 := by decide

theorem reject05705 : Rejected (base 1 7 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 17) _ validLayout0035) (by decide) scope0418 (by rw [← fastBase_exact]; exact bind05705_0) certificate0441

private theorem bind05706_0 : Agrees (spec (fastBase 1 7 18) layout0038) scope0210 := by decide

theorem reject05706 : Rejected (base 1 7 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 18) _ validLayout0038) (by decide) scope0210 (by rw [← fastBase_exact]; exact bind05706_0) certificate0213

private theorem bind05707_0 : Agrees (spec (fastBase 1 7 19) layout0038) scope0214 := by decide

theorem reject05707 : Rejected (base 1 7 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 19) _ validLayout0038) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind05707_0) certificate0217

private theorem bind05708_0 : Agrees (spec (fastBase 1 7 20) layout0035) scope0195 := by decide

theorem reject05708 : Rejected (base 1 7 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 20) _ validLayout0035) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind05708_0) certificate0198

private theorem bind05709_0 : Agrees (spec (fastBase 1 7 21) layout0035) scope0555 := by decide

theorem reject05709 : Rejected (base 1 7 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 21) _ validLayout0035) (by decide) scope0555 (by rw [← fastBase_exact]; exact bind05709_0) certificate0598

private theorem bind05710_0 : Agrees (spec (fastBase 1 7 22) layout0038) scope0211 := by decide

theorem reject05710 : Rejected (base 1 7 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 22) _ validLayout0038) (by decide) scope0211 (by rw [← fastBase_exact]; exact bind05710_0) certificate0214

private theorem bind05711_0 : Agrees (spec (fastBase 1 7 23) layout0038) scope0214 := by decide

theorem reject05711 : Rejected (base 1 7 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 23) _ validLayout0038) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind05711_0) certificate0217

private theorem bind05712_0 : Agrees (spec (fastBase 1 7 24) layout0035) scope0418 := by decide

theorem reject05712 : Rejected (base 1 7 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 24) _ validLayout0035) (by decide) scope0418 (by rw [← fastBase_exact]; exact bind05712_0) certificate0441

private theorem bind05713_0 : Agrees (spec (fastBase 1 7 25) layout0035) scope0197 := by decide

theorem reject05713 : Rejected (base 1 7 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 25) _ validLayout0035) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind05713_0) certificate0200

private theorem bind05714_0 : Agrees (spec (fastBase 1 7 26) layout0035) scope0556 := by decide

theorem reject05714 : Rejected (base 1 7 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 26) _ validLayout0035) (by decide) scope0556 (by rw [← fastBase_exact]; exact bind05714_0) certificate0599

private theorem bind05715_0 : Agrees (spec (fastBase 1 7 27) layout0035) scope0195 := by decide

theorem reject05715 : Rejected (base 1 7 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 27) _ validLayout0035) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind05715_0) certificate0198

private theorem bind05716_0 : Agrees (spec (fastBase 1 7 28) layout0035) scope0557 := by decide

theorem reject05716 : Rejected (base 1 7 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 28) _ validLayout0035) (by decide) scope0557 (by rw [← fastBase_exact]; exact bind05716_0) certificate0600

private theorem bind05717_0 : Agrees (spec (fastBase 1 7 29) layout0036) scope0381 := by decide

private theorem bind05717_1 : Agrees (spec (fastBase 1 7 29) layout0037) scope0216 := by decide

theorem reject05717 : Rejected (base 1 7 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0036 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 29) _ validLayout0036) (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 29) _ validLayout0037) (by decide) (by decide) scope0381 scope0216 (by rw [← fastBase_exact]; exact bind05717_0) (by rw [← fastBase_exact]; exact bind05717_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0390 certificate0219 (by decide)

private theorem bind05718_0 : Agrees (spec (fastBase 1 7 30) layout0035) scope0558 := by decide

theorem reject05718 : Rejected (base 1 7 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 30) _ validLayout0035) (by decide) scope0558 (by rw [← fastBase_exact]; exact bind05718_0) certificate0601

private theorem bind05719_0 : Agrees (spec (fastBase 1 7 31) layout0035) scope0208 := by decide

theorem reject05719 : Rejected (base 1 7 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 31) _ validLayout0035) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind05719_0) certificate0211

private theorem bind05720_0 : Agrees (spec (fastBase 1 7 32) layout0035) scope0195 := by decide

theorem reject05720 : Rejected (base 1 7 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 32) _ validLayout0035) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind05720_0) certificate0198

private theorem bind05721_0 : Agrees (spec (fastBase 1 7 33) layout0035) scope0197 := by decide

theorem reject05721 : Rejected (base 1 7 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 33) _ validLayout0035) (by decide) scope0197 (by rw [← fastBase_exact]; exact bind05721_0) certificate0200

private theorem bind05722_0 : Agrees (spec (fastBase 1 7 34) layout0038) scope0214 := by decide

theorem reject05722 : Rejected (base 1 7 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 34) _ validLayout0038) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind05722_0) certificate0217

private theorem bind05723_0 : Agrees (spec (fastBase 1 7 35) layout0035) scope0554 := by decide

theorem reject05723 : Rejected (base 1 7 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 35) _ validLayout0035) (by decide) scope0554 (by rw [← fastBase_exact]; exact bind05723_0) certificate0597

private theorem bind05724_0 : Agrees (spec (fastBase 1 7 36) layout0035) scope0557 := by decide

theorem reject05724 : Rejected (base 1 7 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 36) _ validLayout0035) (by decide) scope0557 (by rw [← fastBase_exact]; exact bind05724_0) certificate0600

private theorem bind05725_0 : Agrees (spec (fastBase 1 7 37) layout0040) scope0232 := by decide

theorem reject05725 : Rejected (base 1 7 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 37) _ validLayout0040) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind05725_0) certificate0235

private theorem bind05726_0 : Agrees (spec (fastBase 1 7 38) layout0040) scope0233 := by decide

theorem reject05726 : Rejected (base 1 7 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 38) _ validLayout0040) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind05726_0) certificate0236

private theorem bind05727_0 : Agrees (spec (fastBase 1 7 39) layout0038) scope0215 := by decide

private theorem bind05727_1 : Agrees (spec (fastBase 1 7 39) layout0037) scope0213 := by decide

theorem reject05727 : Rejected (base 1 7 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0038 layout0037 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 39) _ validLayout0038) (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 39) _ validLayout0037) (by decide) (by decide) scope0215 scope0213 (by rw [← fastBase_exact]; exact bind05727_0) (by rw [← fastBase_exact]; exact bind05727_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0218 certificate0216 (by decide)

private theorem bind05728_0 : Agrees (spec (fastBase 1 7 40) layout0038) scope0220 := by decide

theorem reject05728 : Rejected (base 1 7 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 40) _ validLayout0038) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind05728_0) certificate0223

private theorem bind05729_0 : Agrees (spec (fastBase 1 7 41) layout0038) scope0221 := by decide

theorem reject05729 : Rejected (base 1 7 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 41) _ validLayout0038) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind05729_0) certificate0224

private theorem bind05730_0 : Agrees (spec (fastBase 1 7 42) layout0035) scope0553 := by decide

theorem reject05730 : Rejected (base 1 7 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 42) _ validLayout0035) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind05730_0) certificate0596

private theorem bind05731_0 : Agrees (spec (fastBase 1 7 43) layout0035) scope0553 := by decide

theorem reject05731 : Rejected (base 1 7 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 43) _ validLayout0035) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind05731_0) certificate0596

private theorem bind05732_0 : Agrees (spec (fastBase 1 7 44) layout0035) scope0553 := by decide

theorem reject05732 : Rejected (base 1 7 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 44) _ validLayout0035) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind05732_0) certificate0596

private theorem bind05733_0 : Agrees (spec (fastBase 1 7 45) layout0035) scope0553 := by decide

theorem reject05733 : Rejected (base 1 7 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 45) _ validLayout0035) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind05733_0) certificate0596

private theorem bind05734_0 : Agrees (spec (fastBase 1 7 46) layout0035) scope0553 := by decide

theorem reject05734 : Rejected (base 1 7 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 46) _ validLayout0035) (by decide) scope0553 (by rw [← fastBase_exact]; exact bind05734_0) certificate0596

private theorem bind05735_0 : Agrees (spec (fastBase 1 7 47) layout0035) scope0421 := by decide

theorem reject05735 : Rejected (base 1 7 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 47) _ validLayout0035) (by decide) scope0421 (by rw [← fastBase_exact]; exact bind05735_0) certificate0444

private theorem bind05736_0 : Agrees (spec (fastBase 1 7 48) layout0035) scope0559 := by decide

theorem reject05736 : Rejected (base 1 7 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 48) _ validLayout0035) (by decide) scope0559 (by rw [← fastBase_exact]; exact bind05736_0) certificate0602

private theorem bind05737_0 : Agrees (spec (fastBase 1 7 49) layout0035) scope0423 := by decide

theorem reject05737 : Rejected (base 1 7 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 49) _ validLayout0035) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind05737_0) certificate0447

private theorem bind05738_0 : Agrees (spec (fastBase 1 7 50) layout0038) scope0220 := by decide

theorem reject05738 : Rejected (base 1 7 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 50) _ validLayout0038) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind05738_0) certificate0223

private theorem bind05739_0 : Agrees (spec (fastBase 1 7 51) layout0038) scope0221 := by decide

theorem reject05739 : Rejected (base 1 7 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 51) _ validLayout0038) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind05739_0) certificate0224

private theorem bind05740_0 : Agrees (spec (fastBase 1 7 52) layout0038) scope0209 := by decide

theorem reject05740 : Rejected (base 1 7 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 52) _ validLayout0038) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind05740_0) certificate0212

private theorem bind05741_0 : Agrees (spec (fastBase 1 7 53) layout0035) scope0556 := by decide

theorem reject05741 : Rejected (base 1 7 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 53) _ validLayout0035) (by decide) scope0556 (by rw [← fastBase_exact]; exact bind05741_0) certificate0599

private theorem bind05742_0 : Agrees (spec (fastBase 1 7 54) layout0035) scope0205 := by decide

theorem reject05742 : Rejected (base 1 7 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 54) _ validLayout0035) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind05742_0) certificate0208

private theorem bind05743_0 : Agrees (spec (fastBase 1 7 55) layout0035) scope0421 := by decide

theorem reject05743 : Rejected (base 1 7 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 55) _ validLayout0035) (by decide) scope0421 (by rw [← fastBase_exact]; exact bind05743_0) certificate0444

private theorem bind05744_0 : Agrees (spec (fastBase 1 7 56) layout0038) scope0219 := by decide

theorem reject05744 : Rejected (base 1 7 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 56) _ validLayout0038) (by decide) scope0219 (by rw [← fastBase_exact]; exact bind05744_0) certificate0222

private theorem bind05745_0 : Agrees (spec (fastBase 1 7 57) layout0035) scope0558 := by decide

theorem reject05745 : Rejected (base 1 7 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 57) _ validLayout0035) (by decide) scope0558 (by rw [← fastBase_exact]; exact bind05745_0) certificate0601

private theorem bind05746_0 : Agrees (spec (fastBase 1 7 58) layout0040) scope0433 := by decide

theorem reject05746 : Rejected (base 1 7 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 58) _ validLayout0040) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind05746_0) certificate0460

private theorem bind05747_0 : Agrees (spec (fastBase 1 7 59) layout0035) scope0424 := by decide

theorem reject05747 : Rejected (base 1 7 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 59) _ validLayout0035) (by decide) scope0424 (by rw [← fastBase_exact]; exact bind05747_0) certificate0448

private theorem bind05748_0 : Agrees (spec (fastBase 1 7 60) layout0035) scope0423 := by decide

theorem reject05748 : Rejected (base 1 7 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 60) _ validLayout0035) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind05748_0) certificate0447

private theorem bind05749_0 : Agrees (spec (fastBase 1 7 61) layout0035) scope0208 := by decide

theorem reject05749 : Rejected (base 1 7 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 61) _ validLayout0035) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind05749_0) certificate0211

private theorem bind05750_0 : Agrees (spec (fastBase 1 7 62) layout0035) scope0420 := by decide

theorem reject05750 : Rejected (base 1 7 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 62) _ validLayout0035) (by decide) scope0420 (by rw [← fastBase_exact]; exact bind05750_0) certificate0443

private theorem bind05751_0 : Agrees (spec (fastBase 1 7 63) layout0040) scope0434 := by decide

theorem reject05751 : Rejected (base 1 7 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 63) _ validLayout0040) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind05751_0) certificate0461

private theorem bind05752_0 : Agrees (spec (fastBase 1 7 64) layout0035) scope0423 := by decide

theorem reject05752 : Rejected (base 1 7 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 64) _ validLayout0035) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind05752_0) certificate0447

private theorem bind05753_0 : Agrees (spec (fastBase 1 7 65) layout0035) scope0205 := by decide

theorem reject05753 : Rejected (base 1 7 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 65) _ validLayout0035) (by decide) scope0205 (by rw [← fastBase_exact]; exact bind05753_0) certificate0208

private theorem bind05754_0 : Agrees (spec (fastBase 1 7 66) layout0035) scope0424 := by decide

theorem reject05754 : Rejected (base 1 7 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 66) _ validLayout0035) (by decide) scope0424 (by rw [← fastBase_exact]; exact bind05754_0) certificate0448

private theorem bind05755_0 : Agrees (spec (fastBase 1 7 67) layout0040) scope0236 := by decide

theorem reject05755 : Rejected (base 1 7 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0040 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 67) _ validLayout0040) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind05755_0) certificate0239

private theorem bind05756_0 : Agrees (spec (fastBase 1 7 68) layout0035) scope0555 := by decide

theorem reject05756 : Rejected (base 1 7 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 68) _ validLayout0035) (by decide) scope0555 (by rw [← fastBase_exact]; exact bind05756_0) certificate0598

private theorem bind05757_0 : Agrees (spec (fastBase 1 7 69) layout0035) scope0208 := by decide

theorem reject05757 : Rejected (base 1 7 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 69) _ validLayout0035) (by decide) scope0208 (by rw [← fastBase_exact]; exact bind05757_0) certificate0211

private theorem bind05758_0 : Agrees (spec (fastBase 1 7 70) layout0038) scope0222 := by decide

theorem reject05758 : Rejected (base 1 7 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0038 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 70) _ validLayout0038) (by decide) scope0222 (by rw [← fastBase_exact]; exact bind05758_0) certificate0225

private theorem bind05759_0 : Agrees (spec (fastBase 1 7 71) layout0035) scope0559 := by decide

theorem reject05759 : Rejected (base 1 7 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0035 (layoutValid_of_refines _ _ (base_refines_skeleton 1 7 71) _ validLayout0035) (by decide) scope0559 (by rw [← fastBase_exact]; exact bind05759_0) certificate0602

theorem allCases079 : ∀ y : Fin 72, Rejected (base 1 7 y) := by
  intro y
  fin_cases y

  · exact reject05688

  · exact reject05689

  · exact reject05690

  · exact reject05691

  · exact reject05692

  · exact reject05693

  · exact reject05694

  · exact reject05695

  · exact reject05696

  · exact reject05697

  · exact reject05698

  · exact reject05699

  · exact reject05700

  · exact reject05701

  · exact reject05702

  · exact reject05703

  · exact reject05704

  · exact reject05705

  · exact reject05706

  · exact reject05707

  · exact reject05708

  · exact reject05709

  · exact reject05710

  · exact reject05711

  · exact reject05712

  · exact reject05713

  · exact reject05714

  · exact reject05715

  · exact reject05716

  · exact reject05717

  · exact reject05718

  · exact reject05719

  · exact reject05720

  · exact reject05721

  · exact reject05722

  · exact reject05723

  · exact reject05724

  · exact reject05725

  · exact reject05726

  · exact reject05727

  · exact reject05728

  · exact reject05729

  · exact reject05730

  · exact reject05731

  · exact reject05732

  · exact reject05733

  · exact reject05734

  · exact reject05735

  · exact reject05736

  · exact reject05737

  · exact reject05738

  · exact reject05739

  · exact reject05740

  · exact reject05741

  · exact reject05742

  · exact reject05743

  · exact reject05744

  · exact reject05745

  · exact reject05746

  · exact reject05747

  · exact reject05748

  · exact reject05749

  · exact reject05750

  · exact reject05751

  · exact reject05752

  · exact reject05753

  · exact reject05754

  · exact reject05755

  · exact reject05756

  · exact reject05757

  · exact reject05758

  · exact reject05759

end PricingIntegration.RemainingGWitnesses
