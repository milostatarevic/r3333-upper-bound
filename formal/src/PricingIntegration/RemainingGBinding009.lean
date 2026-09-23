import PricingIntegration.RemainingGLayouts005

import PricingIntegration.RemainingGLayouts006

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks017

import PricingIntegration.RemainingGScopeChecks018


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00648_0 : Agrees (spec (fastBase 0 9 0) layout0044) scope0265 := by decide

theorem reject00648 : Rejected (base 0 9 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 0) _ validLayout0044) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind00648_0) certificate0268

private theorem bind00649_0 : Agrees (spec (fastBase 0 9 1) layout0044) scope0266 := by decide

theorem reject00649 : Rejected (base 0 9 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 1) _ validLayout0044) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind00649_0) certificate0269

private theorem bind00650_0 : Agrees (spec (fastBase 0 9 2) layout0044) scope0267 := by decide

theorem reject00650 : Rejected (base 0 9 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 2) _ validLayout0044) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind00650_0) certificate0270

private theorem bind00651_0 : Agrees (spec (fastBase 0 9 3) layout0044) scope0268 := by decide

theorem reject00651 : Rejected (base 0 9 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 3) _ validLayout0044) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind00651_0) certificate0271

private theorem bind00652_0 : Agrees (spec (fastBase 0 9 4) layout0044) scope0269 := by decide

theorem reject00652 : Rejected (base 0 9 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 4) _ validLayout0044) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind00652_0) certificate0272

private theorem bind00653_0 : Agrees (spec (fastBase 0 9 5) layout0044) scope0270 := by decide

theorem reject00653 : Rejected (base 0 9 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 5) _ validLayout0044) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind00653_0) certificate0273

private theorem bind00654_0 : Agrees (spec (fastBase 0 9 6) layout0044) scope0271 := by decide

theorem reject00654 : Rejected (base 0 9 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 6) _ validLayout0044) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind00654_0) certificate0274

private theorem bind00655_0 : Agrees (spec (fastBase 0 9 7) layout0045) scope0272 := by decide

private theorem bind00655_1 : Agrees (spec (fastBase 0 9 7) layout0046) scope0273 := by decide

theorem reject00655 : Rejected (base 0 9 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0045 layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 7) _ validLayout0045) (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 7) _ validLayout0046) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind00655_0) (by rw [← fastBase_exact]; exact bind00655_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind00656_0 : Agrees (spec (fastBase 0 9 8) layout0044) scope0274 := by decide

theorem reject00656 : Rejected (base 0 9 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 8) _ validLayout0044) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind00656_0) certificate0277

private theorem bind00657_0 : Agrees (spec (fastBase 0 9 9) layout0044) scope0275 := by decide

theorem reject00657 : Rejected (base 0 9 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 9) _ validLayout0044) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind00657_0) certificate0278

private theorem bind00658_0 : Agrees (spec (fastBase 0 9 10) layout0047) scope0276 := by decide

private theorem bind00658_1 : Agrees (spec (fastBase 0 9 10) layout0048) scope0277 := by decide

theorem reject00658 : Rejected (base 0 9 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0047 layout0048 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 10) _ validLayout0047) (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 10) _ validLayout0048) (by decide) (by decide) scope0276 scope0277 (by rw [← fastBase_exact]; exact bind00658_0) (by rw [← fastBase_exact]; exact bind00658_1) 3 8 3 8 (by decide) (by decide) 2 3 (by decide) certificate0279 certificate0280 (by decide)

private theorem bind00659_0 : Agrees (spec (fastBase 0 9 11) layout0044) scope0278 := by decide

theorem reject00659 : Rejected (base 0 9 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 11) _ validLayout0044) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind00659_0) certificate0281

private theorem bind00660_0 : Agrees (spec (fastBase 0 9 12) layout0044) scope0279 := by decide

theorem reject00660 : Rejected (base 0 9 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 12) _ validLayout0044) (by decide) scope0279 (by rw [← fastBase_exact]; exact bind00660_0) certificate0282

private theorem bind00661_0 : Agrees (spec (fastBase 0 9 13) layout0044) scope0267 := by decide

theorem reject00661 : Rejected (base 0 9 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 13) _ validLayout0044) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind00661_0) certificate0270

private theorem bind00662_0 : Agrees (spec (fastBase 0 9 14) layout0044) scope0270 := by decide

theorem reject00662 : Rejected (base 0 9 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 14) _ validLayout0044) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind00662_0) certificate0273

private theorem bind00663_0 : Agrees (spec (fastBase 0 9 15) layout0044) scope0265 := by decide

theorem reject00663 : Rejected (base 0 9 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 15) _ validLayout0044) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind00663_0) certificate0268

private theorem bind00664_0 : Agrees (spec (fastBase 0 9 16) layout0044) scope0280 := by decide

theorem reject00664 : Rejected (base 0 9 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 16) _ validLayout0044) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind00664_0) certificate0283

private theorem bind00665_0 : Agrees (spec (fastBase 0 9 17) layout0044) scope0281 := by decide

theorem reject00665 : Rejected (base 0 9 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 17) _ validLayout0044) (by decide) scope0281 (by rw [← fastBase_exact]; exact bind00665_0) certificate0284

private theorem bind00666_0 : Agrees (spec (fastBase 0 9 18) layout0044) scope0268 := by decide

theorem reject00666 : Rejected (base 0 9 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 18) _ validLayout0044) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind00666_0) certificate0271

private theorem bind00667_0 : Agrees (spec (fastBase 0 9 19) layout0044) scope0266 := by decide

theorem reject00667 : Rejected (base 0 9 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 19) _ validLayout0044) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind00667_0) certificate0269

private theorem bind00668_0 : Agrees (spec (fastBase 0 9 20) layout0044) scope0282 := by decide

theorem reject00668 : Rejected (base 0 9 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 20) _ validLayout0044) (by decide) scope0282 (by rw [← fastBase_exact]; exact bind00668_0) certificate0285

private theorem bind00669_0 : Agrees (spec (fastBase 0 9 21) layout0044) scope0275 := by decide

theorem reject00669 : Rejected (base 0 9 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 21) _ validLayout0044) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind00669_0) certificate0278

private theorem bind00670_0 : Agrees (spec (fastBase 0 9 22) layout0044) scope0265 := by decide

theorem reject00670 : Rejected (base 0 9 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 22) _ validLayout0044) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind00670_0) certificate0268

private theorem bind00671_0 : Agrees (spec (fastBase 0 9 23) layout0044) scope0267 := by decide

theorem reject00671 : Rejected (base 0 9 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 23) _ validLayout0044) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind00671_0) certificate0270

private theorem bind00672_0 : Agrees (spec (fastBase 0 9 24) layout0045) scope0279 := by decide

theorem reject00672 : Rejected (base 0 9 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0045 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 24) _ validLayout0045) (by decide) scope0279 (by rw [← fastBase_exact]; exact bind00672_0) certificate0282

private theorem bind00673_0 : Agrees (spec (fastBase 0 9 25) layout0044) scope0283 := by decide

theorem reject00673 : Rejected (base 0 9 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 25) _ validLayout0044) (by decide) scope0283 (by rw [← fastBase_exact]; exact bind00673_0) certificate0286

private theorem bind00674_0 : Agrees (spec (fastBase 0 9 26) layout0045) scope0267 := by decide

theorem reject00674 : Rejected (base 0 9 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0045 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 26) _ validLayout0045) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind00674_0) certificate0270

private theorem bind00675_0 : Agrees (spec (fastBase 0 9 27) layout0044) scope0266 := by decide

theorem reject00675 : Rejected (base 0 9 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 27) _ validLayout0044) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind00675_0) certificate0269

private theorem bind00676_0 : Agrees (spec (fastBase 0 9 28) layout0044) scope0279 := by decide

theorem reject00676 : Rejected (base 0 9 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 28) _ validLayout0044) (by decide) scope0279 (by rw [← fastBase_exact]; exact bind00676_0) certificate0282

private theorem bind00677_0 : Agrees (spec (fastBase 0 9 29) layout0044) scope0270 := by decide

theorem reject00677 : Rejected (base 0 9 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 29) _ validLayout0044) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind00677_0) certificate0273

private theorem bind00678_0 : Agrees (spec (fastBase 0 9 30) layout0044) scope0268 := by decide

theorem reject00678 : Rejected (base 0 9 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 30) _ validLayout0044) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind00678_0) certificate0271

private theorem bind00679_0 : Agrees (spec (fastBase 0 9 31) layout0044) scope0284 := by decide

theorem reject00679 : Rejected (base 0 9 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 31) _ validLayout0044) (by decide) scope0284 (by rw [← fastBase_exact]; exact bind00679_0) certificate0287

private theorem bind00680_0 : Agrees (spec (fastBase 0 9 32) layout0044) scope0269 := by decide

theorem reject00680 : Rejected (base 0 9 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 32) _ validLayout0044) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind00680_0) certificate0272

private theorem bind00681_0 : Agrees (spec (fastBase 0 9 33) layout0044) scope0269 := by decide

theorem reject00681 : Rejected (base 0 9 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 33) _ validLayout0044) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind00681_0) certificate0272

private theorem bind00682_0 : Agrees (spec (fastBase 0 9 34) layout0044) scope0269 := by decide

theorem reject00682 : Rejected (base 0 9 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 34) _ validLayout0044) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind00682_0) certificate0272

private theorem bind00683_0 : Agrees (spec (fastBase 0 9 35) layout0044) scope0269 := by decide

theorem reject00683 : Rejected (base 0 9 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 35) _ validLayout0044) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind00683_0) certificate0272

private theorem bind00684_0 : Agrees (spec (fastBase 0 9 36) layout0044) scope0269 := by decide

theorem reject00684 : Rejected (base 0 9 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 36) _ validLayout0044) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind00684_0) certificate0272

private theorem bind00685_0 : Agrees (spec (fastBase 0 9 37) layout0044) scope0265 := by decide

theorem reject00685 : Rejected (base 0 9 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 37) _ validLayout0044) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind00685_0) certificate0268

private theorem bind00686_0 : Agrees (spec (fastBase 0 9 38) layout0044) scope0270 := by decide

theorem reject00686 : Rejected (base 0 9 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 38) _ validLayout0044) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind00686_0) certificate0273

private theorem bind00687_0 : Agrees (spec (fastBase 0 9 39) layout0044) scope0268 := by decide

theorem reject00687 : Rejected (base 0 9 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 39) _ validLayout0044) (by decide) scope0268 (by rw [← fastBase_exact]; exact bind00687_0) certificate0271

private theorem bind00688_0 : Agrees (spec (fastBase 0 9 40) layout0044) scope0281 := by decide

theorem reject00688 : Rejected (base 0 9 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 40) _ validLayout0044) (by decide) scope0281 (by rw [← fastBase_exact]; exact bind00688_0) certificate0284

private theorem bind00689_0 : Agrees (spec (fastBase 0 9 41) layout0046) scope0285 := by decide

theorem reject00689 : Rejected (base 0 9 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 41) _ validLayout0046) (by decide) scope0285 (by rw [← fastBase_exact]; exact bind00689_0) certificate0288

private theorem bind00690_0 : Agrees (spec (fastBase 0 9 42) layout0044) scope0286 := by decide

theorem reject00690 : Rejected (base 0 9 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 42) _ validLayout0044) (by decide) scope0286 (by rw [← fastBase_exact]; exact bind00690_0) certificate0289

private theorem bind00691_0 : Agrees (spec (fastBase 0 9 43) layout0044) scope0287 := by decide

theorem reject00691 : Rejected (base 0 9 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 43) _ validLayout0044) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind00691_0) certificate0290

private theorem bind00692_0 : Agrees (spec (fastBase 0 9 44) layout0044) scope0274 := by decide

theorem reject00692 : Rejected (base 0 9 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 44) _ validLayout0044) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind00692_0) certificate0277

private theorem bind00693_0 : Agrees (spec (fastBase 0 9 45) layout0044) scope0271 := by decide

theorem reject00693 : Rejected (base 0 9 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 45) _ validLayout0044) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind00693_0) certificate0274

private theorem bind00694_0 : Agrees (spec (fastBase 0 9 46) layout0044) scope0278 := by decide

theorem reject00694 : Rejected (base 0 9 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 46) _ validLayout0044) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind00694_0) certificate0281

private theorem bind00695_0 : Agrees (spec (fastBase 0 9 47) layout0046) scope0288 := by decide

theorem reject00695 : Rejected (base 0 9 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 47) _ validLayout0046) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind00695_0) certificate0291

private theorem bind00696_0 : Agrees (spec (fastBase 0 9 48) layout0046) scope0289 := by decide

theorem reject00696 : Rejected (base 0 9 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 48) _ validLayout0046) (by decide) scope0289 (by rw [← fastBase_exact]; exact bind00696_0) certificate0292

private theorem bind00697_0 : Agrees (spec (fastBase 0 9 49) layout0045) scope0271 := by decide

theorem reject00697 : Rejected (base 0 9 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0045 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 49) _ validLayout0045) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind00697_0) certificate0274

private theorem bind00698_0 : Agrees (spec (fastBase 0 9 50) layout0045) scope0272 := by decide

private theorem bind00698_1 : Agrees (spec (fastBase 0 9 50) layout0046) scope0273 := by decide

theorem reject00698 : Rejected (base 0 9 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0045 layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 50) _ validLayout0045) (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 50) _ validLayout0046) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind00698_0) (by rw [← fastBase_exact]; exact bind00698_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind00699_0 : Agrees (spec (fastBase 0 9 51) layout0045) scope0290 := by decide

private theorem bind00699_1 : Agrees (spec (fastBase 0 9 51) layout0046) scope0273 := by decide

theorem reject00699 : Rejected (base 0 9 51) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0045 layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 51) _ validLayout0045) (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 51) _ validLayout0046) (by decide) (by decide) scope0290 scope0273 (by rw [← fastBase_exact]; exact bind00699_0) (by rw [← fastBase_exact]; exact bind00699_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0293 certificate0276 (by decide)

private theorem bind00700_0 : Agrees (spec (fastBase 0 9 52) layout0044) scope0283 := by decide

theorem reject00700 : Rejected (base 0 9 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 52) _ validLayout0044) (by decide) scope0283 (by rw [← fastBase_exact]; exact bind00700_0) certificate0286

private theorem bind00701_0 : Agrees (spec (fastBase 0 9 53) layout0044) scope0274 := by decide

theorem reject00701 : Rejected (base 0 9 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 53) _ validLayout0044) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind00701_0) certificate0277

private theorem bind00702_0 : Agrees (spec (fastBase 0 9 54) layout0044) scope0271 := by decide

theorem reject00702 : Rejected (base 0 9 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 54) _ validLayout0044) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind00702_0) certificate0274

private theorem bind00703_0 : Agrees (spec (fastBase 0 9 55) layout0045) scope0286 := by decide

theorem reject00703 : Rejected (base 0 9 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0045 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 55) _ validLayout0045) (by decide) scope0286 (by rw [← fastBase_exact]; exact bind00703_0) certificate0289

private theorem bind00704_0 : Agrees (spec (fastBase 0 9 56) layout0046) scope0291 := by decide

theorem reject00704 : Rejected (base 0 9 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 56) _ validLayout0046) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind00704_0) certificate0294

private theorem bind00705_0 : Agrees (spec (fastBase 0 9 57) layout0044) scope0266 := by decide

theorem reject00705 : Rejected (base 0 9 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 57) _ validLayout0044) (by decide) scope0266 (by rw [← fastBase_exact]; exact bind00705_0) certificate0269

private theorem bind00706_0 : Agrees (spec (fastBase 0 9 58) layout0044) scope0284 := by decide

theorem reject00706 : Rejected (base 0 9 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 58) _ validLayout0044) (by decide) scope0284 (by rw [← fastBase_exact]; exact bind00706_0) certificate0287

private theorem bind00707_0 : Agrees (spec (fastBase 0 9 59) layout0044) scope0286 := by decide

theorem reject00707 : Rejected (base 0 9 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 59) _ validLayout0044) (by decide) scope0286 (by rw [← fastBase_exact]; exact bind00707_0) certificate0289

private theorem bind00708_0 : Agrees (spec (fastBase 0 9 60) layout0044) scope0275 := by decide

theorem reject00708 : Rejected (base 0 9 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 60) _ validLayout0044) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind00708_0) certificate0278

private theorem bind00709_0 : Agrees (spec (fastBase 0 9 61) layout0044) scope0278 := by decide

theorem reject00709 : Rejected (base 0 9 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 61) _ validLayout0044) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind00709_0) certificate0281

private theorem bind00710_0 : Agrees (spec (fastBase 0 9 62) layout0044) scope0267 := by decide

theorem reject00710 : Rejected (base 0 9 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 62) _ validLayout0044) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind00710_0) certificate0270

private theorem bind00711_0 : Agrees (spec (fastBase 0 9 63) layout0044) scope0280 := by decide

theorem reject00711 : Rejected (base 0 9 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 63) _ validLayout0044) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind00711_0) certificate0283

private theorem bind00712_0 : Agrees (spec (fastBase 0 9 64) layout0045) scope0272 := by decide

private theorem bind00712_1 : Agrees (spec (fastBase 0 9 64) layout0046) scope0276 := by decide

theorem reject00712 : Rejected (base 0 9 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0045 layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 64) _ validLayout0045) (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 64) _ validLayout0046) (by decide) (by decide) scope0272 scope0276 (by rw [← fastBase_exact]; exact bind00712_0) (by rw [← fastBase_exact]; exact bind00712_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0295 certificate0296 (by decide)

private theorem bind00713_0 : Agrees (spec (fastBase 0 9 65) layout0044) scope0274 := by decide

theorem reject00713 : Rejected (base 0 9 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 65) _ validLayout0044) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind00713_0) certificate0277

private theorem bind00714_0 : Agrees (spec (fastBase 0 9 66) layout0044) scope0287 := by decide

theorem reject00714 : Rejected (base 0 9 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 66) _ validLayout0044) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind00714_0) certificate0290

private theorem bind00715_0 : Agrees (spec (fastBase 0 9 67) layout0044) scope0282 := by decide

theorem reject00715 : Rejected (base 0 9 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 67) _ validLayout0044) (by decide) scope0282 (by rw [← fastBase_exact]; exact bind00715_0) certificate0285

private theorem bind00716_0 : Agrees (spec (fastBase 0 9 68) layout0044) scope0278 := by decide

theorem reject00716 : Rejected (base 0 9 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 68) _ validLayout0044) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind00716_0) certificate0281

private theorem bind00717_0 : Agrees (spec (fastBase 0 9 69) layout0044) scope0271 := by decide

theorem reject00717 : Rejected (base 0 9 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 69) _ validLayout0044) (by decide) scope0271 (by rw [← fastBase_exact]; exact bind00717_0) certificate0274

private theorem bind00718_0 : Agrees (spec (fastBase 0 9 70) layout0044) scope0275 := by decide

theorem reject00718 : Rejected (base 0 9 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0044 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 70) _ validLayout0044) (by decide) scope0275 (by rw [← fastBase_exact]; exact bind00718_0) certificate0278

private theorem bind00719_0 : Agrees (spec (fastBase 0 9 71) layout0045) scope0292 := by decide

private theorem bind00719_1 : Agrees (spec (fastBase 0 9 71) layout0046) scope0293 := by decide

theorem reject00719 : Rejected (base 0 9 71) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0045 layout0046 (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 71) _ validLayout0045) (layoutValid_of_refines _ _ (base_refines_skeleton 0 9 71) _ validLayout0046) (by decide) (by decide) scope0292 scope0293 (by rw [← fastBase_exact]; exact bind00719_0) (by rw [← fastBase_exact]; exact bind00719_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0297 certificate0298 (by decide)

theorem allCases009 : ∀ y : Fin 72, Rejected (base 0 9 y) := by
  intro y
  fin_cases y

  · exact reject00648

  · exact reject00649

  · exact reject00650

  · exact reject00651

  · exact reject00652

  · exact reject00653

  · exact reject00654

  · exact reject00655

  · exact reject00656

  · exact reject00657

  · exact reject00658

  · exact reject00659

  · exact reject00660

  · exact reject00661

  · exact reject00662

  · exact reject00663

  · exact reject00664

  · exact reject00665

  · exact reject00666

  · exact reject00667

  · exact reject00668

  · exact reject00669

  · exact reject00670

  · exact reject00671

  · exact reject00672

  · exact reject00673

  · exact reject00674

  · exact reject00675

  · exact reject00676

  · exact reject00677

  · exact reject00678

  · exact reject00679

  · exact reject00680

  · exact reject00681

  · exact reject00682

  · exact reject00683

  · exact reject00684

  · exact reject00685

  · exact reject00686

  · exact reject00687

  · exact reject00688

  · exact reject00689

  · exact reject00690

  · exact reject00691

  · exact reject00692

  · exact reject00693

  · exact reject00694

  · exact reject00695

  · exact reject00696

  · exact reject00697

  · exact reject00698

  · exact reject00699

  · exact reject00700

  · exact reject00701

  · exact reject00702

  · exact reject00703

  · exact reject00704

  · exact reject00705

  · exact reject00706

  · exact reject00707

  · exact reject00708

  · exact reject00709

  · exact reject00710

  · exact reject00711

  · exact reject00712

  · exact reject00713

  · exact reject00714

  · exact reject00715

  · exact reject00716

  · exact reject00717

  · exact reject00718

  · exact reject00719

end PricingIntegration.RemainingGWitnesses
