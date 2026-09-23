import PricingIntegration.RemainingGLayouts006

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks019

import PricingIntegration.RemainingGScopeChecks020


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind00720_0 : Agrees (spec (fastBase 0 10 0) layout0049) scope0294 := by decide

theorem reject00720 : Rejected (base 0 10 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 0) _ validLayout0049) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind00720_0) certificate0299

private theorem bind00721_0 : Agrees (spec (fastBase 0 10 1) layout0049) scope0295 := by decide

theorem reject00721 : Rejected (base 0 10 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 1) _ validLayout0049) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind00721_0) certificate0300

private theorem bind00722_0 : Agrees (spec (fastBase 0 10 2) layout0049) scope0296 := by decide

theorem reject00722 : Rejected (base 0 10 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 2) _ validLayout0049) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind00722_0) certificate0301

private theorem bind00723_0 : Agrees (spec (fastBase 0 10 3) layout0049) scope0297 := by decide

theorem reject00723 : Rejected (base 0 10 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 3) _ validLayout0049) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind00723_0) certificate0302

private theorem bind00724_0 : Agrees (spec (fastBase 0 10 4) layout0049) scope0298 := by decide

theorem reject00724 : Rejected (base 0 10 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 4) _ validLayout0049) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind00724_0) certificate0303

private theorem bind00725_0 : Agrees (spec (fastBase 0 10 5) layout0049) scope0299 := by decide

theorem reject00725 : Rejected (base 0 10 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 5) _ validLayout0049) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind00725_0) certificate0304

private theorem bind00726_0 : Agrees (spec (fastBase 0 10 6) layout0050) scope0300 := by decide

private theorem bind00726_1 : Agrees (spec (fastBase 0 10 6) layout0051) scope0301 := by decide

theorem reject00726 : Rejected (base 0 10 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0050 layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 6) _ validLayout0050) (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 6) _ validLayout0051) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind00726_0) (by rw [← fastBase_exact]; exact bind00726_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind00727_0 : Agrees (spec (fastBase 0 10 7) layout0049) scope0302 := by decide

theorem reject00727 : Rejected (base 0 10 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 7) _ validLayout0049) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind00727_0) certificate0307

private theorem bind00728_0 : Agrees (spec (fastBase 0 10 8) layout0049) scope0303 := by decide

theorem reject00728 : Rejected (base 0 10 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 8) _ validLayout0049) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind00728_0) certificate0308

private theorem bind00729_0 : Agrees (spec (fastBase 0 10 9) layout0049) scope0304 := by decide

theorem reject00729 : Rejected (base 0 10 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 9) _ validLayout0049) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind00729_0) certificate0309

private theorem bind00730_0 : Agrees (spec (fastBase 0 10 10) layout0049) scope0305 := by decide

theorem reject00730 : Rejected (base 0 10 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 10) _ validLayout0049) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind00730_0) certificate0310

private theorem bind00731_0 : Agrees (spec (fastBase 0 10 11) layout0052) scope0306 := by decide

private theorem bind00731_1 : Agrees (spec (fastBase 0 10 11) layout0053) scope0307 := by decide

theorem reject00731 : Rejected (base 0 10 11) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0052 layout0053 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 11) _ validLayout0052) (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 11) _ validLayout0053) (by decide) (by decide) scope0306 scope0307 (by rw [← fastBase_exact]; exact bind00731_0) (by rw [← fastBase_exact]; exact bind00731_1) 3 8 3 8 (by decide) (by decide) 3 2 (by decide) certificate0311 certificate0312 (by decide)

private theorem bind00732_0 : Agrees (spec (fastBase 0 10 12) layout0049) scope0308 := by decide

theorem reject00732 : Rejected (base 0 10 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 12) _ validLayout0049) (by decide) scope0308 (by rw [← fastBase_exact]; exact bind00732_0) certificate0313

private theorem bind00733_0 : Agrees (spec (fastBase 0 10 13) layout0049) scope0296 := by decide

theorem reject00733 : Rejected (base 0 10 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 13) _ validLayout0049) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind00733_0) certificate0301

private theorem bind00734_0 : Agrees (spec (fastBase 0 10 14) layout0049) scope0294 := by decide

theorem reject00734 : Rejected (base 0 10 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 14) _ validLayout0049) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind00734_0) certificate0299

private theorem bind00735_0 : Agrees (spec (fastBase 0 10 15) layout0049) scope0309 := by decide

theorem reject00735 : Rejected (base 0 10 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 15) _ validLayout0049) (by decide) scope0309 (by rw [← fastBase_exact]; exact bind00735_0) certificate0314

private theorem bind00736_0 : Agrees (spec (fastBase 0 10 16) layout0049) scope0303 := by decide

theorem reject00736 : Rejected (base 0 10 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 16) _ validLayout0049) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind00736_0) certificate0308

private theorem bind00737_0 : Agrees (spec (fastBase 0 10 17) layout0049) scope0310 := by decide

theorem reject00737 : Rejected (base 0 10 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 17) _ validLayout0049) (by decide) scope0310 (by rw [← fastBase_exact]; exact bind00737_0) certificate0315

private theorem bind00738_0 : Agrees (spec (fastBase 0 10 18) layout0049) scope0297 := by decide

theorem reject00738 : Rejected (base 0 10 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 18) _ validLayout0049) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind00738_0) certificate0302

private theorem bind00739_0 : Agrees (spec (fastBase 0 10 19) layout0049) scope0298 := by decide

theorem reject00739 : Rejected (base 0 10 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 19) _ validLayout0049) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind00739_0) certificate0303

private theorem bind00740_0 : Agrees (spec (fastBase 0 10 20) layout0049) scope0295 := by decide

theorem reject00740 : Rejected (base 0 10 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 20) _ validLayout0049) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind00740_0) certificate0300

private theorem bind00741_0 : Agrees (spec (fastBase 0 10 21) layout0049) scope0311 := by decide

theorem reject00741 : Rejected (base 0 10 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 21) _ validLayout0049) (by decide) scope0311 (by rw [← fastBase_exact]; exact bind00741_0) certificate0316

private theorem bind00742_0 : Agrees (spec (fastBase 0 10 22) layout0049) scope0294 := by decide

theorem reject00742 : Rejected (base 0 10 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 22) _ validLayout0049) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind00742_0) certificate0299

private theorem bind00743_0 : Agrees (spec (fastBase 0 10 23) layout0049) scope0298 := by decide

theorem reject00743 : Rejected (base 0 10 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 23) _ validLayout0049) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind00743_0) certificate0303

private theorem bind00744_0 : Agrees (spec (fastBase 0 10 24) layout0049) scope0310 := by decide

theorem reject00744 : Rejected (base 0 10 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 24) _ validLayout0049) (by decide) scope0310 (by rw [← fastBase_exact]; exact bind00744_0) certificate0315

private theorem bind00745_0 : Agrees (spec (fastBase 0 10 25) layout0049) scope0296 := by decide

theorem reject00745 : Rejected (base 0 10 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 25) _ validLayout0049) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind00745_0) certificate0301

private theorem bind00746_0 : Agrees (spec (fastBase 0 10 26) layout0049) scope0312 := by decide

theorem reject00746 : Rejected (base 0 10 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 26) _ validLayout0049) (by decide) scope0312 (by rw [← fastBase_exact]; exact bind00746_0) certificate0317

private theorem bind00747_0 : Agrees (spec (fastBase 0 10 27) layout0049) scope0295 := by decide

theorem reject00747 : Rejected (base 0 10 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 27) _ validLayout0049) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind00747_0) certificate0300

private theorem bind00748_0 : Agrees (spec (fastBase 0 10 28) layout0051) scope0313 := by decide

theorem reject00748 : Rejected (base 0 10 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 28) _ validLayout0051) (by decide) scope0313 (by rw [← fastBase_exact]; exact bind00748_0) certificate0318

private theorem bind00749_0 : Agrees (spec (fastBase 0 10 29) layout0049) scope0297 := by decide

theorem reject00749 : Rejected (base 0 10 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 29) _ validLayout0049) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind00749_0) certificate0302

private theorem bind00750_0 : Agrees (spec (fastBase 0 10 30) layout0049) scope0314 := by decide

theorem reject00750 : Rejected (base 0 10 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 30) _ validLayout0049) (by decide) scope0314 (by rw [← fastBase_exact]; exact bind00750_0) certificate0319

private theorem bind00751_0 : Agrees (spec (fastBase 0 10 31) layout0051) scope0315 := by decide

theorem reject00751 : Rejected (base 0 10 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 31) _ validLayout0051) (by decide) scope0315 (by rw [← fastBase_exact]; exact bind00751_0) certificate0320

private theorem bind00752_0 : Agrees (spec (fastBase 0 10 32) layout0049) scope0295 := by decide

theorem reject00752 : Rejected (base 0 10 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 32) _ validLayout0049) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind00752_0) certificate0300

private theorem bind00753_0 : Agrees (spec (fastBase 0 10 33) layout0049) scope0296 := by decide

theorem reject00753 : Rejected (base 0 10 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 33) _ validLayout0049) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind00753_0) certificate0301

private theorem bind00754_0 : Agrees (spec (fastBase 0 10 34) layout0049) scope0298 := by decide

theorem reject00754 : Rejected (base 0 10 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 34) _ validLayout0049) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind00754_0) certificate0303

private theorem bind00755_0 : Agrees (spec (fastBase 0 10 35) layout0049) scope0308 := by decide

theorem reject00755 : Rejected (base 0 10 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 35) _ validLayout0049) (by decide) scope0308 (by rw [← fastBase_exact]; exact bind00755_0) certificate0313

private theorem bind00756_0 : Agrees (spec (fastBase 0 10 36) layout0050) scope0311 := by decide

theorem reject00756 : Rejected (base 0 10 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 36) _ validLayout0050) (by decide) scope0311 (by rw [← fastBase_exact]; exact bind00756_0) certificate0316

private theorem bind00757_0 : Agrees (spec (fastBase 0 10 37) layout0049) scope0299 := by decide

theorem reject00757 : Rejected (base 0 10 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 37) _ validLayout0049) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind00757_0) certificate0304

private theorem bind00758_0 : Agrees (spec (fastBase 0 10 38) layout0049) scope0299 := by decide

theorem reject00758 : Rejected (base 0 10 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 38) _ validLayout0049) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind00758_0) certificate0304

private theorem bind00759_0 : Agrees (spec (fastBase 0 10 39) layout0049) scope0299 := by decide

theorem reject00759 : Rejected (base 0 10 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 39) _ validLayout0049) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind00759_0) certificate0304

private theorem bind00760_0 : Agrees (spec (fastBase 0 10 40) layout0049) scope0299 := by decide

theorem reject00760 : Rejected (base 0 10 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 40) _ validLayout0049) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind00760_0) certificate0304

private theorem bind00761_0 : Agrees (spec (fastBase 0 10 41) layout0049) scope0299 := by decide

theorem reject00761 : Rejected (base 0 10 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 41) _ validLayout0049) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind00761_0) certificate0304

private theorem bind00762_0 : Agrees (spec (fastBase 0 10 42) layout0050) scope0295 := by decide

theorem reject00762 : Rejected (base 0 10 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 42) _ validLayout0050) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind00762_0) certificate0300

private theorem bind00763_0 : Agrees (spec (fastBase 0 10 43) layout0050) scope0296 := by decide

theorem reject00763 : Rejected (base 0 10 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 43) _ validLayout0050) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind00763_0) certificate0301

private theorem bind00764_0 : Agrees (spec (fastBase 0 10 44) layout0050) scope0300 := by decide

private theorem bind00764_1 : Agrees (spec (fastBase 0 10 44) layout0051) scope0301 := by decide

theorem reject00764 : Rejected (base 0 10 44) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0050 layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 44) _ validLayout0050) (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 44) _ validLayout0051) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind00764_0) (by rw [← fastBase_exact]; exact bind00764_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind00765_0 : Agrees (spec (fastBase 0 10 45) layout0051) scope0316 := by decide

theorem reject00765 : Rejected (base 0 10 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 45) _ validLayout0051) (by decide) scope0316 (by rw [← fastBase_exact]; exact bind00765_0) certificate0321

private theorem bind00766_0 : Agrees (spec (fastBase 0 10 46) layout0050) scope0300 := by decide

private theorem bind00766_1 : Agrees (spec (fastBase 0 10 46) layout0051) scope0306 := by decide

theorem reject00766 : Rejected (base 0 10 46) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0050 layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 46) _ validLayout0050) (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 46) _ validLayout0051) (by decide) (by decide) scope0300 scope0306 (by rw [← fastBase_exact]; exact bind00766_0) (by rw [← fastBase_exact]; exact bind00766_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0322 (by decide)

private theorem bind00767_0 : Agrees (spec (fastBase 0 10 47) layout0049) scope0317 := by decide

theorem reject00767 : Rejected (base 0 10 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 47) _ validLayout0049) (by decide) scope0317 (by rw [← fastBase_exact]; exact bind00767_0) certificate0323

private theorem bind00768_0 : Agrees (spec (fastBase 0 10 48) layout0049) scope0318 := by decide

theorem reject00768 : Rejected (base 0 10 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 48) _ validLayout0049) (by decide) scope0318 (by rw [← fastBase_exact]; exact bind00768_0) certificate0324

private theorem bind00769_0 : Agrees (spec (fastBase 0 10 49) layout0049) scope0302 := by decide

theorem reject00769 : Rejected (base 0 10 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 49) _ validLayout0049) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind00769_0) certificate0307

private theorem bind00770_0 : Agrees (spec (fastBase 0 10 50) layout0049) scope0304 := by decide

theorem reject00770 : Rejected (base 0 10 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 50) _ validLayout0049) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind00770_0) certificate0309

private theorem bind00771_0 : Agrees (spec (fastBase 0 10 51) layout0049) scope0305 := by decide

theorem reject00771 : Rejected (base 0 10 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 51) _ validLayout0049) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind00771_0) certificate0310

private theorem bind00772_0 : Agrees (spec (fastBase 0 10 52) layout0049) scope0294 := by decide

theorem reject00772 : Rejected (base 0 10 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 52) _ validLayout0049) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind00772_0) certificate0299

private theorem bind00773_0 : Agrees (spec (fastBase 0 10 53) layout0049) scope0312 := by decide

theorem reject00773 : Rejected (base 0 10 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 53) _ validLayout0049) (by decide) scope0312 (by rw [← fastBase_exact]; exact bind00773_0) certificate0317

private theorem bind00774_0 : Agrees (spec (fastBase 0 10 54) layout0049) scope0303 := by decide

theorem reject00774 : Rejected (base 0 10 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 54) _ validLayout0049) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind00774_0) certificate0308

private theorem bind00775_0 : Agrees (spec (fastBase 0 10 55) layout0049) scope0317 := by decide

theorem reject00775 : Rejected (base 0 10 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 55) _ validLayout0049) (by decide) scope0317 (by rw [← fastBase_exact]; exact bind00775_0) certificate0323

private theorem bind00776_0 : Agrees (spec (fastBase 0 10 56) layout0049) scope0305 := by decide

theorem reject00776 : Rejected (base 0 10 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 56) _ validLayout0049) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind00776_0) certificate0310

private theorem bind00777_0 : Agrees (spec (fastBase 0 10 57) layout0049) scope0314 := by decide

theorem reject00777 : Rejected (base 0 10 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 57) _ validLayout0049) (by decide) scope0314 (by rw [← fastBase_exact]; exact bind00777_0) certificate0319

private theorem bind00778_0 : Agrees (spec (fastBase 0 10 58) layout0049) scope0304 := by decide

theorem reject00778 : Rejected (base 0 10 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 58) _ validLayout0049) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind00778_0) certificate0309

private theorem bind00779_0 : Agrees (spec (fastBase 0 10 59) layout0051) scope0319 := by decide

theorem reject00779 : Rejected (base 0 10 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 59) _ validLayout0051) (by decide) scope0319 (by rw [← fastBase_exact]; exact bind00779_0) certificate0325

private theorem bind00780_0 : Agrees (spec (fastBase 0 10 60) layout0049) scope0302 := by decide

theorem reject00780 : Rejected (base 0 10 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 60) _ validLayout0049) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind00780_0) certificate0307

private theorem bind00781_0 : Agrees (spec (fastBase 0 10 61) layout0050) scope0304 := by decide

theorem reject00781 : Rejected (base 0 10 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0050 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 61) _ validLayout0050) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind00781_0) certificate0309

private theorem bind00782_0 : Agrees (spec (fastBase 0 10 62) layout0049) scope0309 := by decide

theorem reject00782 : Rejected (base 0 10 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 62) _ validLayout0049) (by decide) scope0309 (by rw [← fastBase_exact]; exact bind00782_0) certificate0314

private theorem bind00783_0 : Agrees (spec (fastBase 0 10 63) layout0049) scope0305 := by decide

theorem reject00783 : Rejected (base 0 10 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 63) _ validLayout0049) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind00783_0) certificate0310

private theorem bind00784_0 : Agrees (spec (fastBase 0 10 64) layout0049) scope0302 := by decide

theorem reject00784 : Rejected (base 0 10 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 64) _ validLayout0049) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind00784_0) certificate0307

private theorem bind00785_0 : Agrees (spec (fastBase 0 10 65) layout0049) scope0303 := by decide

theorem reject00785 : Rejected (base 0 10 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 65) _ validLayout0049) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind00785_0) certificate0308

private theorem bind00786_0 : Agrees (spec (fastBase 0 10 66) layout0050) scope0320 := by decide

private theorem bind00786_1 : Agrees (spec (fastBase 0 10 66) layout0051) scope0321 := by decide

theorem reject00786 : Rejected (base 0 10 66) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0050 layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 66) _ validLayout0050) (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 66) _ validLayout0051) (by decide) (by decide) scope0320 scope0321 (by rw [← fastBase_exact]; exact bind00786_0) (by rw [← fastBase_exact]; exact bind00786_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0326 certificate0327 (by decide)

private theorem bind00787_0 : Agrees (spec (fastBase 0 10 67) layout0049) scope0297 := by decide

theorem reject00787 : Rejected (base 0 10 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 67) _ validLayout0049) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind00787_0) certificate0302

private theorem bind00788_0 : Agrees (spec (fastBase 0 10 68) layout0049) scope0311 := by decide

theorem reject00788 : Rejected (base 0 10 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 68) _ validLayout0049) (by decide) scope0311 (by rw [← fastBase_exact]; exact bind00788_0) certificate0316

private theorem bind00789_0 : Agrees (spec (fastBase 0 10 69) layout0050) scope0322 := by decide

private theorem bind00789_1 : Agrees (spec (fastBase 0 10 69) layout0051) scope0301 := by decide

theorem reject00789 : Rejected (base 0 10 69) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0050 layout0051 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 69) _ validLayout0050) (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 69) _ validLayout0051) (by decide) (by decide) scope0322 scope0301 (by rw [← fastBase_exact]; exact bind00789_0) (by rw [← fastBase_exact]; exact bind00789_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0328 certificate0329 (by decide)

private theorem bind00790_0 : Agrees (spec (fastBase 0 10 70) layout0049) scope0304 := by decide

theorem reject00790 : Rejected (base 0 10 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 70) _ validLayout0049) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind00790_0) certificate0309

private theorem bind00791_0 : Agrees (spec (fastBase 0 10 71) layout0049) scope0318 := by decide

theorem reject00791 : Rejected (base 0 10 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0049 (layoutValid_of_refines _ _ (base_refines_skeleton 0 10 71) _ validLayout0049) (by decide) scope0318 (by rw [← fastBase_exact]; exact bind00791_0) certificate0324

theorem allCases010 : ∀ y : Fin 72, Rejected (base 0 10 y) := by
  intro y
  fin_cases y

  · exact reject00720

  · exact reject00721

  · exact reject00722

  · exact reject00723

  · exact reject00724

  · exact reject00725

  · exact reject00726

  · exact reject00727

  · exact reject00728

  · exact reject00729

  · exact reject00730

  · exact reject00731

  · exact reject00732

  · exact reject00733

  · exact reject00734

  · exact reject00735

  · exact reject00736

  · exact reject00737

  · exact reject00738

  · exact reject00739

  · exact reject00740

  · exact reject00741

  · exact reject00742

  · exact reject00743

  · exact reject00744

  · exact reject00745

  · exact reject00746

  · exact reject00747

  · exact reject00748

  · exact reject00749

  · exact reject00750

  · exact reject00751

  · exact reject00752

  · exact reject00753

  · exact reject00754

  · exact reject00755

  · exact reject00756

  · exact reject00757

  · exact reject00758

  · exact reject00759

  · exact reject00760

  · exact reject00761

  · exact reject00762

  · exact reject00763

  · exact reject00764

  · exact reject00765

  · exact reject00766

  · exact reject00767

  · exact reject00768

  · exact reject00769

  · exact reject00770

  · exact reject00771

  · exact reject00772

  · exact reject00773

  · exact reject00774

  · exact reject00775

  · exact reject00776

  · exact reject00777

  · exact reject00778

  · exact reject00779

  · exact reject00780

  · exact reject00781

  · exact reject00782

  · exact reject00783

  · exact reject00784

  · exact reject00785

  · exact reject00786

  · exact reject00787

  · exact reject00788

  · exact reject00789

  · exact reject00790

  · exact reject00791

end PricingIntegration.RemainingGWitnesses
