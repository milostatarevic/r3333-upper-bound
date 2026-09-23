import PricingIntegration.RemainingGLayouts003

import PricingIntegration.RemainingGLayouts004

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05616_0 : Agrees (spec (fastBase 1 6 0) layout0031) scope0232 := by decide

theorem reject05616 : Rejected (base 1 6 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 0) _ validLayout0031) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind05616_0) certificate0235

private theorem bind05617_0 : Agrees (spec (fastBase 1 6 1) layout0031) scope0547 := by decide

theorem reject05617 : Rejected (base 1 6 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 1) _ validLayout0031) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind05617_0) certificate0589

private theorem bind05618_0 : Agrees (spec (fastBase 1 6 2) layout0031) scope0548 := by decide

theorem reject05618 : Rejected (base 1 6 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 2) _ validLayout0031) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind05618_0) certificate0590

private theorem bind05619_0 : Agrees (spec (fastBase 1 6 3) layout0032) scope0549 := by decide

private theorem bind05619_1 : Agrees (spec (fastBase 1 6 3) layout0034) scope0430 := by decide

theorem reject05619 : Rejected (base 1 6 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0032 layout0034 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 3) _ validLayout0032) (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 3) _ validLayout0034) (by decide) (by decide) scope0549 scope0430 (by rw [← fastBase_exact]; exact bind05619_0) (by rw [← fastBase_exact]; exact bind05619_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0591 certificate0457 (by decide)

private theorem bind05620_0 : Agrees (spec (fastBase 1 6 4) layout0031) scope0233 := by decide

theorem reject05620 : Rejected (base 1 6 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 4) _ validLayout0031) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind05620_0) certificate0236

private theorem bind05621_0 : Agrees (spec (fastBase 1 6 5) layout0032) scope0215 := by decide

private theorem bind05621_1 : Agrees (spec (fastBase 1 6 5) layout0034) scope0432 := by decide

theorem reject05621 : Rejected (base 1 6 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0032 layout0034 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 5) _ validLayout0032) (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 5) _ validLayout0034) (by decide) (by decide) scope0215 scope0432 (by rw [← fastBase_exact]; exact bind05621_0) (by rw [← fastBase_exact]; exact bind05621_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0592 certificate0459 (by decide)

private theorem bind05622_0 : Agrees (spec (fastBase 1 6 6) layout0031) scope0438 := by decide

theorem reject05622 : Rejected (base 1 6 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 6) _ validLayout0031) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind05622_0) certificate0467

private theorem bind05623_0 : Agrees (spec (fastBase 1 6 7) layout0031) scope0441 := by decide

theorem reject05623 : Rejected (base 1 6 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 7) _ validLayout0031) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind05623_0) certificate0470

private theorem bind05624_0 : Agrees (spec (fastBase 1 6 8) layout0031) scope0444 := by decide

theorem reject05624 : Rejected (base 1 6 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 8) _ validLayout0031) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind05624_0) certificate0475

private theorem bind05625_0 : Agrees (spec (fastBase 1 6 9) layout0031) scope0433 := by decide

theorem reject05625 : Rejected (base 1 6 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 9) _ validLayout0031) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind05625_0) certificate0460

private theorem bind05626_0 : Agrees (spec (fastBase 1 6 10) layout0031) scope0434 := by decide

theorem reject05626 : Rejected (base 1 6 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 10) _ validLayout0031) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind05626_0) certificate0461

private theorem bind05627_0 : Agrees (spec (fastBase 1 6 11) layout0031) scope0236 := by decide

theorem reject05627 : Rejected (base 1 6 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 11) _ validLayout0031) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind05627_0) certificate0239

private theorem bind05628_0 : Agrees (spec (fastBase 1 6 12) layout0031) scope0550 := by decide

theorem reject05628 : Rejected (base 1 6 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 12) _ validLayout0031) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind05628_0) certificate0593

private theorem bind05629_0 : Agrees (spec (fastBase 1 6 13) layout0031) scope0548 := by decide

theorem reject05629 : Rejected (base 1 6 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 13) _ validLayout0031) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind05629_0) certificate0590

private theorem bind05630_0 : Agrees (spec (fastBase 1 6 14) layout0031) scope0232 := by decide

theorem reject05630 : Rejected (base 1 6 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 14) _ validLayout0031) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind05630_0) certificate0235

private theorem bind05631_0 : Agrees (spec (fastBase 1 6 15) layout0031) scope0442 := by decide

theorem reject05631 : Rejected (base 1 6 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 15) _ validLayout0031) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind05631_0) certificate0471

private theorem bind05632_0 : Agrees (spec (fastBase 1 6 16) layout0031) scope0444 := by decide

theorem reject05632 : Rejected (base 1 6 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 16) _ validLayout0031) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind05632_0) certificate0475

private theorem bind05633_0 : Agrees (spec (fastBase 1 6 17) layout0029) scope0194 := by decide

theorem reject05633 : Rejected (base 1 6 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 17) _ validLayout0029) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind05633_0) certificate0197

private theorem bind05634_0 : Agrees (spec (fastBase 1 6 18) layout0033) scope0195 := by decide

theorem reject05634 : Rejected (base 1 6 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0033 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 18) _ validLayout0033) (by decide) scope0195 (by rw [← fastBase_exact]; exact bind05634_0) certificate0198

private theorem bind05635_0 : Agrees (spec (fastBase 1 6 19) layout0031) scope0233 := by decide

theorem reject05635 : Rejected (base 1 6 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 19) _ validLayout0031) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind05635_0) certificate0236

private theorem bind05636_0 : Agrees (spec (fastBase 1 6 20) layout0031) scope0547 := by decide

theorem reject05636 : Rejected (base 1 6 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 20) _ validLayout0031) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind05636_0) certificate0589

private theorem bind05637_0 : Agrees (spec (fastBase 1 6 21) layout0031) scope0551 := by decide

theorem reject05637 : Rejected (base 1 6 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 21) _ validLayout0031) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind05637_0) certificate0594

private theorem bind05638_0 : Agrees (spec (fastBase 1 6 22) layout0031) scope0232 := by decide

theorem reject05638 : Rejected (base 1 6 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 22) _ validLayout0031) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind05638_0) certificate0235

private theorem bind05639_0 : Agrees (spec (fastBase 1 6 23) layout0031) scope0233 := by decide

theorem reject05639 : Rejected (base 1 6 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 23) _ validLayout0031) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind05639_0) certificate0236

private theorem bind05640_0 : Agrees (spec (fastBase 1 6 24) layout0029) scope0200 := by decide

theorem reject05640 : Rejected (base 1 6 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 24) _ validLayout0029) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind05640_0) certificate0203

private theorem bind05641_0 : Agrees (spec (fastBase 1 6 25) layout0031) scope0548 := by decide

theorem reject05641 : Rejected (base 1 6 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 25) _ validLayout0031) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind05641_0) certificate0590

private theorem bind05642_0 : Agrees (spec (fastBase 1 6 26) layout0031) scope0439 := by decide

theorem reject05642 : Rejected (base 1 6 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 26) _ validLayout0031) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind05642_0) certificate0468

private theorem bind05643_0 : Agrees (spec (fastBase 1 6 27) layout0031) scope0547 := by decide

theorem reject05643 : Rejected (base 1 6 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 27) _ validLayout0031) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind05643_0) certificate0589

private theorem bind05644_0 : Agrees (spec (fastBase 1 6 28) layout0031) scope0228 := by decide

theorem reject05644 : Rejected (base 1 6 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 28) _ validLayout0031) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind05644_0) certificate0231

private theorem bind05645_0 : Agrees (spec (fastBase 1 6 29) layout0032) scope0549 := by decide

private theorem bind05645_1 : Agrees (spec (fastBase 1 6 29) layout0034) scope0432 := by decide

theorem reject05645 : Rejected (base 1 6 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0032 layout0034 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 29) _ validLayout0032) (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 29) _ validLayout0034) (by decide) (by decide) scope0549 scope0432 (by rw [← fastBase_exact]; exact bind05645_0) (by rw [← fastBase_exact]; exact bind05645_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0591 certificate0459 (by decide)

private theorem bind05646_0 : Agrees (spec (fastBase 1 6 30) layout0031) scope0389 := by decide

theorem reject05646 : Rejected (base 1 6 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 30) _ validLayout0031) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind05646_0) certificate0402

private theorem bind05647_0 : Agrees (spec (fastBase 1 6 31) layout0031) scope0236 := by decide

theorem reject05647 : Rejected (base 1 6 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 31) _ validLayout0031) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind05647_0) certificate0239

private theorem bind05648_0 : Agrees (spec (fastBase 1 6 32) layout0031) scope0547 := by decide

theorem reject05648 : Rejected (base 1 6 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 32) _ validLayout0031) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind05648_0) certificate0589

private theorem bind05649_0 : Agrees (spec (fastBase 1 6 33) layout0031) scope0548 := by decide

theorem reject05649 : Rejected (base 1 6 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 33) _ validLayout0031) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind05649_0) certificate0590

private theorem bind05650_0 : Agrees (spec (fastBase 1 6 34) layout0031) scope0233 := by decide

theorem reject05650 : Rejected (base 1 6 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 34) _ validLayout0031) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind05650_0) certificate0236

private theorem bind05651_0 : Agrees (spec (fastBase 1 6 35) layout0031) scope0550 := by decide

theorem reject05651 : Rejected (base 1 6 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 35) _ validLayout0031) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind05651_0) certificate0593

private theorem bind05652_0 : Agrees (spec (fastBase 1 6 36) layout0031) scope0228 := by decide

theorem reject05652 : Rejected (base 1 6 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 36) _ validLayout0031) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind05652_0) certificate0231

private theorem bind05653_0 : Agrees (spec (fastBase 1 6 37) layout0032) scope0209 := by decide

theorem reject05653 : Rejected (base 1 6 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0032 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 37) _ validLayout0032) (by decide) scope0209 (by rw [← fastBase_exact]; exact bind05653_0) certificate0212

private theorem bind05654_0 : Agrees (spec (fastBase 1 6 38) layout0032) scope0214 := by decide

theorem reject05654 : Rejected (base 1 6 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0032 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 38) _ validLayout0032) (by decide) scope0214 (by rw [← fastBase_exact]; exact bind05654_0) certificate0217

private theorem bind05655_0 : Agrees (spec (fastBase 1 6 39) layout0032) scope0215 := by decide

private theorem bind05655_1 : Agrees (spec (fastBase 1 6 39) layout0034) scope0430 := by decide

theorem reject05655 : Rejected (base 1 6 39) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0032 layout0034 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 39) _ validLayout0032) (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 39) _ validLayout0034) (by decide) (by decide) scope0215 scope0430 (by rw [← fastBase_exact]; exact bind05655_0) (by rw [← fastBase_exact]; exact bind05655_1) 4 9 4 9 (by decide) (by decide) 2 3 (by decide) certificate0592 certificate0457 (by decide)

private theorem bind05656_0 : Agrees (spec (fastBase 1 6 40) layout0032) scope0220 := by decide

theorem reject05656 : Rejected (base 1 6 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0032 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 40) _ validLayout0032) (by decide) scope0220 (by rw [← fastBase_exact]; exact bind05656_0) certificate0223

private theorem bind05657_0 : Agrees (spec (fastBase 1 6 41) layout0032) scope0221 := by decide

theorem reject05657 : Rejected (base 1 6 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0032 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 41) _ validLayout0032) (by decide) scope0221 (by rw [← fastBase_exact]; exact bind05657_0) certificate0224

private theorem bind05658_0 : Agrees (spec (fastBase 1 6 42) layout0031) scope0438 := by decide

theorem reject05658 : Rejected (base 1 6 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 42) _ validLayout0031) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind05658_0) certificate0467

private theorem bind05659_0 : Agrees (spec (fastBase 1 6 43) layout0031) scope0438 := by decide

theorem reject05659 : Rejected (base 1 6 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 43) _ validLayout0031) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind05659_0) certificate0467

private theorem bind05660_0 : Agrees (spec (fastBase 1 6 44) layout0031) scope0438 := by decide

theorem reject05660 : Rejected (base 1 6 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 44) _ validLayout0031) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind05660_0) certificate0467

private theorem bind05661_0 : Agrees (spec (fastBase 1 6 45) layout0031) scope0438 := by decide

theorem reject05661 : Rejected (base 1 6 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 45) _ validLayout0031) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind05661_0) certificate0467

private theorem bind05662_0 : Agrees (spec (fastBase 1 6 46) layout0031) scope0438 := by decide

theorem reject05662 : Rejected (base 1 6 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 46) _ validLayout0031) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind05662_0) certificate0467

private theorem bind05663_0 : Agrees (spec (fastBase 1 6 47) layout0031) scope0443 := by decide

theorem reject05663 : Rejected (base 1 6 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 47) _ validLayout0031) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind05663_0) certificate0474

private theorem bind05664_0 : Agrees (spec (fastBase 1 6 48) layout0029) scope0203 := by decide

theorem reject05664 : Rejected (base 1 6 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 48) _ validLayout0029) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind05664_0) certificate0206

private theorem bind05665_0 : Agrees (spec (fastBase 1 6 49) layout0031) scope0441 := by decide

theorem reject05665 : Rejected (base 1 6 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 49) _ validLayout0031) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind05665_0) certificate0470

private theorem bind05666_0 : Agrees (spec (fastBase 1 6 50) layout0031) scope0433 := by decide

theorem reject05666 : Rejected (base 1 6 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 50) _ validLayout0031) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind05666_0) certificate0460

private theorem bind05667_0 : Agrees (spec (fastBase 1 6 51) layout0031) scope0434 := by decide

theorem reject05667 : Rejected (base 1 6 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 51) _ validLayout0031) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind05667_0) certificate0461

private theorem bind05668_0 : Agrees (spec (fastBase 1 6 52) layout0031) scope0232 := by decide

theorem reject05668 : Rejected (base 1 6 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 52) _ validLayout0031) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind05668_0) certificate0235

private theorem bind05669_0 : Agrees (spec (fastBase 1 6 53) layout0031) scope0439 := by decide

theorem reject05669 : Rejected (base 1 6 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 53) _ validLayout0031) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind05669_0) certificate0468

private theorem bind05670_0 : Agrees (spec (fastBase 1 6 54) layout0031) scope0444 := by decide

theorem reject05670 : Rejected (base 1 6 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 54) _ validLayout0031) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind05670_0) certificate0475

private theorem bind05671_0 : Agrees (spec (fastBase 1 6 55) layout0031) scope0443 := by decide

theorem reject05671 : Rejected (base 1 6 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 55) _ validLayout0031) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind05671_0) certificate0474

private theorem bind05672_0 : Agrees (spec (fastBase 1 6 56) layout0031) scope0434 := by decide

theorem reject05672 : Rejected (base 1 6 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 56) _ validLayout0031) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind05672_0) certificate0461

private theorem bind05673_0 : Agrees (spec (fastBase 1 6 57) layout0031) scope0389 := by decide

theorem reject05673 : Rejected (base 1 6 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 57) _ validLayout0031) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind05673_0) certificate0402

private theorem bind05674_0 : Agrees (spec (fastBase 1 6 58) layout0031) scope0433 := by decide

theorem reject05674 : Rejected (base 1 6 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 58) _ validLayout0031) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind05674_0) certificate0460

private theorem bind05675_0 : Agrees (spec (fastBase 1 6 59) layout0031) scope0552 := by decide

theorem reject05675 : Rejected (base 1 6 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 59) _ validLayout0031) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind05675_0) certificate0595

private theorem bind05676_0 : Agrees (spec (fastBase 1 6 60) layout0031) scope0441 := by decide

theorem reject05676 : Rejected (base 1 6 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 60) _ validLayout0031) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind05676_0) certificate0470

private theorem bind05677_0 : Agrees (spec (fastBase 1 6 61) layout0031) scope0236 := by decide

theorem reject05677 : Rejected (base 1 6 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 61) _ validLayout0031) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind05677_0) certificate0239

private theorem bind05678_0 : Agrees (spec (fastBase 1 6 62) layout0031) scope0442 := by decide

theorem reject05678 : Rejected (base 1 6 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 62) _ validLayout0031) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind05678_0) certificate0471

private theorem bind05679_0 : Agrees (spec (fastBase 1 6 63) layout0031) scope0434 := by decide

theorem reject05679 : Rejected (base 1 6 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 63) _ validLayout0031) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind05679_0) certificate0461

private theorem bind05680_0 : Agrees (spec (fastBase 1 6 64) layout0031) scope0441 := by decide

theorem reject05680 : Rejected (base 1 6 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 64) _ validLayout0031) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind05680_0) certificate0470

private theorem bind05681_0 : Agrees (spec (fastBase 1 6 65) layout0031) scope0444 := by decide

theorem reject05681 : Rejected (base 1 6 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 65) _ validLayout0031) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind05681_0) certificate0475

private theorem bind05682_0 : Agrees (spec (fastBase 1 6 66) layout0031) scope0552 := by decide

theorem reject05682 : Rejected (base 1 6 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 66) _ validLayout0031) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind05682_0) certificate0595

private theorem bind05683_0 : Agrees (spec (fastBase 1 6 67) layout0029) scope0191 := by decide

theorem reject05683 : Rejected (base 1 6 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 67) _ validLayout0029) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind05683_0) certificate0194

private theorem bind05684_0 : Agrees (spec (fastBase 1 6 68) layout0031) scope0551 := by decide

theorem reject05684 : Rejected (base 1 6 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 68) _ validLayout0031) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind05684_0) certificate0594

private theorem bind05685_0 : Agrees (spec (fastBase 1 6 69) layout0031) scope0236 := by decide

theorem reject05685 : Rejected (base 1 6 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 69) _ validLayout0031) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind05685_0) certificate0239

private theorem bind05686_0 : Agrees (spec (fastBase 1 6 70) layout0031) scope0433 := by decide

theorem reject05686 : Rejected (base 1 6 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0031 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 70) _ validLayout0031) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind05686_0) certificate0460

private theorem bind05687_0 : Agrees (spec (fastBase 1 6 71) layout0029) scope0203 := by decide

theorem reject05687 : Rejected (base 1 6 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0029 (layoutValid_of_refines _ _ (base_refines_skeleton 1 6 71) _ validLayout0029) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind05687_0) certificate0206

theorem allCases078 : ∀ y : Fin 72, Rejected (base 1 6 y) := by
  intro y
  fin_cases y

  · exact reject05616

  · exact reject05617

  · exact reject05618

  · exact reject05619

  · exact reject05620

  · exact reject05621

  · exact reject05622

  · exact reject05623

  · exact reject05624

  · exact reject05625

  · exact reject05626

  · exact reject05627

  · exact reject05628

  · exact reject05629

  · exact reject05630

  · exact reject05631

  · exact reject05632

  · exact reject05633

  · exact reject05634

  · exact reject05635

  · exact reject05636

  · exact reject05637

  · exact reject05638

  · exact reject05639

  · exact reject05640

  · exact reject05641

  · exact reject05642

  · exact reject05643

  · exact reject05644

  · exact reject05645

  · exact reject05646

  · exact reject05647

  · exact reject05648

  · exact reject05649

  · exact reject05650

  · exact reject05651

  · exact reject05652

  · exact reject05653

  · exact reject05654

  · exact reject05655

  · exact reject05656

  · exact reject05657

  · exact reject05658

  · exact reject05659

  · exact reject05660

  · exact reject05661

  · exact reject05662

  · exact reject05663

  · exact reject05664

  · exact reject05665

  · exact reject05666

  · exact reject05667

  · exact reject05668

  · exact reject05669

  · exact reject05670

  · exact reject05671

  · exact reject05672

  · exact reject05673

  · exact reject05674

  · exact reject05675

  · exact reject05676

  · exact reject05677

  · exact reject05678

  · exact reject05679

  · exact reject05680

  · exact reject05681

  · exact reject05682

  · exact reject05683

  · exact reject05684

  · exact reject05685

  · exact reject05686

  · exact reject05687

end PricingIntegration.RemainingGWitnesses
