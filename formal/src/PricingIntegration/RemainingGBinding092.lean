import PricingIntegration.RemainingGLayouts010

import PricingIntegration.RemainingGLayouts011

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks002

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks023

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind06624_0 : Agrees (spec (fastBase 1 20 0) layout0087) scope0233 := by decide

theorem reject06624 : Rejected (base 1 20 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 0) _ validLayout0087) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind06624_0) certificate0236

private theorem bind06625_0 : Agrees (spec (fastBase 1 20 1) layout0087) scope0548 := by decide

theorem reject06625 : Rejected (base 1 20 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 1) _ validLayout0087) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind06625_0) certificate0590

private theorem bind06626_0 : Agrees (spec (fastBase 1 20 2) layout0087) scope0444 := by decide

theorem reject06626 : Rejected (base 1 20 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 2) _ validLayout0087) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind06626_0) certificate0475

private theorem bind06627_0 : Agrees (spec (fastBase 1 20 3) layout0087) scope0434 := by decide

theorem reject06627 : Rejected (base 1 20 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 3) _ validLayout0087) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind06627_0) certificate0461

private theorem bind06628_0 : Agrees (spec (fastBase 1 20 4) layout0087) scope0438 := by decide

theorem reject06628 : Rejected (base 1 20 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 4) _ validLayout0087) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06628_0) certificate0467

private theorem bind06629_0 : Agrees (spec (fastBase 1 20 5) layout0087) scope0236 := by decide

theorem reject06629 : Rejected (base 1 20 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 5) _ validLayout0087) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind06629_0) certificate0239

private theorem bind06630_0 : Agrees (spec (fastBase 1 20 6) layout0087) scope0232 := by decide

theorem reject06630 : Rejected (base 1 20 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 6) _ validLayout0087) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind06630_0) certificate0235

private theorem bind06631_0 : Agrees (spec (fastBase 1 20 7) layout0086) scope0048 := by decide

private theorem bind06631_1 : Agrees (spec (fastBase 1 20 7) layout0088) scope0033 := by decide

theorem reject06631 : Rejected (base 1 20 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 7) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 7) _ validLayout0088) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind06631_0) (by rw [← fastBase_exact]; exact bind06631_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind06632_0 : Agrees (spec (fastBase 1 20 8) layout0087) scope0547 := by decide

theorem reject06632 : Rejected (base 1 20 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 8) _ validLayout0087) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind06632_0) certificate0589

private theorem bind06633_0 : Agrees (spec (fastBase 1 20 9) layout0086) scope0037 := by decide

theorem reject06633 : Rejected (base 1 20 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 9) _ validLayout0086) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind06633_0) certificate0037

private theorem bind06634_0 : Agrees (spec (fastBase 1 20 10) layout0087) scope0433 := by decide

theorem reject06634 : Rejected (base 1 20 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 10) _ validLayout0087) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind06634_0) certificate0460

private theorem bind06635_0 : Agrees (spec (fastBase 1 20 11) layout0087) scope0441 := by decide

theorem reject06635 : Rejected (base 1 20 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 11) _ validLayout0087) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind06635_0) certificate0470

private theorem bind06636_0 : Agrees (spec (fastBase 1 20 12) layout0087) scope0548 := by decide

theorem reject06636 : Rejected (base 1 20 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 12) _ validLayout0087) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind06636_0) certificate0590

private theorem bind06637_0 : Agrees (spec (fastBase 1 20 13) layout0087) scope0550 := by decide

theorem reject06637 : Rejected (base 1 20 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 13) _ validLayout0087) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind06637_0) certificate0593

private theorem bind06638_0 : Agrees (spec (fastBase 1 20 14) layout0087) scope0228 := by decide

theorem reject06638 : Rejected (base 1 20 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 14) _ validLayout0087) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind06638_0) certificate0231

private theorem bind06639_0 : Agrees (spec (fastBase 1 20 15) layout0087) scope0233 := by decide

theorem reject06639 : Rejected (base 1 20 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 15) _ validLayout0087) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind06639_0) certificate0236

private theorem bind06640_0 : Agrees (spec (fastBase 1 20 16) layout0087) scope0547 := by decide

theorem reject06640 : Rejected (base 1 20 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 16) _ validLayout0087) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind06640_0) certificate0589

private theorem bind06641_0 : Agrees (spec (fastBase 1 20 17) layout0087) scope0233 := by decide

theorem reject06641 : Rejected (base 1 20 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 17) _ validLayout0087) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind06641_0) certificate0236

private theorem bind06642_0 : Agrees (spec (fastBase 1 20 18) layout0087) scope0439 := by decide

theorem reject06642 : Rejected (base 1 20 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 18) _ validLayout0087) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind06642_0) certificate0468

private theorem bind06643_0 : Agrees (spec (fastBase 1 20 19) layout0087) scope0548 := by decide

theorem reject06643 : Rejected (base 1 20 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 19) _ validLayout0087) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind06643_0) certificate0590

private theorem bind06644_0 : Agrees (spec (fastBase 1 20 20) layout0087) scope0232 := by decide

theorem reject06644 : Rejected (base 1 20 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 20) _ validLayout0087) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind06644_0) certificate0235

private theorem bind06645_0 : Agrees (spec (fastBase 1 20 21) layout0086) scope0027 := by decide

theorem reject06645 : Rejected (base 1 20 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 21) _ validLayout0086) (by decide) scope0027 (by rw [← fastBase_exact]; exact bind06645_0) certificate0027

private theorem bind06646_0 : Agrees (spec (fastBase 1 20 22) layout0087) scope0439 := by decide

theorem reject06646 : Rejected (base 1 20 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 22) _ validLayout0087) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind06646_0) certificate0468

private theorem bind06647_0 : Agrees (spec (fastBase 1 20 23) layout0087) scope0444 := by decide

theorem reject06647 : Rejected (base 1 20 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 23) _ validLayout0087) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind06647_0) certificate0475

private theorem bind06648_0 : Agrees (spec (fastBase 1 20 24) layout0087) scope0434 := by decide

theorem reject06648 : Rejected (base 1 20 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 24) _ validLayout0087) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind06648_0) certificate0461

private theorem bind06649_0 : Agrees (spec (fastBase 1 20 25) layout0087) scope0232 := by decide

theorem reject06649 : Rejected (base 1 20 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 25) _ validLayout0087) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind06649_0) certificate0235

private theorem bind06650_0 : Agrees (spec (fastBase 1 20 26) layout0087) scope0443 := by decide

theorem reject06650 : Rejected (base 1 20 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 26) _ validLayout0087) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind06650_0) certificate0474

private theorem bind06651_0 : Agrees (spec (fastBase 1 20 27) layout0087) scope0442 := by decide

theorem reject06651 : Rejected (base 1 20 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 27) _ validLayout0087) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind06651_0) certificate0471

private theorem bind06652_0 : Agrees (spec (fastBase 1 20 28) layout0087) scope0444 := by decide

theorem reject06652 : Rejected (base 1 20 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 28) _ validLayout0087) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind06652_0) certificate0475

private theorem bind06653_0 : Agrees (spec (fastBase 1 20 29) layout0087) scope0552 := by decide

theorem reject06653 : Rejected (base 1 20 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 29) _ validLayout0087) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind06653_0) certificate0595

private theorem bind06654_0 : Agrees (spec (fastBase 1 20 30) layout0087) scope0434 := by decide

theorem reject06654 : Rejected (base 1 20 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 30) _ validLayout0087) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind06654_0) certificate0461

private theorem bind06655_0 : Agrees (spec (fastBase 1 20 31) layout0087) scope0441 := by decide

theorem reject06655 : Rejected (base 1 20 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 31) _ validLayout0087) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind06655_0) certificate0470

private theorem bind06656_0 : Agrees (spec (fastBase 1 20 32) layout0087) scope0438 := by decide

theorem reject06656 : Rejected (base 1 20 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 32) _ validLayout0087) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06656_0) certificate0467

private theorem bind06657_0 : Agrees (spec (fastBase 1 20 33) layout0087) scope0438 := by decide

theorem reject06657 : Rejected (base 1 20 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 33) _ validLayout0087) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06657_0) certificate0467

private theorem bind06658_0 : Agrees (spec (fastBase 1 20 34) layout0087) scope0438 := by decide

theorem reject06658 : Rejected (base 1 20 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 34) _ validLayout0087) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06658_0) certificate0467

private theorem bind06659_0 : Agrees (spec (fastBase 1 20 35) layout0087) scope0438 := by decide

theorem reject06659 : Rejected (base 1 20 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 35) _ validLayout0087) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06659_0) certificate0467

private theorem bind06660_0 : Agrees (spec (fastBase 1 20 36) layout0087) scope0438 := by decide

theorem reject06660 : Rejected (base 1 20 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 36) _ validLayout0087) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06660_0) certificate0467

private theorem bind06661_0 : Agrees (spec (fastBase 1 20 37) layout0087) scope0551 := by decide

theorem reject06661 : Rejected (base 1 20 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 37) _ validLayout0087) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind06661_0) certificate0594

private theorem bind06662_0 : Agrees (spec (fastBase 1 20 38) layout0087) scope0236 := by decide

theorem reject06662 : Rejected (base 1 20 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 38) _ validLayout0087) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind06662_0) certificate0239

private theorem bind06663_0 : Agrees (spec (fastBase 1 20 39) layout0086) scope0031 := by decide

theorem reject06663 : Rejected (base 1 20 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 39) _ validLayout0086) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind06663_0) certificate0031

private theorem bind06664_0 : Agrees (spec (fastBase 1 20 40) layout0086) scope0037 := by decide

theorem reject06664 : Rejected (base 1 20 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 40) _ validLayout0086) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind06664_0) certificate0037

private theorem bind06665_0 : Agrees (spec (fastBase 1 20 41) layout0087) scope0433 := by decide

theorem reject06665 : Rejected (base 1 20 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 41) _ validLayout0087) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind06665_0) certificate0460

private theorem bind06666_0 : Agrees (spec (fastBase 1 20 42) layout0087) scope0548 := by decide

theorem reject06666 : Rejected (base 1 20 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 42) _ validLayout0087) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind06666_0) certificate0590

private theorem bind06667_0 : Agrees (spec (fastBase 1 20 43) layout0087) scope0444 := by decide

theorem reject06667 : Rejected (base 1 20 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 43) _ validLayout0087) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind06667_0) certificate0475

private theorem bind06668_0 : Agrees (spec (fastBase 1 20 44) layout0087) scope0550 := by decide

theorem reject06668 : Rejected (base 1 20 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 44) _ validLayout0087) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind06668_0) certificate0593

private theorem bind06669_0 : Agrees (spec (fastBase 1 20 45) layout0087) scope0232 := by decide

theorem reject06669 : Rejected (base 1 20 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 45) _ validLayout0087) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind06669_0) certificate0235

private theorem bind06670_0 : Agrees (spec (fastBase 1 20 46) layout0087) scope0442 := by decide

theorem reject06670 : Rejected (base 1 20 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 46) _ validLayout0087) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind06670_0) certificate0471

private theorem bind06671_0 : Agrees (spec (fastBase 1 20 47) layout0086) scope0048 := by decide

private theorem bind06671_1 : Agrees (spec (fastBase 1 20 47) layout0088) scope0033 := by decide

theorem reject06671 : Rejected (base 1 20 47) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 47) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 47) _ validLayout0088) (by decide) (by decide) scope0048 scope0033 (by rw [← fastBase_exact]; exact bind06671_0) (by rw [← fastBase_exact]; exact bind06671_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0048 certificate0033 (by decide)

private theorem bind06672_0 : Agrees (spec (fastBase 1 20 48) layout0086) scope0029 := by decide

theorem reject06672 : Rejected (base 1 20 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 48) _ validLayout0086) (by decide) scope0029 (by rw [← fastBase_exact]; exact bind06672_0) certificate0029

private theorem bind06673_0 : Agrees (spec (fastBase 1 20 49) layout0086) scope0032 := by decide

private theorem bind06673_1 : Agrees (spec (fastBase 1 20 49) layout0088) scope0033 := by decide

theorem reject06673 : Rejected (base 1 20 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0086 layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 49) _ validLayout0086) (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 49) _ validLayout0088) (by decide) (by decide) scope0032 scope0033 (by rw [← fastBase_exact]; exact bind06673_0) (by rw [← fastBase_exact]; exact bind06673_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0032 certificate0033 (by decide)

private theorem bind06674_0 : Agrees (spec (fastBase 1 20 50) layout0086) scope0042 := by decide

theorem reject06674 : Rejected (base 1 20 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 50) _ validLayout0086) (by decide) scope0042 (by rw [← fastBase_exact]; exact bind06674_0) certificate0042

private theorem bind06675_0 : Agrees (spec (fastBase 1 20 51) layout0086) scope0043 := by decide

theorem reject06675 : Rejected (base 1 20 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 51) _ validLayout0086) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind06675_0) certificate0043

private theorem bind06676_0 : Agrees (spec (fastBase 1 20 52) layout0087) scope0233 := by decide

theorem reject06676 : Rejected (base 1 20 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 52) _ validLayout0087) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind06676_0) certificate0236

private theorem bind06677_0 : Agrees (spec (fastBase 1 20 53) layout0087) scope0547 := by decide

theorem reject06677 : Rejected (base 1 20 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 53) _ validLayout0087) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind06677_0) certificate0589

private theorem bind06678_0 : Agrees (spec (fastBase 1 20 54) layout0086) scope0036 := by decide

theorem reject06678 : Rejected (base 1 20 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 54) _ validLayout0086) (by decide) scope0036 (by rw [← fastBase_exact]; exact bind06678_0) certificate0036

private theorem bind06679_0 : Agrees (spec (fastBase 1 20 55) layout0086) scope0037 := by decide

theorem reject06679 : Rejected (base 1 20 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 55) _ validLayout0086) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind06679_0) certificate0037

private theorem bind06680_0 : Agrees (spec (fastBase 1 20 56) layout0087) scope0551 := by decide

theorem reject06680 : Rejected (base 1 20 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 56) _ validLayout0087) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind06680_0) certificate0594

private theorem bind06681_0 : Agrees (spec (fastBase 1 20 57) layout0087) scope0228 := by decide

theorem reject06681 : Rejected (base 1 20 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 57) _ validLayout0087) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind06681_0) certificate0231

private theorem bind06682_0 : Agrees (spec (fastBase 1 20 58) layout0087) scope0236 := by decide

theorem reject06682 : Rejected (base 1 20 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 58) _ validLayout0087) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind06682_0) certificate0239

private theorem bind06683_0 : Agrees (spec (fastBase 1 20 59) layout0087) scope0547 := by decide

theorem reject06683 : Rejected (base 1 20 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 59) _ validLayout0087) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind06683_0) certificate0589

private theorem bind06684_0 : Agrees (spec (fastBase 1 20 60) layout0088) scope0369 := by decide

theorem reject06684 : Rejected (base 1 20 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0088 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 60) _ validLayout0088) (by decide) scope0369 (by rw [← fastBase_exact]; exact bind06684_0) certificate0377

private theorem bind06685_0 : Agrees (spec (fastBase 1 20 61) layout0087) scope0389 := by decide

theorem reject06685 : Rejected (base 1 20 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 61) _ validLayout0087) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind06685_0) certificate0402

private theorem bind06686_0 : Agrees (spec (fastBase 1 20 62) layout0087) scope0552 := by decide

theorem reject06686 : Rejected (base 1 20 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 62) _ validLayout0087) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind06686_0) certificate0595

private theorem bind06687_0 : Agrees (spec (fastBase 1 20 63) layout0087) scope0236 := by decide

theorem reject06687 : Rejected (base 1 20 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 63) _ validLayout0087) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind06687_0) certificate0239

private theorem bind06688_0 : Agrees (spec (fastBase 1 20 64) layout0087) scope0433 := by decide

theorem reject06688 : Rejected (base 1 20 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 64) _ validLayout0087) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind06688_0) certificate0460

private theorem bind06689_0 : Agrees (spec (fastBase 1 20 65) layout0087) scope0389 := by decide

theorem reject06689 : Rejected (base 1 20 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 65) _ validLayout0087) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind06689_0) certificate0402

private theorem bind06690_0 : Agrees (spec (fastBase 1 20 66) layout0087) scope0441 := by decide

theorem reject06690 : Rejected (base 1 20 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 66) _ validLayout0087) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind06690_0) certificate0470

private theorem bind06691_0 : Agrees (spec (fastBase 1 20 67) layout0087) scope0434 := by decide

theorem reject06691 : Rejected (base 1 20 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 67) _ validLayout0087) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind06691_0) certificate0461

private theorem bind06692_0 : Agrees (spec (fastBase 1 20 68) layout0087) scope0441 := by decide

theorem reject06692 : Rejected (base 1 20 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 68) _ validLayout0087) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind06692_0) certificate0470

private theorem bind06693_0 : Agrees (spec (fastBase 1 20 69) layout0087) scope0443 := by decide

theorem reject06693 : Rejected (base 1 20 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 69) _ validLayout0087) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind06693_0) certificate0474

private theorem bind06694_0 : Agrees (spec (fastBase 1 20 70) layout0086) scope0050 := by decide

theorem reject06694 : Rejected (base 1 20 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0086 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 70) _ validLayout0086) (by decide) scope0050 (by rw [← fastBase_exact]; exact bind06694_0) certificate0052

private theorem bind06695_0 : Agrees (spec (fastBase 1 20 71) layout0087) scope0433 := by decide

theorem reject06695 : Rejected (base 1 20 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0087 (layoutValid_of_refines _ _ (base_refines_skeleton 1 20 71) _ validLayout0087) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind06695_0) certificate0460

theorem allCases092 : ∀ y : Fin 72, Rejected (base 1 20 y) := by
  intro y
  fin_cases y

  · exact reject06624

  · exact reject06625

  · exact reject06626

  · exact reject06627

  · exact reject06628

  · exact reject06629

  · exact reject06630

  · exact reject06631

  · exact reject06632

  · exact reject06633

  · exact reject06634

  · exact reject06635

  · exact reject06636

  · exact reject06637

  · exact reject06638

  · exact reject06639

  · exact reject06640

  · exact reject06641

  · exact reject06642

  · exact reject06643

  · exact reject06644

  · exact reject06645

  · exact reject06646

  · exact reject06647

  · exact reject06648

  · exact reject06649

  · exact reject06650

  · exact reject06651

  · exact reject06652

  · exact reject06653

  · exact reject06654

  · exact reject06655

  · exact reject06656

  · exact reject06657

  · exact reject06658

  · exact reject06659

  · exact reject06660

  · exact reject06661

  · exact reject06662

  · exact reject06663

  · exact reject06664

  · exact reject06665

  · exact reject06666

  · exact reject06667

  · exact reject06668

  · exact reject06669

  · exact reject06670

  · exact reject06671

  · exact reject06672

  · exact reject06673

  · exact reject06674

  · exact reject06675

  · exact reject06676

  · exact reject06677

  · exact reject06678

  · exact reject06679

  · exact reject06680

  · exact reject06681

  · exact reject06682

  · exact reject06683

  · exact reject06684

  · exact reject06685

  · exact reject06686

  · exact reject06687

  · exact reject06688

  · exact reject06689

  · exact reject06690

  · exact reject06691

  · exact reject06692

  · exact reject06693

  · exact reject06694

  · exact reject06695

end PricingIntegration.RemainingGWitnesses
