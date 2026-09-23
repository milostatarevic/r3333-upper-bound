import PricingIntegration.RemainingGLayouts016

import PricingIntegration.RemainingGLayouts017

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks007

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks039


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind07632_0 : Agrees (spec (fastBase 1 34 0) layout0135) scope0534 := by decide

theorem reject07632 : Rejected (base 1 34 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 0) _ validLayout0135) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind07632_0) certificate0576

private theorem bind07633_0 : Agrees (spec (fastBase 1 34 1) layout0135) scope0393 := by decide

theorem reject07633 : Rejected (base 1 34 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 1) _ validLayout0135) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind07633_0) certificate0406

private theorem bind07634_0 : Agrees (spec (fastBase 1 34 2) layout0135) scope0535 := by decide

theorem reject07634 : Rejected (base 1 34 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 2) _ validLayout0135) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind07634_0) certificate0577

private theorem bind07635_0 : Agrees (spec (fastBase 1 34 3) layout0135) scope0536 := by decide

theorem reject07635 : Rejected (base 1 34 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 3) _ validLayout0135) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind07635_0) certificate0578

private theorem bind07636_0 : Agrees (spec (fastBase 1 34 4) layout0135) scope0392 := by decide

theorem reject07636 : Rejected (base 1 34 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 4) _ validLayout0135) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind07636_0) certificate0405

private theorem bind07637_0 : Agrees (spec (fastBase 1 34 5) layout0135) scope0537 := by decide

theorem reject07637 : Rejected (base 1 34 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 5) _ validLayout0135) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind07637_0) certificate0579

private theorem bind07638_0 : Agrees (spec (fastBase 1 34 6) layout0134) scope0114 := by decide

private theorem bind07638_1 : Agrees (spec (fastBase 1 34 6) layout0136) scope0538 := by decide

theorem reject07638 : Rejected (base 1 34 6) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 6) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 6) _ validLayout0136) (by decide) (by decide) scope0114 scope0538 (by rw [← fastBase_exact]; exact bind07638_0) (by rw [← fastBase_exact]; exact bind07638_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0629 (by decide)

private theorem bind07639_0 : Agrees (spec (fastBase 1 34 7) layout0134) scope0116 := by decide

private theorem bind07639_1 : Agrees (spec (fastBase 1 34 7) layout0136) scope0539 := by decide

theorem reject07639 : Rejected (base 1 34 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 7) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 7) _ validLayout0136) (by decide) (by decide) scope0116 scope0539 (by rw [← fastBase_exact]; exact bind07639_0) (by rw [← fastBase_exact]; exact bind07639_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0630 (by decide)

private theorem bind07640_0 : Agrees (spec (fastBase 1 34 8) layout0135) scope0399 := by decide

theorem reject07640 : Rejected (base 1 34 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 8) _ validLayout0135) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind07640_0) certificate0412

private theorem bind07641_0 : Agrees (spec (fastBase 1 34 9) layout0135) scope0400 := by decide

theorem reject07641 : Rejected (base 1 34 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 9) _ validLayout0135) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind07641_0) certificate0413

private theorem bind07642_0 : Agrees (spec (fastBase 1 34 10) layout0135) scope0133 := by decide

theorem reject07642 : Rejected (base 1 34 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 10) _ validLayout0135) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind07642_0) certificate0136

private theorem bind07643_0 : Agrees (spec (fastBase 1 34 11) layout0135) scope0137 := by decide

theorem reject07643 : Rejected (base 1 34 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 11) _ validLayout0135) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind07643_0) certificate0140

private theorem bind07644_0 : Agrees (spec (fastBase 1 34 12) layout0135) scope0540 := by decide

theorem reject07644 : Rejected (base 1 34 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 12) _ validLayout0135) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind07644_0) certificate0582

private theorem bind07645_0 : Agrees (spec (fastBase 1 34 13) layout0135) scope0535 := by decide

theorem reject07645 : Rejected (base 1 34 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 13) _ validLayout0135) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind07645_0) certificate0577

private theorem bind07646_0 : Agrees (spec (fastBase 1 34 14) layout0135) scope0537 := by decide

theorem reject07646 : Rejected (base 1 34 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 14) _ validLayout0135) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind07646_0) certificate0579

private theorem bind07647_0 : Agrees (spec (fastBase 1 34 15) layout0135) scope0534 := by decide

theorem reject07647 : Rejected (base 1 34 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 15) _ validLayout0135) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind07647_0) certificate0576

private theorem bind07648_0 : Agrees (spec (fastBase 1 34 16) layout0135) scope0541 := by decide

theorem reject07648 : Rejected (base 1 34 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 16) _ validLayout0135) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind07648_0) certificate0583

private theorem bind07649_0 : Agrees (spec (fastBase 1 34 17) layout0135) scope0542 := by decide

theorem reject07649 : Rejected (base 1 34 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 17) _ validLayout0135) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind07649_0) certificate0584

private theorem bind07650_0 : Agrees (spec (fastBase 1 34 18) layout0135) scope0536 := by decide

theorem reject07650 : Rejected (base 1 34 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 18) _ validLayout0135) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind07650_0) certificate0578

private theorem bind07651_0 : Agrees (spec (fastBase 1 34 19) layout0135) scope0393 := by decide

theorem reject07651 : Rejected (base 1 34 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 19) _ validLayout0135) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind07651_0) certificate0406

private theorem bind07652_0 : Agrees (spec (fastBase 1 34 20) layout0134) scope0109 := by decide

theorem reject07652 : Rejected (base 1 34 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 20) _ validLayout0134) (by decide) scope0109 (by rw [← fastBase_exact]; exact bind07652_0) certificate0112

private theorem bind07653_0 : Agrees (spec (fastBase 1 34 21) layout0135) scope0400 := by decide

theorem reject07653 : Rejected (base 1 34 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 21) _ validLayout0135) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind07653_0) certificate0413

private theorem bind07654_0 : Agrees (spec (fastBase 1 34 22) layout0135) scope0534 := by decide

theorem reject07654 : Rejected (base 1 34 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 22) _ validLayout0135) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind07654_0) certificate0576

private theorem bind07655_0 : Agrees (spec (fastBase 1 34 23) layout0135) scope0535 := by decide

theorem reject07655 : Rejected (base 1 34 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 23) _ validLayout0135) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind07655_0) certificate0577

private theorem bind07656_0 : Agrees (spec (fastBase 1 34 24) layout0135) scope0395 := by decide

theorem reject07656 : Rejected (base 1 34 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 24) _ validLayout0135) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind07656_0) certificate0408

private theorem bind07657_0 : Agrees (spec (fastBase 1 34 25) layout0134) scope0110 := by decide

theorem reject07657 : Rejected (base 1 34 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 25) _ validLayout0134) (by decide) scope0110 (by rw [← fastBase_exact]; exact bind07657_0) certificate0113

private theorem bind07658_0 : Agrees (spec (fastBase 1 34 26) layout0135) scope0133 := by decide

theorem reject07658 : Rejected (base 1 34 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 26) _ validLayout0135) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind07658_0) certificate0136

private theorem bind07659_0 : Agrees (spec (fastBase 1 34 27) layout0135) scope0393 := by decide

theorem reject07659 : Rejected (base 1 34 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 27) _ validLayout0135) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind07659_0) certificate0406

private theorem bind07660_0 : Agrees (spec (fastBase 1 34 28) layout0135) scope0540 := by decide

theorem reject07660 : Rejected (base 1 34 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 28) _ validLayout0135) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind07660_0) certificate0582

private theorem bind07661_0 : Agrees (spec (fastBase 1 34 29) layout0135) scope0537 := by decide

theorem reject07661 : Rejected (base 1 34 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 29) _ validLayout0135) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind07661_0) certificate0579

private theorem bind07662_0 : Agrees (spec (fastBase 1 34 30) layout0135) scope0536 := by decide

theorem reject07662 : Rejected (base 1 34 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 30) _ validLayout0135) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind07662_0) certificate0578

private theorem bind07663_0 : Agrees (spec (fastBase 1 34 31) layout0135) scope0543 := by decide

theorem reject07663 : Rejected (base 1 34 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 31) _ validLayout0135) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind07663_0) certificate0585

private theorem bind07664_0 : Agrees (spec (fastBase 1 34 32) layout0135) scope0392 := by decide

theorem reject07664 : Rejected (base 1 34 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 32) _ validLayout0135) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind07664_0) certificate0405

private theorem bind07665_0 : Agrees (spec (fastBase 1 34 33) layout0135) scope0392 := by decide

theorem reject07665 : Rejected (base 1 34 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 33) _ validLayout0135) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind07665_0) certificate0405

private theorem bind07666_0 : Agrees (spec (fastBase 1 34 34) layout0135) scope0392 := by decide

theorem reject07666 : Rejected (base 1 34 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 34) _ validLayout0135) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind07666_0) certificate0405

private theorem bind07667_0 : Agrees (spec (fastBase 1 34 35) layout0135) scope0392 := by decide

theorem reject07667 : Rejected (base 1 34 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 35) _ validLayout0135) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind07667_0) certificate0405

private theorem bind07668_0 : Agrees (spec (fastBase 1 34 36) layout0135) scope0392 := by decide

theorem reject07668 : Rejected (base 1 34 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 36) _ validLayout0135) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind07668_0) certificate0405

private theorem bind07669_0 : Agrees (spec (fastBase 1 34 37) layout0135) scope0534 := by decide

theorem reject07669 : Rejected (base 1 34 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 37) _ validLayout0135) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind07669_0) certificate0576

private theorem bind07670_0 : Agrees (spec (fastBase 1 34 38) layout0135) scope0537 := by decide

theorem reject07670 : Rejected (base 1 34 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 38) _ validLayout0135) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind07670_0) certificate0579

private theorem bind07671_0 : Agrees (spec (fastBase 1 34 39) layout0135) scope0536 := by decide

theorem reject07671 : Rejected (base 1 34 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 39) _ validLayout0135) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind07671_0) certificate0578

private theorem bind07672_0 : Agrees (spec (fastBase 1 34 40) layout0135) scope0542 := by decide

theorem reject07672 : Rejected (base 1 34 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 40) _ validLayout0135) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind07672_0) certificate0584

private theorem bind07673_0 : Agrees (spec (fastBase 1 34 41) layout0135) scope0395 := by decide

theorem reject07673 : Rejected (base 1 34 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 41) _ validLayout0135) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind07673_0) certificate0408

private theorem bind07674_0 : Agrees (spec (fastBase 1 34 42) layout0135) scope0396 := by decide

theorem reject07674 : Rejected (base 1 34 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 42) _ validLayout0135) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind07674_0) certificate0409

private theorem bind07675_0 : Agrees (spec (fastBase 1 34 43) layout0135) scope0544 := by decide

theorem reject07675 : Rejected (base 1 34 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 43) _ validLayout0135) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind07675_0) certificate0586

private theorem bind07676_0 : Agrees (spec (fastBase 1 34 44) layout0135) scope0399 := by decide

theorem reject07676 : Rejected (base 1 34 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 44) _ validLayout0135) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind07676_0) certificate0412

private theorem bind07677_0 : Agrees (spec (fastBase 1 34 45) layout0134) scope0116 := by decide

private theorem bind07677_1 : Agrees (spec (fastBase 1 34 45) layout0136) scope0538 := by decide

theorem reject07677 : Rejected (base 1 34 45) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 45) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 45) _ validLayout0136) (by decide) (by decide) scope0116 scope0538 (by rw [← fastBase_exact]; exact bind07677_0) (by rw [← fastBase_exact]; exact bind07677_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0119 certificate0629 (by decide)

private theorem bind07678_0 : Agrees (spec (fastBase 1 34 46) layout0135) scope0137 := by decide

theorem reject07678 : Rejected (base 1 34 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 46) _ validLayout0135) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind07678_0) certificate0140

private theorem bind07679_0 : Agrees (spec (fastBase 1 34 47) layout0134) scope0134 := by decide

theorem reject07679 : Rejected (base 1 34 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 47) _ validLayout0134) (by decide) scope0134 (by rw [← fastBase_exact]; exact bind07679_0) certificate0137

private theorem bind07680_0 : Agrees (spec (fastBase 1 34 48) layout0134) scope0135 := by decide

theorem reject07680 : Rejected (base 1 34 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 48) _ validLayout0134) (by decide) scope0135 (by rw [← fastBase_exact]; exact bind07680_0) certificate0138

private theorem bind07681_0 : Agrees (spec (fastBase 1 34 49) layout0134) scope0114 := by decide

private theorem bind07681_1 : Agrees (spec (fastBase 1 34 49) layout0136) scope0539 := by decide

theorem reject07681 : Rejected (base 1 34 49) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0134 layout0136 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 49) _ validLayout0134) (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 49) _ validLayout0136) (by decide) (by decide) scope0114 scope0539 (by rw [← fastBase_exact]; exact bind07681_0) (by rw [← fastBase_exact]; exact bind07681_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0117 certificate0630 (by decide)

private theorem bind07682_0 : Agrees (spec (fastBase 1 34 50) layout0134) scope0119 := by decide

theorem reject07682 : Rejected (base 1 34 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 50) _ validLayout0134) (by decide) scope0119 (by rw [← fastBase_exact]; exact bind07682_0) certificate0122

private theorem bind07683_0 : Agrees (spec (fastBase 1 34 51) layout0137) scope0399 := by decide

theorem reject07683 : Rejected (base 1 34 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 51) _ validLayout0137) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind07683_0) certificate0412

private theorem bind07684_0 : Agrees (spec (fastBase 1 34 52) layout0134) scope0118 := by decide

theorem reject07684 : Rejected (base 1 34 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 52) _ validLayout0134) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind07684_0) certificate0121

private theorem bind07685_0 : Agrees (spec (fastBase 1 34 53) layout0135) scope0399 := by decide

theorem reject07685 : Rejected (base 1 34 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 53) _ validLayout0135) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind07685_0) certificate0412

private theorem bind07686_0 : Agrees (spec (fastBase 1 34 54) layout0134) scope0118 := by decide

theorem reject07686 : Rejected (base 1 34 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 54) _ validLayout0134) (by decide) scope0118 (by rw [← fastBase_exact]; exact bind07686_0) certificate0121

private theorem bind07687_0 : Agrees (spec (fastBase 1 34 55) layout0135) scope0394 := by decide

theorem reject07687 : Rejected (base 1 34 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 55) _ validLayout0135) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind07687_0) certificate0407

private theorem bind07688_0 : Agrees (spec (fastBase 1 34 56) layout0135) scope0133 := by decide

theorem reject07688 : Rejected (base 1 34 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 56) _ validLayout0135) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind07688_0) certificate0136

private theorem bind07689_0 : Agrees (spec (fastBase 1 34 57) layout0135) scope0393 := by decide

theorem reject07689 : Rejected (base 1 34 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 57) _ validLayout0135) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind07689_0) certificate0406

private theorem bind07690_0 : Agrees (spec (fastBase 1 34 58) layout0135) scope0543 := by decide

theorem reject07690 : Rejected (base 1 34 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 58) _ validLayout0135) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind07690_0) certificate0585

private theorem bind07691_0 : Agrees (spec (fastBase 1 34 59) layout0135) scope0396 := by decide

theorem reject07691 : Rejected (base 1 34 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 59) _ validLayout0135) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind07691_0) certificate0409

private theorem bind07692_0 : Agrees (spec (fastBase 1 34 60) layout0135) scope0400 := by decide

theorem reject07692 : Rejected (base 1 34 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 60) _ validLayout0135) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind07692_0) certificate0413

private theorem bind07693_0 : Agrees (spec (fastBase 1 34 61) layout0135) scope0137 := by decide

theorem reject07693 : Rejected (base 1 34 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 61) _ validLayout0135) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind07693_0) certificate0140

private theorem bind07694_0 : Agrees (spec (fastBase 1 34 62) layout0135) scope0535 := by decide

theorem reject07694 : Rejected (base 1 34 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 62) _ validLayout0135) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind07694_0) certificate0577

private theorem bind07695_0 : Agrees (spec (fastBase 1 34 63) layout0135) scope0541 := by decide

theorem reject07695 : Rejected (base 1 34 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 63) _ validLayout0135) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind07695_0) certificate0583

private theorem bind07696_0 : Agrees (spec (fastBase 1 34 64) layout0135) scope0133 := by decide

theorem reject07696 : Rejected (base 1 34 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 64) _ validLayout0135) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind07696_0) certificate0136

private theorem bind07697_0 : Agrees (spec (fastBase 1 34 65) layout0135) scope0399 := by decide

theorem reject07697 : Rejected (base 1 34 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 65) _ validLayout0135) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind07697_0) certificate0412

private theorem bind07698_0 : Agrees (spec (fastBase 1 34 66) layout0135) scope0544 := by decide

theorem reject07698 : Rejected (base 1 34 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 66) _ validLayout0135) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind07698_0) certificate0586

private theorem bind07699_0 : Agrees (spec (fastBase 1 34 67) layout0134) scope0121 := by decide

theorem reject07699 : Rejected (base 1 34 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0134 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 67) _ validLayout0134) (by decide) scope0121 (by rw [← fastBase_exact]; exact bind07699_0) certificate0124

private theorem bind07700_0 : Agrees (spec (fastBase 1 34 68) layout0135) scope0137 := by decide

theorem reject07700 : Rejected (base 1 34 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 68) _ validLayout0135) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind07700_0) certificate0140

private theorem bind07701_0 : Agrees (spec (fastBase 1 34 69) layout0137) scope0400 := by decide

theorem reject07701 : Rejected (base 1 34 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0137 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 69) _ validLayout0137) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind07701_0) certificate0413

private theorem bind07702_0 : Agrees (spec (fastBase 1 34 70) layout0135) scope0400 := by decide

theorem reject07702 : Rejected (base 1 34 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 70) _ validLayout0135) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind07702_0) certificate0413

private theorem bind07703_0 : Agrees (spec (fastBase 1 34 71) layout0135) scope0394 := by decide

theorem reject07703 : Rejected (base 1 34 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0135 (layoutValid_of_refines _ _ (base_refines_skeleton 1 34 71) _ validLayout0135) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind07703_0) certificate0407

theorem allCases106 : ∀ y : Fin 72, Rejected (base 1 34 y) := by
  intro y
  fin_cases y

  · exact reject07632

  · exact reject07633

  · exact reject07634

  · exact reject07635

  · exact reject07636

  · exact reject07637

  · exact reject07638

  · exact reject07639

  · exact reject07640

  · exact reject07641

  · exact reject07642

  · exact reject07643

  · exact reject07644

  · exact reject07645

  · exact reject07646

  · exact reject07647

  · exact reject07648

  · exact reject07649

  · exact reject07650

  · exact reject07651

  · exact reject07652

  · exact reject07653

  · exact reject07654

  · exact reject07655

  · exact reject07656

  · exact reject07657

  · exact reject07658

  · exact reject07659

  · exact reject07660

  · exact reject07661

  · exact reject07662

  · exact reject07663

  · exact reject07664

  · exact reject07665

  · exact reject07666

  · exact reject07667

  · exact reject07668

  · exact reject07669

  · exact reject07670

  · exact reject07671

  · exact reject07672

  · exact reject07673

  · exact reject07674

  · exact reject07675

  · exact reject07676

  · exact reject07677

  · exact reject07678

  · exact reject07679

  · exact reject07680

  · exact reject07681

  · exact reject07682

  · exact reject07683

  · exact reject07684

  · exact reject07685

  · exact reject07686

  · exact reject07687

  · exact reject07688

  · exact reject07689

  · exact reject07690

  · exact reject07691

  · exact reject07692

  · exact reject07693

  · exact reject07694

  · exact reject07695

  · exact reject07696

  · exact reject07697

  · exact reject07698

  · exact reject07699

  · exact reject07700

  · exact reject07701

  · exact reject07702

  · exact reject07703

end PricingIntegration.RemainingGWitnesses
