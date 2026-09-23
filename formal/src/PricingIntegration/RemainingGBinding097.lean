import PricingIntegration.RemainingGLayouts012

import PricingIntegration.RemainingGLayouts013

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks004

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks024

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks033

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind06984_0 : Agrees (spec (fastBase 1 25 0) layout0103) scope0548 := by decide

theorem reject06984 : Rejected (base 1 25 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 0) _ validLayout0103) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind06984_0) certificate0590

private theorem bind06985_0 : Agrees (spec (fastBase 1 25 1) layout0103) scope0233 := by decide

theorem reject06985 : Rejected (base 1 25 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 1) _ validLayout0103) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind06985_0) certificate0236

private theorem bind06986_0 : Agrees (spec (fastBase 1 25 2) layout0103) scope0232 := by decide

theorem reject06986 : Rejected (base 1 25 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 2) _ validLayout0103) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind06986_0) certificate0235

private theorem bind06987_0 : Agrees (spec (fastBase 1 25 3) layout0104) scope0062 := by decide

private theorem bind06987_1 : Agrees (spec (fastBase 1 25 3) layout0105) scope0057 := by decide

theorem reject06987 : Rejected (base 1 25 3) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 3) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 3) _ validLayout0105) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind06987_0) (by rw [← fastBase_exact]; exact bind06987_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind06988_0 : Agrees (spec (fastBase 1 25 4) layout0103) scope0547 := by decide

theorem reject06988 : Rejected (base 1 25 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 4) _ validLayout0103) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind06988_0) certificate0589

private theorem bind06989_0 : Agrees (spec (fastBase 1 25 5) layout0104) scope0065 := by decide

theorem reject06989 : Rejected (base 1 25 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 5) _ validLayout0104) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind06989_0) certificate0067

private theorem bind06990_0 : Agrees (spec (fastBase 1 25 6) layout0103) scope0444 := by decide

theorem reject06990 : Rejected (base 1 25 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 6) _ validLayout0103) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind06990_0) certificate0475

private theorem bind06991_0 : Agrees (spec (fastBase 1 25 7) layout0103) scope0434 := by decide

theorem reject06991 : Rejected (base 1 25 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 7) _ validLayout0103) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind06991_0) certificate0461

private theorem bind06992_0 : Agrees (spec (fastBase 1 25 8) layout0103) scope0438 := by decide

theorem reject06992 : Rejected (base 1 25 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 8) _ validLayout0103) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind06992_0) certificate0467

private theorem bind06993_0 : Agrees (spec (fastBase 1 25 9) layout0103) scope0236 := by decide

theorem reject06993 : Rejected (base 1 25 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 9) _ validLayout0103) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind06993_0) certificate0239

private theorem bind06994_0 : Agrees (spec (fastBase 1 25 10) layout0103) scope0441 := by decide

theorem reject06994 : Rejected (base 1 25 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 10) _ validLayout0103) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind06994_0) certificate0470

private theorem bind06995_0 : Agrees (spec (fastBase 1 25 11) layout0103) scope0433 := by decide

theorem reject06995 : Rejected (base 1 25 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 11) _ validLayout0103) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind06995_0) certificate0460

private theorem bind06996_0 : Agrees (spec (fastBase 1 25 12) layout0103) scope0233 := by decide

theorem reject06996 : Rejected (base 1 25 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 12) _ validLayout0103) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind06996_0) certificate0236

private theorem bind06997_0 : Agrees (spec (fastBase 1 25 13) layout0103) scope0232 := by decide

theorem reject06997 : Rejected (base 1 25 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 13) _ validLayout0103) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind06997_0) certificate0235

private theorem bind06998_0 : Agrees (spec (fastBase 1 25 14) layout0104) scope0069 := by decide

theorem reject06998 : Rejected (base 1 25 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 14) _ validLayout0104) (by decide) scope0069 (by rw [← fastBase_exact]; exact bind06998_0) certificate0071

private theorem bind06999_0 : Agrees (spec (fastBase 1 25 15) layout0103) scope0439 := by decide

theorem reject06999 : Rejected (base 1 25 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 15) _ validLayout0103) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind06999_0) certificate0468

private theorem bind07000_0 : Agrees (spec (fastBase 1 25 16) layout0103) scope0548 := by decide

theorem reject07000 : Rejected (base 1 25 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 16) _ validLayout0103) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind07000_0) certificate0590

private theorem bind07001_0 : Agrees (spec (fastBase 1 25 17) layout0103) scope0548 := by decide

theorem reject07001 : Rejected (base 1 25 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 17) _ validLayout0103) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind07001_0) certificate0590

private theorem bind07002_0 : Agrees (spec (fastBase 1 25 18) layout0103) scope0233 := by decide

theorem reject07002 : Rejected (base 1 25 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 18) _ validLayout0103) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind07002_0) certificate0236

private theorem bind07003_0 : Agrees (spec (fastBase 1 25 19) layout0103) scope0547 := by decide

theorem reject07003 : Rejected (base 1 25 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 19) _ validLayout0103) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind07003_0) certificate0589

private theorem bind07004_0 : Agrees (spec (fastBase 1 25 20) layout0103) scope0550 := by decide

theorem reject07004 : Rejected (base 1 25 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 20) _ validLayout0103) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind07004_0) certificate0593

private theorem bind07005_0 : Agrees (spec (fastBase 1 25 21) layout0103) scope0228 := by decide

theorem reject07005 : Rejected (base 1 25 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 21) _ validLayout0103) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind07005_0) certificate0231

private theorem bind07006_0 : Agrees (spec (fastBase 1 25 22) layout0103) scope0548 := by decide

theorem reject07006 : Rejected (base 1 25 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 22) _ validLayout0103) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind07006_0) certificate0590

private theorem bind07007_0 : Agrees (spec (fastBase 1 25 23) layout0103) scope0550 := by decide

theorem reject07007 : Rejected (base 1 25 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 23) _ validLayout0103) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind07007_0) certificate0593

private theorem bind07008_0 : Agrees (spec (fastBase 1 25 24) layout0103) scope0232 := by decide

theorem reject07008 : Rejected (base 1 25 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 24) _ validLayout0103) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind07008_0) certificate0235

private theorem bind07009_0 : Agrees (spec (fastBase 1 25 25) layout0103) scope0444 := by decide

theorem reject07009 : Rejected (base 1 25 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 25) _ validLayout0103) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind07009_0) certificate0475

private theorem bind07010_0 : Agrees (spec (fastBase 1 25 26) layout0103) scope0442 := by decide

theorem reject07010 : Rejected (base 1 25 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 26) _ validLayout0103) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind07010_0) certificate0471

private theorem bind07011_0 : Agrees (spec (fastBase 1 25 27) layout0104) scope0054 := by decide

theorem reject07011 : Rejected (base 1 25 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 27) _ validLayout0104) (by decide) scope0054 (by rw [← fastBase_exact]; exact bind07011_0) certificate0056

private theorem bind07012_0 : Agrees (spec (fastBase 1 25 28) layout0104) scope0061 := by decide

theorem reject07012 : Rejected (base 1 25 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 28) _ validLayout0104) (by decide) scope0061 (by rw [← fastBase_exact]; exact bind07012_0) certificate0063

private theorem bind07013_0 : Agrees (spec (fastBase 1 25 29) layout0105) scope0377 := by decide

theorem reject07013 : Rejected (base 1 25 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 29) _ validLayout0105) (by decide) scope0377 (by rw [← fastBase_exact]; exact bind07013_0) certificate0386

private theorem bind07014_0 : Agrees (spec (fastBase 1 25 30) layout0104) scope0062 := by decide

private theorem bind07014_1 : Agrees (spec (fastBase 1 25 30) layout0105) scope0063 := by decide

theorem reject07014 : Rejected (base 1 25 30) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 30) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 30) _ validLayout0105) (by decide) (by decide) scope0062 scope0063 (by rw [← fastBase_exact]; exact bind07014_0) (by rw [← fastBase_exact]; exact bind07014_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0065 (by decide)

private theorem bind07015_0 : Agrees (spec (fastBase 1 25 31) layout0104) scope0062 := by decide

private theorem bind07015_1 : Agrees (spec (fastBase 1 25 31) layout0105) scope0057 := by decide

theorem reject07015 : Rejected (base 1 25 31) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0104 layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 31) _ validLayout0104) (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 31) _ validLayout0105) (by decide) (by decide) scope0062 scope0057 (by rw [← fastBase_exact]; exact bind07015_0) (by rw [← fastBase_exact]; exact bind07015_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0064 certificate0059 (by decide)

private theorem bind07016_0 : Agrees (spec (fastBase 1 25 32) layout0103) scope0233 := by decide

theorem reject07016 : Rejected (base 1 25 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 32) _ validLayout0103) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind07016_0) certificate0236

private theorem bind07017_0 : Agrees (spec (fastBase 1 25 33) layout0104) scope0071 := by decide

theorem reject07017 : Rejected (base 1 25 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 33) _ validLayout0104) (by decide) scope0071 (by rw [← fastBase_exact]; exact bind07017_0) certificate0073

private theorem bind07018_0 : Agrees (spec (fastBase 1 25 34) layout0104) scope0065 := by decide

theorem reject07018 : Rejected (base 1 25 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 34) _ validLayout0104) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind07018_0) certificate0067

private theorem bind07019_0 : Agrees (spec (fastBase 1 25 35) layout0103) scope0547 := by decide

theorem reject07019 : Rejected (base 1 25 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 35) _ validLayout0103) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind07019_0) certificate0589

private theorem bind07020_0 : Agrees (spec (fastBase 1 25 36) layout0103) scope0551 := by decide

theorem reject07020 : Rejected (base 1 25 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 36) _ validLayout0103) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind07020_0) certificate0594

private theorem bind07021_0 : Agrees (spec (fastBase 1 25 37) layout0103) scope0228 := by decide

theorem reject07021 : Rejected (base 1 25 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 37) _ validLayout0103) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind07021_0) certificate0231

private theorem bind07022_0 : Agrees (spec (fastBase 1 25 38) layout0103) scope0547 := by decide

theorem reject07022 : Rejected (base 1 25 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 38) _ validLayout0103) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind07022_0) certificate0589

private theorem bind07023_0 : Agrees (spec (fastBase 1 25 39) layout0104) scope0065 := by decide

theorem reject07023 : Rejected (base 1 25 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 39) _ validLayout0104) (by decide) scope0065 (by rw [← fastBase_exact]; exact bind07023_0) certificate0067

private theorem bind07024_0 : Agrees (spec (fastBase 1 25 40) layout0103) scope0236 := by decide

theorem reject07024 : Rejected (base 1 25 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 40) _ validLayout0103) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind07024_0) certificate0239

private theorem bind07025_0 : Agrees (spec (fastBase 1 25 41) layout0103) scope0389 := by decide

theorem reject07025 : Rejected (base 1 25 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 41) _ validLayout0103) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind07025_0) certificate0402

private theorem bind07026_0 : Agrees (spec (fastBase 1 25 42) layout0103) scope0439 := by decide

theorem reject07026 : Rejected (base 1 25 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 42) _ validLayout0103) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind07026_0) certificate0468

private theorem bind07027_0 : Agrees (spec (fastBase 1 25 43) layout0103) scope0232 := by decide

theorem reject07027 : Rejected (base 1 25 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 43) _ validLayout0103) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind07027_0) certificate0235

private theorem bind07028_0 : Agrees (spec (fastBase 1 25 44) layout0103) scope0444 := by decide

theorem reject07028 : Rejected (base 1 25 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 44) _ validLayout0103) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind07028_0) certificate0475

private theorem bind07029_0 : Agrees (spec (fastBase 1 25 45) layout0103) scope0434 := by decide

theorem reject07029 : Rejected (base 1 25 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 45) _ validLayout0103) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind07029_0) certificate0461

private theorem bind07030_0 : Agrees (spec (fastBase 1 25 46) layout0103) scope0443 := by decide

theorem reject07030 : Rejected (base 1 25 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 46) _ validLayout0103) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind07030_0) certificate0474

private theorem bind07031_0 : Agrees (spec (fastBase 1 25 47) layout0103) scope0442 := by decide

theorem reject07031 : Rejected (base 1 25 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 47) _ validLayout0103) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind07031_0) certificate0471

private theorem bind07032_0 : Agrees (spec (fastBase 1 25 48) layout0103) scope0434 := by decide

theorem reject07032 : Rejected (base 1 25 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 48) _ validLayout0103) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind07032_0) certificate0461

private theorem bind07033_0 : Agrees (spec (fastBase 1 25 49) layout0103) scope0444 := by decide

theorem reject07033 : Rejected (base 1 25 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 49) _ validLayout0103) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind07033_0) certificate0475

private theorem bind07034_0 : Agrees (spec (fastBase 1 25 50) layout0103) scope0552 := by decide

theorem reject07034 : Rejected (base 1 25 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 50) _ validLayout0103) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind07034_0) certificate0595

private theorem bind07035_0 : Agrees (spec (fastBase 1 25 51) layout0103) scope0441 := by decide

theorem reject07035 : Rejected (base 1 25 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 51) _ validLayout0103) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind07035_0) certificate0470

private theorem bind07036_0 : Agrees (spec (fastBase 1 25 52) layout0103) scope0438 := by decide

theorem reject07036 : Rejected (base 1 25 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 52) _ validLayout0103) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind07036_0) certificate0467

private theorem bind07037_0 : Agrees (spec (fastBase 1 25 53) layout0103) scope0438 := by decide

theorem reject07037 : Rejected (base 1 25 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 53) _ validLayout0103) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind07037_0) certificate0467

private theorem bind07038_0 : Agrees (spec (fastBase 1 25 54) layout0103) scope0438 := by decide

theorem reject07038 : Rejected (base 1 25 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 54) _ validLayout0103) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind07038_0) certificate0467

private theorem bind07039_0 : Agrees (spec (fastBase 1 25 55) layout0103) scope0438 := by decide

theorem reject07039 : Rejected (base 1 25 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 55) _ validLayout0103) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind07039_0) certificate0467

private theorem bind07040_0 : Agrees (spec (fastBase 1 25 56) layout0103) scope0438 := by decide

theorem reject07040 : Rejected (base 1 25 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 56) _ validLayout0103) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind07040_0) certificate0467

private theorem bind07041_0 : Agrees (spec (fastBase 1 25 57) layout0103) scope0551 := by decide

theorem reject07041 : Rejected (base 1 25 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 57) _ validLayout0103) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind07041_0) certificate0594

private theorem bind07042_0 : Agrees (spec (fastBase 1 25 58) layout0104) scope0060 := by decide

theorem reject07042 : Rejected (base 1 25 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0104 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 58) _ validLayout0104) (by decide) scope0060 (by rw [← fastBase_exact]; exact bind07042_0) certificate0062

private theorem bind07043_0 : Agrees (spec (fastBase 1 25 59) layout0103) scope0236 := by decide

theorem reject07043 : Rejected (base 1 25 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 59) _ validLayout0103) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind07043_0) certificate0239

private theorem bind07044_0 : Agrees (spec (fastBase 1 25 60) layout0105) scope0491 := by decide

theorem reject07044 : Rejected (base 1 25 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 60) _ validLayout0105) (by decide) scope0491 (by rw [← fastBase_exact]; exact bind07044_0) certificate0533

private theorem bind07045_0 : Agrees (spec (fastBase 1 25 61) layout0103) scope0433 := by decide

theorem reject07045 : Rejected (base 1 25 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 61) _ validLayout0103) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind07045_0) certificate0460

private theorem bind07046_0 : Agrees (spec (fastBase 1 25 62) layout0103) scope0443 := by decide

theorem reject07046 : Rejected (base 1 25 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 62) _ validLayout0103) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind07046_0) certificate0474

private theorem bind07047_0 : Agrees (spec (fastBase 1 25 63) layout0105) scope0375 := by decide

theorem reject07047 : Rejected (base 1 25 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0105 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 63) _ validLayout0105) (by decide) scope0375 (by rw [← fastBase_exact]; exact bind07047_0) certificate0384

private theorem bind07048_0 : Agrees (spec (fastBase 1 25 64) layout0103) scope0434 := by decide

theorem reject07048 : Rejected (base 1 25 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 64) _ validLayout0103) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind07048_0) certificate0461

private theorem bind07049_0 : Agrees (spec (fastBase 1 25 65) layout0103) scope0441 := by decide

theorem reject07049 : Rejected (base 1 25 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 65) _ validLayout0103) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind07049_0) certificate0470

private theorem bind07050_0 : Agrees (spec (fastBase 1 25 66) layout0103) scope0433 := by decide

theorem reject07050 : Rejected (base 1 25 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 66) _ validLayout0103) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind07050_0) certificate0460

private theorem bind07051_0 : Agrees (spec (fastBase 1 25 67) layout0103) scope0433 := by decide

theorem reject07051 : Rejected (base 1 25 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 67) _ validLayout0103) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind07051_0) certificate0460

private theorem bind07052_0 : Agrees (spec (fastBase 1 25 68) layout0103) scope0389 := by decide

theorem reject07052 : Rejected (base 1 25 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 68) _ validLayout0103) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind07052_0) certificate0402

private theorem bind07053_0 : Agrees (spec (fastBase 1 25 69) layout0103) scope0552 := by decide

theorem reject07053 : Rejected (base 1 25 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 69) _ validLayout0103) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind07053_0) certificate0595

private theorem bind07054_0 : Agrees (spec (fastBase 1 25 70) layout0103) scope0236 := by decide

theorem reject07054 : Rejected (base 1 25 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 70) _ validLayout0103) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind07054_0) certificate0239

private theorem bind07055_0 : Agrees (spec (fastBase 1 25 71) layout0103) scope0441 := by decide

theorem reject07055 : Rejected (base 1 25 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0103 (layoutValid_of_refines _ _ (base_refines_skeleton 1 25 71) _ validLayout0103) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind07055_0) certificate0470

theorem allCases097 : ∀ y : Fin 72, Rejected (base 1 25 y) := by
  intro y
  fin_cases y

  · exact reject06984

  · exact reject06985

  · exact reject06986

  · exact reject06987

  · exact reject06988

  · exact reject06989

  · exact reject06990

  · exact reject06991

  · exact reject06992

  · exact reject06993

  · exact reject06994

  · exact reject06995

  · exact reject06996

  · exact reject06997

  · exact reject06998

  · exact reject06999

  · exact reject07000

  · exact reject07001

  · exact reject07002

  · exact reject07003

  · exact reject07004

  · exact reject07005

  · exact reject07006

  · exact reject07007

  · exact reject07008

  · exact reject07009

  · exact reject07010

  · exact reject07011

  · exact reject07012

  · exact reject07013

  · exact reject07014

  · exact reject07015

  · exact reject07016

  · exact reject07017

  · exact reject07018

  · exact reject07019

  · exact reject07020

  · exact reject07021

  · exact reject07022

  · exact reject07023

  · exact reject07024

  · exact reject07025

  · exact reject07026

  · exact reject07027

  · exact reject07028

  · exact reject07029

  · exact reject07030

  · exact reject07031

  · exact reject07032

  · exact reject07033

  · exact reject07034

  · exact reject07035

  · exact reject07036

  · exact reject07037

  · exact reject07038

  · exact reject07039

  · exact reject07040

  · exact reject07041

  · exact reject07042

  · exact reject07043

  · exact reject07044

  · exact reject07045

  · exact reject07046

  · exact reject07047

  · exact reject07048

  · exact reject07049

  · exact reject07050

  · exact reject07051

  · exact reject07052

  · exact reject07053

  · exact reject07054

  · exact reject07055

end PricingIntegration.RemainingGWitnesses
