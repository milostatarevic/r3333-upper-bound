import PricingIntegration.RemainingGLayouts032

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks014

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks021

import PricingIntegration.RemainingGScopeChecks022

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks028

import PricingIntegration.RemainingGScopeChecks029

import PricingIntegration.RemainingGScopeChecks032

import PricingIntegration.RemainingGScopeChecks036

import PricingIntegration.RemainingGScopeChecks037


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind10152_0 : Agrees (spec (fastBase 1 69 0) layout0261) scope0434 := by decide

theorem reject10152 : Rejected (base 1 69 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 0) _ validLayout0261) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind10152_0) certificate0461

private theorem bind10153_0 : Agrees (spec (fastBase 1 69 1) layout0261) scope0236 := by decide

theorem reject10153 : Rejected (base 1 69 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 1) _ validLayout0261) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind10153_0) certificate0239

private theorem bind10154_0 : Agrees (spec (fastBase 1 69 2) layout0261) scope0548 := by decide

theorem reject10154 : Rejected (base 1 69 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 2) _ validLayout0261) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind10154_0) certificate0590

private theorem bind10155_0 : Agrees (spec (fastBase 1 69 3) layout0261) scope0438 := by decide

theorem reject10155 : Rejected (base 1 69 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 3) _ validLayout0261) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind10155_0) certificate0467

private theorem bind10156_0 : Agrees (spec (fastBase 1 69 4) layout0261) scope0233 := by decide

theorem reject10156 : Rejected (base 1 69 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 4) _ validLayout0261) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind10156_0) certificate0236

private theorem bind10157_0 : Agrees (spec (fastBase 1 69 5) layout0261) scope0444 := by decide

theorem reject10157 : Rejected (base 1 69 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 5) _ validLayout0261) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind10157_0) certificate0475

private theorem bind10158_0 : Agrees (spec (fastBase 1 69 6) layout0260) scope0330 := by decide

theorem reject10158 : Rejected (base 1 69 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 6) _ validLayout0260) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind10158_0) certificate0337

private theorem bind10159_0 : Agrees (spec (fastBase 1 69 7) layout0261) scope0441 := by decide

theorem reject10159 : Rejected (base 1 69 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 7) _ validLayout0261) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind10159_0) certificate0470

private theorem bind10160_0 : Agrees (spec (fastBase 1 69 8) layout0260) scope0332 := by decide

private theorem bind10160_1 : Agrees (spec (fastBase 1 69 8) layout0262) scope0425 := by decide

theorem reject10160 : Rejected (base 1 69 8) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 8) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 8) _ validLayout0262) (by decide) (by decide) scope0332 scope0425 (by rw [← fastBase_exact]; exact bind10160_0) (by rw [← fastBase_exact]; exact bind10160_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0520 (by decide)

private theorem bind10161_0 : Agrees (spec (fastBase 1 69 9) layout0261) scope0433 := by decide

theorem reject10161 : Rejected (base 1 69 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 9) _ validLayout0261) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind10161_0) certificate0460

private theorem bind10162_0 : Agrees (spec (fastBase 1 69 10) layout0261) scope0232 := by decide

theorem reject10162 : Rejected (base 1 69 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 10) _ validLayout0261) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind10162_0) certificate0235

private theorem bind10163_0 : Agrees (spec (fastBase 1 69 11) layout0261) scope0547 := by decide

theorem reject10163 : Rejected (base 1 69 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 11) _ validLayout0261) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind10163_0) certificate0589

private theorem bind10164_0 : Agrees (spec (fastBase 1 69 12) layout0261) scope0552 := by decide

theorem reject10164 : Rejected (base 1 69 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 12) _ validLayout0261) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind10164_0) certificate0595

private theorem bind10165_0 : Agrees (spec (fastBase 1 69 13) layout0261) scope0442 := by decide

theorem reject10165 : Rejected (base 1 69 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 13) _ validLayout0261) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind10165_0) certificate0471

private theorem bind10166_0 : Agrees (spec (fastBase 1 69 14) layout0261) scope0444 := by decide

theorem reject10166 : Rejected (base 1 69 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 14) _ validLayout0261) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind10166_0) certificate0475

private theorem bind10167_0 : Agrees (spec (fastBase 1 69 15) layout0261) scope0441 := by decide

theorem reject10167 : Rejected (base 1 69 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 15) _ validLayout0261) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind10167_0) certificate0470

private theorem bind10168_0 : Agrees (spec (fastBase 1 69 16) layout0261) scope0434 := by decide

theorem reject10168 : Rejected (base 1 69 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 16) _ validLayout0261) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind10168_0) certificate0461

private theorem bind10169_0 : Agrees (spec (fastBase 1 69 17) layout0260) scope0339 := by decide

theorem reject10169 : Rejected (base 1 69 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 17) _ validLayout0260) (by decide) scope0339 (by rw [← fastBase_exact]; exact bind10169_0) certificate0346

private theorem bind10170_0 : Agrees (spec (fastBase 1 69 18) layout0261) scope0236 := by decide

theorem reject10170 : Rejected (base 1 69 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 18) _ validLayout0261) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind10170_0) certificate0239

private theorem bind10171_0 : Agrees (spec (fastBase 1 69 19) layout0261) scope0551 := by decide

theorem reject10171 : Rejected (base 1 69 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 19) _ validLayout0261) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind10171_0) certificate0594

private theorem bind10172_0 : Agrees (spec (fastBase 1 69 20) layout0260) scope0480 := by decide

private theorem bind10172_1 : Agrees (spec (fastBase 1 69 20) layout0262) scope0427 := by decide

theorem reject10172 : Rejected (base 1 69 20) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 20) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 20) _ validLayout0262) (by decide) (by decide) scope0480 scope0427 (by rw [← fastBase_exact]; exact bind10172_0) (by rw [← fastBase_exact]; exact bind10172_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0521 certificate0522 (by decide)

private theorem bind10173_0 : Agrees (spec (fastBase 1 69 21) layout0261) scope0433 := by decide

theorem reject10173 : Rejected (base 1 69 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 21) _ validLayout0261) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind10173_0) certificate0460

private theorem bind10174_0 : Agrees (spec (fastBase 1 69 22) layout0261) scope0439 := by decide

theorem reject10174 : Rejected (base 1 69 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 22) _ validLayout0261) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind10174_0) certificate0468

private theorem bind10175_0 : Agrees (spec (fastBase 1 69 23) layout0261) scope0233 := by decide

theorem reject10175 : Rejected (base 1 69 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 23) _ validLayout0261) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind10175_0) certificate0236

private theorem bind10176_0 : Agrees (spec (fastBase 1 69 24) layout0261) scope0548 := by decide

theorem reject10176 : Rejected (base 1 69 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 24) _ validLayout0261) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind10176_0) certificate0590

private theorem bind10177_0 : Agrees (spec (fastBase 1 69 25) layout0260) scope0346 := by decide

theorem reject10177 : Rejected (base 1 69 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 25) _ validLayout0260) (by decide) scope0346 (by rw [← fastBase_exact]; exact bind10177_0) certificate0353

private theorem bind10178_0 : Agrees (spec (fastBase 1 69 26) layout0261) scope0232 := by decide

theorem reject10178 : Rejected (base 1 69 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 26) _ validLayout0261) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind10178_0) certificate0235

private theorem bind10179_0 : Agrees (spec (fastBase 1 69 27) layout0261) scope0438 := by decide

theorem reject10179 : Rejected (base 1 69 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 27) _ validLayout0261) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind10179_0) certificate0467

private theorem bind10180_0 : Agrees (spec (fastBase 1 69 28) layout0261) scope0438 := by decide

theorem reject10180 : Rejected (base 1 69 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 28) _ validLayout0261) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind10180_0) certificate0467

private theorem bind10181_0 : Agrees (spec (fastBase 1 69 29) layout0261) scope0438 := by decide

theorem reject10181 : Rejected (base 1 69 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 29) _ validLayout0261) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind10181_0) certificate0467

private theorem bind10182_0 : Agrees (spec (fastBase 1 69 30) layout0261) scope0438 := by decide

theorem reject10182 : Rejected (base 1 69 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 30) _ validLayout0261) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind10182_0) certificate0467

private theorem bind10183_0 : Agrees (spec (fastBase 1 69 31) layout0261) scope0438 := by decide

theorem reject10183 : Rejected (base 1 69 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 31) _ validLayout0261) (by decide) scope0438 (by rw [← fastBase_exact]; exact bind10183_0) certificate0467

private theorem bind10184_0 : Agrees (spec (fastBase 1 69 32) layout0261) scope0228 := by decide

theorem reject10184 : Rejected (base 1 69 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 32) _ validLayout0261) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind10184_0) certificate0231

private theorem bind10185_0 : Agrees (spec (fastBase 1 69 33) layout0261) scope0548 := by decide

theorem reject10185 : Rejected (base 1 69 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 33) _ validLayout0261) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind10185_0) certificate0590

private theorem bind10186_0 : Agrees (spec (fastBase 1 69 34) layout0261) scope0550 := by decide

theorem reject10186 : Rejected (base 1 69 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 34) _ validLayout0261) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind10186_0) certificate0593

private theorem bind10187_0 : Agrees (spec (fastBase 1 69 35) layout0261) scope0233 := by decide

theorem reject10187 : Rejected (base 1 69 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 35) _ validLayout0261) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind10187_0) certificate0236

private theorem bind10188_0 : Agrees (spec (fastBase 1 69 36) layout0261) scope0547 := by decide

theorem reject10188 : Rejected (base 1 69 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 36) _ validLayout0261) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind10188_0) certificate0589

private theorem bind10189_0 : Agrees (spec (fastBase 1 69 37) layout0261) scope0434 := by decide

theorem reject10189 : Rejected (base 1 69 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 37) _ validLayout0261) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind10189_0) certificate0461

private theorem bind10190_0 : Agrees (spec (fastBase 1 69 38) layout0261) scope0439 := by decide

theorem reject10190 : Rejected (base 1 69 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 38) _ validLayout0261) (by decide) scope0439 (by rw [← fastBase_exact]; exact bind10190_0) certificate0468

private theorem bind10191_0 : Agrees (spec (fastBase 1 69 39) layout0261) scope0444 := by decide

theorem reject10191 : Rejected (base 1 69 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 39) _ validLayout0261) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind10191_0) certificate0475

private theorem bind10192_0 : Agrees (spec (fastBase 1 69 40) layout0261) scope0443 := by decide

theorem reject10192 : Rejected (base 1 69 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 40) _ validLayout0261) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind10192_0) certificate0474

private theorem bind10193_0 : Agrees (spec (fastBase 1 69 41) layout0261) scope0232 := by decide

theorem reject10193 : Rejected (base 1 69 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 41) _ validLayout0261) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind10193_0) certificate0235

private theorem bind10194_0 : Agrees (spec (fastBase 1 69 42) layout0261) scope0236 := by decide

theorem reject10194 : Rejected (base 1 69 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 42) _ validLayout0261) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind10194_0) certificate0239

private theorem bind10195_0 : Agrees (spec (fastBase 1 69 43) layout0261) scope0228 := by decide

theorem reject10195 : Rejected (base 1 69 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 43) _ validLayout0261) (by decide) scope0228 (by rw [← fastBase_exact]; exact bind10195_0) certificate0231

private theorem bind10196_0 : Agrees (spec (fastBase 1 69 44) layout0260) scope0332 := by decide

private theorem bind10196_1 : Agrees (spec (fastBase 1 69 44) layout0262) scope0427 := by decide

theorem reject10196 : Rejected (base 1 69 44) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 44) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 44) _ validLayout0262) (by decide) (by decide) scope0332 scope0427 (by rw [← fastBase_exact]; exact bind10196_0) (by rw [← fastBase_exact]; exact bind10196_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0522 (by decide)

private theorem bind10197_0 : Agrees (spec (fastBase 1 69 45) layout0261) scope0389 := by decide

theorem reject10197 : Rejected (base 1 69 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 45) _ validLayout0261) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind10197_0) certificate0402

private theorem bind10198_0 : Agrees (spec (fastBase 1 69 46) layout0261) scope0547 := by decide

theorem reject10198 : Rejected (base 1 69 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 46) _ validLayout0261) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind10198_0) certificate0589

private theorem bind10199_0 : Agrees (spec (fastBase 1 69 47) layout0261) scope0434 := by decide

theorem reject10199 : Rejected (base 1 69 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 47) _ validLayout0261) (by decide) scope0434 (by rw [← fastBase_exact]; exact bind10199_0) certificate0461

private theorem bind10200_0 : Agrees (spec (fastBase 1 69 48) layout0261) scope0441 := by decide

theorem reject10200 : Rejected (base 1 69 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 48) _ validLayout0261) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind10200_0) certificate0470

private theorem bind10201_0 : Agrees (spec (fastBase 1 69 49) layout0260) scope0331 := by decide

theorem reject10201 : Rejected (base 1 69 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 49) _ validLayout0260) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind10201_0) certificate0338

private theorem bind10202_0 : Agrees (spec (fastBase 1 69 50) layout0261) scope0433 := by decide

theorem reject10202 : Rejected (base 1 69 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 50) _ validLayout0261) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind10202_0) certificate0460

private theorem bind10203_0 : Agrees (spec (fastBase 1 69 51) layout0261) scope0443 := by decide

theorem reject10203 : Rejected (base 1 69 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 51) _ validLayout0261) (by decide) scope0443 (by rw [← fastBase_exact]; exact bind10203_0) certificate0474

private theorem bind10204_0 : Agrees (spec (fastBase 1 69 52) layout0260) scope0342 := by decide

theorem reject10204 : Rejected (base 1 69 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 52) _ validLayout0260) (by decide) scope0342 (by rw [← fastBase_exact]; exact bind10204_0) certificate0349

private theorem bind10205_0 : Agrees (spec (fastBase 1 69 53) layout0260) scope0327 := by decide

private theorem bind10205_1 : Agrees (spec (fastBase 1 69 53) layout0262) scope0425 := by decide

theorem reject10205 : Rejected (base 1 69 53) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 53) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 53) _ validLayout0262) (by decide) (by decide) scope0327 scope0425 (by rw [← fastBase_exact]; exact bind10205_0) (by rw [← fastBase_exact]; exact bind10205_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0520 (by decide)

private theorem bind10206_0 : Agrees (spec (fastBase 1 69 54) layout0260) scope0330 := by decide

theorem reject10206 : Rejected (base 1 69 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 54) _ validLayout0260) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind10206_0) certificate0337

private theorem bind10207_0 : Agrees (spec (fastBase 1 69 55) layout0260) scope0347 := by decide

theorem reject10207 : Rejected (base 1 69 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 55) _ validLayout0260) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind10207_0) certificate0354

private theorem bind10208_0 : Agrees (spec (fastBase 1 69 56) layout0260) scope0332 := by decide

private theorem bind10208_1 : Agrees (spec (fastBase 1 69 56) layout0262) scope0425 := by decide

theorem reject10208 : Rejected (base 1 69 56) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 56) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 56) _ validLayout0262) (by decide) (by decide) scope0332 scope0425 (by rw [← fastBase_exact]; exact bind10208_0) (by rw [← fastBase_exact]; exact bind10208_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0520 (by decide)

private theorem bind10209_0 : Agrees (spec (fastBase 1 69 57) layout0261) scope0236 := by decide

theorem reject10209 : Rejected (base 1 69 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 57) _ validLayout0261) (by decide) scope0236 (by rw [← fastBase_exact]; exact bind10209_0) certificate0239

private theorem bind10210_0 : Agrees (spec (fastBase 1 69 58) layout0261) scope0552 := by decide

theorem reject10210 : Rejected (base 1 69 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 58) _ validLayout0261) (by decide) scope0552 (by rw [← fastBase_exact]; exact bind10210_0) certificate0595

private theorem bind10211_0 : Agrees (spec (fastBase 1 69 59) layout0261) scope0433 := by decide

theorem reject10211 : Rejected (base 1 69 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 59) _ validLayout0261) (by decide) scope0433 (by rw [← fastBase_exact]; exact bind10211_0) certificate0460

private theorem bind10212_0 : Agrees (spec (fastBase 1 69 60) layout0261) scope0441 := by decide

theorem reject10212 : Rejected (base 1 69 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 60) _ validLayout0261) (by decide) scope0441 (by rw [← fastBase_exact]; exact bind10212_0) certificate0470

private theorem bind10213_0 : Agrees (spec (fastBase 1 69 61) layout0261) scope0389 := by decide

theorem reject10213 : Rejected (base 1 69 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 61) _ validLayout0261) (by decide) scope0389 (by rw [← fastBase_exact]; exact bind10213_0) certificate0402

private theorem bind10214_0 : Agrees (spec (fastBase 1 69 62) layout0261) scope0548 := by decide

theorem reject10214 : Rejected (base 1 69 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 62) _ validLayout0261) (by decide) scope0548 (by rw [← fastBase_exact]; exact bind10214_0) certificate0590

private theorem bind10215_0 : Agrees (spec (fastBase 1 69 63) layout0261) scope0444 := by decide

theorem reject10215 : Rejected (base 1 69 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 63) _ validLayout0261) (by decide) scope0444 (by rw [← fastBase_exact]; exact bind10215_0) certificate0475

private theorem bind10216_0 : Agrees (spec (fastBase 1 69 64) layout0261) scope0442 := by decide

theorem reject10216 : Rejected (base 1 69 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 64) _ validLayout0261) (by decide) scope0442 (by rw [← fastBase_exact]; exact bind10216_0) certificate0471

private theorem bind10217_0 : Agrees (spec (fastBase 1 69 65) layout0261) scope0232 := by decide

theorem reject10217 : Rejected (base 1 69 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 65) _ validLayout0261) (by decide) scope0232 (by rw [← fastBase_exact]; exact bind10217_0) certificate0235

private theorem bind10218_0 : Agrees (spec (fastBase 1 69 66) layout0261) scope0550 := by decide

theorem reject10218 : Rejected (base 1 69 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 66) _ validLayout0261) (by decide) scope0550 (by rw [← fastBase_exact]; exact bind10218_0) certificate0593

private theorem bind10219_0 : Agrees (spec (fastBase 1 69 67) layout0261) scope0547 := by decide

theorem reject10219 : Rejected (base 1 69 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 67) _ validLayout0261) (by decide) scope0547 (by rw [← fastBase_exact]; exact bind10219_0) certificate0589

private theorem bind10220_0 : Agrees (spec (fastBase 1 69 68) layout0261) scope0233 := by decide

theorem reject10220 : Rejected (base 1 69 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 68) _ validLayout0261) (by decide) scope0233 (by rw [← fastBase_exact]; exact bind10220_0) certificate0236

private theorem bind10221_0 : Agrees (spec (fastBase 1 69 69) layout0260) scope0330 := by decide

theorem reject10221 : Rejected (base 1 69 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 69) _ validLayout0260) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind10221_0) certificate0337

private theorem bind10222_0 : Agrees (spec (fastBase 1 69 70) layout0261) scope0551 := by decide

theorem reject10222 : Rejected (base 1 69 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 70) _ validLayout0261) (by decide) scope0551 (by rw [← fastBase_exact]; exact bind10222_0) certificate0594

private theorem bind10223_0 : Agrees (spec (fastBase 1 69 71) layout0260) scope0347 := by decide

theorem reject10223 : Rejected (base 1 69 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 1 69 71) _ validLayout0260) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind10223_0) certificate0354

theorem allCases141 : ∀ y : Fin 72, Rejected (base 1 69 y) := by
  intro y
  fin_cases y

  · exact reject10152

  · exact reject10153

  · exact reject10154

  · exact reject10155

  · exact reject10156

  · exact reject10157

  · exact reject10158

  · exact reject10159

  · exact reject10160

  · exact reject10161

  · exact reject10162

  · exact reject10163

  · exact reject10164

  · exact reject10165

  · exact reject10166

  · exact reject10167

  · exact reject10168

  · exact reject10169

  · exact reject10170

  · exact reject10171

  · exact reject10172

  · exact reject10173

  · exact reject10174

  · exact reject10175

  · exact reject10176

  · exact reject10177

  · exact reject10178

  · exact reject10179

  · exact reject10180

  · exact reject10181

  · exact reject10182

  · exact reject10183

  · exact reject10184

  · exact reject10185

  · exact reject10186

  · exact reject10187

  · exact reject10188

  · exact reject10189

  · exact reject10190

  · exact reject10191

  · exact reject10192

  · exact reject10193

  · exact reject10194

  · exact reject10195

  · exact reject10196

  · exact reject10197

  · exact reject10198

  · exact reject10199

  · exact reject10200

  · exact reject10201

  · exact reject10202

  · exact reject10203

  · exact reject10204

  · exact reject10205

  · exact reject10206

  · exact reject10207

  · exact reject10208

  · exact reject10209

  · exact reject10210

  · exact reject10211

  · exact reject10212

  · exact reject10213

  · exact reject10214

  · exact reject10215

  · exact reject10216

  · exact reject10217

  · exact reject10218

  · exact reject10219

  · exact reject10220

  · exact reject10221

  · exact reject10222

  · exact reject10223

end PricingIntegration.RemainingGWitnesses
