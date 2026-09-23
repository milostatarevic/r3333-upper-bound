import PricingIntegration.RemainingGLayouts020

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks019

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks026

import PricingIntegration.RemainingGScopeChecks027


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02952_0 : Agrees (spec (fastBase 0 41 0) layout0161) scope0305 := by decide

theorem reject02952 : Rejected (base 0 41 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 0) _ validLayout0161) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind02952_0) certificate0310

private theorem bind02953_0 : Agrees (spec (fastBase 0 41 1) layout0161) scope0302 := by decide

theorem reject02953 : Rejected (base 0 41 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 1) _ validLayout0161) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind02953_0) certificate0307

private theorem bind02954_0 : Agrees (spec (fastBase 0 41 2) layout0161) scope0299 := by decide

theorem reject02954 : Rejected (base 0 41 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 2) _ validLayout0161) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind02954_0) certificate0304

private theorem bind02955_0 : Agrees (spec (fastBase 0 41 3) layout0161) scope0304 := by decide

theorem reject02955 : Rejected (base 0 41 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 3) _ validLayout0161) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind02955_0) certificate0309

private theorem bind02956_0 : Agrees (spec (fastBase 0 41 4) layout0161) scope0294 := by decide

theorem reject02956 : Rejected (base 0 41 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 4) _ validLayout0161) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind02956_0) certificate0299

private theorem bind02957_0 : Agrees (spec (fastBase 0 41 5) layout0161) scope0303 := by decide

theorem reject02957 : Rejected (base 0 41 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 5) _ validLayout0161) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind02957_0) certificate0308

private theorem bind02958_0 : Agrees (spec (fastBase 0 41 6) layout0161) scope0297 := by decide

theorem reject02958 : Rejected (base 0 41 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 6) _ validLayout0161) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind02958_0) certificate0302

private theorem bind02959_0 : Agrees (spec (fastBase 0 41 7) layout0161) scope0322 := by decide

private theorem bind02959_1 : Agrees (spec (fastBase 0 41 7) layout0162) scope0301 := by decide

theorem reject02959 : Rejected (base 0 41 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0161 layout0162 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 7) _ validLayout0161) (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 7) _ validLayout0162) (by decide) (by decide) scope0322 scope0301 (by rw [← fastBase_exact]; exact bind02959_0) (by rw [← fastBase_exact]; exact bind02959_1) 1 6 1 6 (by decide) (by decide) 3 2 (by decide) certificate0328 certificate0329 (by decide)

private theorem bind02960_0 : Agrees (spec (fastBase 0 41 8) layout0161) scope0296 := by decide

theorem reject02960 : Rejected (base 0 41 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 8) _ validLayout0161) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind02960_0) certificate0301

private theorem bind02961_0 : Agrees (spec (fastBase 0 41 9) layout0161) scope0300 := by decide

private theorem bind02961_1 : Agrees (spec (fastBase 0 41 9) layout0162) scope0306 := by decide

theorem reject02961 : Rejected (base 0 41 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0161 layout0162 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 9) _ validLayout0161) (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 9) _ validLayout0162) (by decide) (by decide) scope0300 scope0306 (by rw [← fastBase_exact]; exact bind02961_0) (by rw [← fastBase_exact]; exact bind02961_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0322 (by decide)

private theorem bind02962_0 : Agrees (spec (fastBase 0 41 10) layout0161) scope0298 := by decide

theorem reject02962 : Rejected (base 0 41 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 10) _ validLayout0161) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind02962_0) certificate0303

private theorem bind02963_0 : Agrees (spec (fastBase 0 41 11) layout0161) scope0295 := by decide

theorem reject02963 : Rejected (base 0 41 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 11) _ validLayout0161) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind02963_0) certificate0300

private theorem bind02964_0 : Agrees (spec (fastBase 0 41 12) layout0161) scope0302 := by decide

theorem reject02964 : Rejected (base 0 41 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 12) _ validLayout0161) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind02964_0) certificate0307

private theorem bind02965_0 : Agrees (spec (fastBase 0 41 13) layout0161) scope0305 := by decide

theorem reject02965 : Rejected (base 0 41 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 13) _ validLayout0161) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind02965_0) certificate0310

private theorem bind02966_0 : Agrees (spec (fastBase 0 41 14) layout0161) scope0303 := by decide

theorem reject02966 : Rejected (base 0 41 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 14) _ validLayout0161) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind02966_0) certificate0308

private theorem bind02967_0 : Agrees (spec (fastBase 0 41 15) layout0163) scope0158 := by decide

theorem reject02967 : Rejected (base 0 41 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0163 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 15) _ validLayout0163) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02967_0) certificate0161

private theorem bind02968_0 : Agrees (spec (fastBase 0 41 16) layout0161) scope0309 := by decide

theorem reject02968 : Rejected (base 0 41 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 16) _ validLayout0161) (by decide) scope0309 (by rw [← fastBase_exact]; exact bind02968_0) certificate0314

private theorem bind02969_0 : Agrees (spec (fastBase 0 41 17) layout0161) scope0305 := by decide

theorem reject02969 : Rejected (base 0 41 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 17) _ validLayout0161) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind02969_0) certificate0310

private theorem bind02970_0 : Agrees (spec (fastBase 0 41 18) layout0161) scope0304 := by decide

theorem reject02970 : Rejected (base 0 41 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 18) _ validLayout0161) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind02970_0) certificate0309

private theorem bind02971_0 : Agrees (spec (fastBase 0 41 19) layout0161) scope0317 := by decide

theorem reject02971 : Rejected (base 0 41 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 19) _ validLayout0161) (by decide) scope0317 (by rw [← fastBase_exact]; exact bind02971_0) certificate0323

private theorem bind02972_0 : Agrees (spec (fastBase 0 41 20) layout0161) scope0318 := by decide

theorem reject02972 : Rejected (base 0 41 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 20) _ validLayout0161) (by decide) scope0318 (by rw [← fastBase_exact]; exact bind02972_0) certificate0324

private theorem bind02973_0 : Agrees (spec (fastBase 0 41 21) layout0161) scope0302 := by decide

theorem reject02973 : Rejected (base 0 41 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 21) _ validLayout0161) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind02973_0) certificate0307

private theorem bind02974_0 : Agrees (spec (fastBase 0 41 22) layout0161) scope0299 := by decide

theorem reject02974 : Rejected (base 0 41 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 22) _ validLayout0161) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind02974_0) certificate0304

private theorem bind02975_0 : Agrees (spec (fastBase 0 41 23) layout0161) scope0299 := by decide

theorem reject02975 : Rejected (base 0 41 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 23) _ validLayout0161) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind02975_0) certificate0304

private theorem bind02976_0 : Agrees (spec (fastBase 0 41 24) layout0161) scope0299 := by decide

theorem reject02976 : Rejected (base 0 41 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 24) _ validLayout0161) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind02976_0) certificate0304

private theorem bind02977_0 : Agrees (spec (fastBase 0 41 25) layout0161) scope0299 := by decide

theorem reject02977 : Rejected (base 0 41 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 25) _ validLayout0161) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind02977_0) certificate0304

private theorem bind02978_0 : Agrees (spec (fastBase 0 41 26) layout0161) scope0299 := by decide

theorem reject02978 : Rejected (base 0 41 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 26) _ validLayout0161) (by decide) scope0299 (by rw [← fastBase_exact]; exact bind02978_0) certificate0304

private theorem bind02979_0 : Agrees (spec (fastBase 0 41 27) layout0161) scope0302 := by decide

theorem reject02979 : Rejected (base 0 41 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 27) _ validLayout0161) (by decide) scope0302 (by rw [← fastBase_exact]; exact bind02979_0) certificate0307

private theorem bind02980_0 : Agrees (spec (fastBase 0 41 28) layout0161) scope0304 := by decide

theorem reject02980 : Rejected (base 0 41 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 28) _ validLayout0161) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind02980_0) certificate0309

private theorem bind02981_0 : Agrees (spec (fastBase 0 41 29) layout0163) scope0158 := by decide

theorem reject02981 : Rejected (base 0 41 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0163 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 29) _ validLayout0163) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02981_0) certificate0161

private theorem bind02982_0 : Agrees (spec (fastBase 0 41 30) layout0163) scope0140 := by decide

theorem reject02982 : Rejected (base 0 41 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0163 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 30) _ validLayout0163) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind02982_0) certificate0143

private theorem bind02983_0 : Agrees (spec (fastBase 0 41 31) layout0161) scope0314 := by decide

theorem reject02983 : Rejected (base 0 41 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 31) _ validLayout0161) (by decide) scope0314 (by rw [← fastBase_exact]; exact bind02983_0) certificate0319

private theorem bind02984_0 : Agrees (spec (fastBase 0 41 32) layout0161) scope0309 := by decide

theorem reject02984 : Rejected (base 0 41 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 32) _ validLayout0161) (by decide) scope0309 (by rw [← fastBase_exact]; exact bind02984_0) certificate0314

private theorem bind02985_0 : Agrees (spec (fastBase 0 41 33) layout0161) scope0294 := by decide

theorem reject02985 : Rejected (base 0 41 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 33) _ validLayout0161) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind02985_0) certificate0299

private theorem bind02986_0 : Agrees (spec (fastBase 0 41 34) layout0161) scope0303 := by decide

theorem reject02986 : Rejected (base 0 41 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 34) _ validLayout0161) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind02986_0) certificate0308

private theorem bind02987_0 : Agrees (spec (fastBase 0 41 35) layout0161) scope0296 := by decide

theorem reject02987 : Rejected (base 0 41 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 35) _ validLayout0161) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind02987_0) certificate0301

private theorem bind02988_0 : Agrees (spec (fastBase 0 41 36) layout0161) scope0308 := by decide

theorem reject02988 : Rejected (base 0 41 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 36) _ validLayout0161) (by decide) scope0308 (by rw [← fastBase_exact]; exact bind02988_0) certificate0313

private theorem bind02989_0 : Agrees (spec (fastBase 0 41 37) layout0161) scope0305 := by decide

theorem reject02989 : Rejected (base 0 41 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 37) _ validLayout0161) (by decide) scope0305 (by rw [← fastBase_exact]; exact bind02989_0) certificate0310

private theorem bind02990_0 : Agrees (spec (fastBase 0 41 38) layout0161) scope0294 := by decide

theorem reject02990 : Rejected (base 0 41 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 38) _ validLayout0161) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind02990_0) certificate0299

private theorem bind02991_0 : Agrees (spec (fastBase 0 41 39) layout0161) scope0317 := by decide

theorem reject02991 : Rejected (base 0 41 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 39) _ validLayout0161) (by decide) scope0317 (by rw [← fastBase_exact]; exact bind02991_0) certificate0323

private theorem bind02992_0 : Agrees (spec (fastBase 0 41 40) layout0161) scope0303 := by decide

theorem reject02992 : Rejected (base 0 41 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 40) _ validLayout0161) (by decide) scope0303 (by rw [← fastBase_exact]; exact bind02992_0) certificate0308

private theorem bind02993_0 : Agrees (spec (fastBase 0 41 41) layout0161) scope0312 := by decide

theorem reject02993 : Rejected (base 0 41 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 41) _ validLayout0161) (by decide) scope0312 (by rw [← fastBase_exact]; exact bind02993_0) certificate0317

private theorem bind02994_0 : Agrees (spec (fastBase 0 41 42) layout0161) scope0314 := by decide

theorem reject02994 : Rejected (base 0 41 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 42) _ validLayout0161) (by decide) scope0314 (by rw [← fastBase_exact]; exact bind02994_0) certificate0319

private theorem bind02995_0 : Agrees (spec (fastBase 0 41 43) layout0161) scope0297 := by decide

theorem reject02995 : Rejected (base 0 41 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 43) _ validLayout0161) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind02995_0) certificate0302

private theorem bind02996_0 : Agrees (spec (fastBase 0 41 44) layout0163) scope0171 := by decide

theorem reject02996 : Rejected (base 0 41 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0163 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 44) _ validLayout0163) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind02996_0) certificate0174

private theorem bind02997_0 : Agrees (spec (fastBase 0 41 45) layout0162) scope0414 := by decide

theorem reject02997 : Rejected (base 0 41 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0162 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 45) _ validLayout0162) (by decide) scope0414 (by rw [← fastBase_exact]; exact bind02997_0) certificate0436

private theorem bind02998_0 : Agrees (spec (fastBase 0 41 46) layout0161) scope0295 := by decide

theorem reject02998 : Rejected (base 0 41 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 46) _ validLayout0161) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind02998_0) certificate0300

private theorem bind02999_0 : Agrees (spec (fastBase 0 41 47) layout0161) scope0318 := by decide

theorem reject02999 : Rejected (base 0 41 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 47) _ validLayout0161) (by decide) scope0318 (by rw [← fastBase_exact]; exact bind02999_0) certificate0324

private theorem bind03000_0 : Agrees (spec (fastBase 0 41 48) layout0161) scope0304 := by decide

theorem reject03000 : Rejected (base 0 41 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 48) _ validLayout0161) (by decide) scope0304 (by rw [← fastBase_exact]; exact bind03000_0) certificate0309

private theorem bind03001_0 : Agrees (spec (fastBase 0 41 49) layout0161) scope0297 := by decide

theorem reject03001 : Rejected (base 0 41 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 49) _ validLayout0161) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind03001_0) certificate0302

private theorem bind03002_0 : Agrees (spec (fastBase 0 41 50) layout0162) scope0306 := by decide

private theorem bind03002_1 : Agrees (spec (fastBase 0 41 50) layout0164) scope0409 := by decide

theorem reject03002 : Rejected (base 0 41 50) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0162 layout0164 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 50) _ validLayout0162) (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 50) _ validLayout0164) (by decide) (by decide) scope0306 scope0409 (by rw [← fastBase_exact]; exact bind03002_0) (by rw [← fastBase_exact]; exact bind03002_1) 3 8 3 8 (by decide) (by decide) 3 2 (by decide) certificate0311 certificate0437 (by decide)

private theorem bind03003_0 : Agrees (spec (fastBase 0 41 51) layout0161) scope0311 := by decide

theorem reject03003 : Rejected (base 0 41 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 51) _ validLayout0161) (by decide) scope0311 (by rw [← fastBase_exact]; exact bind03003_0) certificate0316

private theorem bind03004_0 : Agrees (spec (fastBase 0 41 52) layout0161) scope0312 := by decide

theorem reject03004 : Rejected (base 0 41 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 52) _ validLayout0161) (by decide) scope0312 (by rw [← fastBase_exact]; exact bind03004_0) certificate0317

private theorem bind03005_0 : Agrees (spec (fastBase 0 41 53) layout0161) scope0294 := by decide

theorem reject03005 : Rejected (base 0 41 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 53) _ validLayout0161) (by decide) scope0294 (by rw [← fastBase_exact]; exact bind03005_0) certificate0299

private theorem bind03006_0 : Agrees (spec (fastBase 0 41 54) layout0161) scope0310 := by decide

theorem reject03006 : Rejected (base 0 41 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 54) _ validLayout0161) (by decide) scope0310 (by rw [← fastBase_exact]; exact bind03006_0) certificate0315

private theorem bind03007_0 : Agrees (spec (fastBase 0 41 55) layout0161) scope0296 := by decide

theorem reject03007 : Rejected (base 0 41 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 55) _ validLayout0161) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind03007_0) certificate0301

private theorem bind03008_0 : Agrees (spec (fastBase 0 41 56) layout0161) scope0298 := by decide

theorem reject03008 : Rejected (base 0 41 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 56) _ validLayout0161) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind03008_0) certificate0303

private theorem bind03009_0 : Agrees (spec (fastBase 0 41 57) layout0162) scope0415 := by decide

theorem reject03009 : Rejected (base 0 41 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0162 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 57) _ validLayout0162) (by decide) scope0415 (by rw [← fastBase_exact]; exact bind03009_0) certificate0438

private theorem bind03010_0 : Agrees (spec (fastBase 0 41 58) layout0165) scope0416 := by decide

theorem reject03010 : Rejected (base 0 41 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0165 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 58) _ validLayout0165) (by decide) scope0416 (by rw [← fastBase_exact]; exact bind03010_0) certificate0439

private theorem bind03011_0 : Agrees (spec (fastBase 0 41 59) layout0165) scope0417 := by decide

theorem reject03011 : Rejected (base 0 41 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0165 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 59) _ validLayout0165) (by decide) scope0417 (by rw [← fastBase_exact]; exact bind03011_0) certificate0440

private theorem bind03012_0 : Agrees (spec (fastBase 0 41 60) layout0161) scope0300 := by decide

private theorem bind03012_1 : Agrees (spec (fastBase 0 41 60) layout0162) scope0301 := by decide

theorem reject03012 : Rejected (base 0 41 60) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0161 layout0162 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 60) _ validLayout0161) (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 60) _ validLayout0162) (by decide) (by decide) scope0300 scope0301 (by rw [← fastBase_exact]; exact bind03012_0) (by rw [← fastBase_exact]; exact bind03012_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0305 certificate0306 (by decide)

private theorem bind03013_0 : Agrees (spec (fastBase 0 41 61) layout0165) scope0406 := by decide

theorem reject03013 : Rejected (base 0 41 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0165 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 61) _ validLayout0165) (by decide) scope0406 (by rw [← fastBase_exact]; exact bind03013_0) certificate0423

private theorem bind03014_0 : Agrees (spec (fastBase 0 41 62) layout0161) scope0298 := by decide

theorem reject03014 : Rejected (base 0 41 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 62) _ validLayout0161) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind03014_0) certificate0303

private theorem bind03015_0 : Agrees (spec (fastBase 0 41 63) layout0161) scope0308 := by decide

theorem reject03015 : Rejected (base 0 41 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 63) _ validLayout0161) (by decide) scope0308 (by rw [← fastBase_exact]; exact bind03015_0) certificate0313

private theorem bind03016_0 : Agrees (spec (fastBase 0 41 64) layout0163) scope0167 := by decide

theorem reject03016 : Rejected (base 0 41 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0163 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 64) _ validLayout0163) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind03016_0) certificate0170

private theorem bind03017_0 : Agrees (spec (fastBase 0 41 65) layout0161) scope0296 := by decide

theorem reject03017 : Rejected (base 0 41 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 65) _ validLayout0161) (by decide) scope0296 (by rw [← fastBase_exact]; exact bind03017_0) certificate0301

private theorem bind03018_0 : Agrees (spec (fastBase 0 41 66) layout0161) scope0295 := by decide

theorem reject03018 : Rejected (base 0 41 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 66) _ validLayout0161) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind03018_0) certificate0300

private theorem bind03019_0 : Agrees (spec (fastBase 0 41 67) layout0161) scope0311 := by decide

theorem reject03019 : Rejected (base 0 41 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 67) _ validLayout0161) (by decide) scope0311 (by rw [← fastBase_exact]; exact bind03019_0) certificate0316

private theorem bind03020_0 : Agrees (spec (fastBase 0 41 68) layout0161) scope0310 := by decide

theorem reject03020 : Rejected (base 0 41 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 68) _ validLayout0161) (by decide) scope0310 (by rw [← fastBase_exact]; exact bind03020_0) certificate0315

private theorem bind03021_0 : Agrees (spec (fastBase 0 41 69) layout0161) scope0297 := by decide

theorem reject03021 : Rejected (base 0 41 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 69) _ validLayout0161) (by decide) scope0297 (by rw [← fastBase_exact]; exact bind03021_0) certificate0302

private theorem bind03022_0 : Agrees (spec (fastBase 0 41 70) layout0161) scope0295 := by decide

theorem reject03022 : Rejected (base 0 41 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 70) _ validLayout0161) (by decide) scope0295 (by rw [← fastBase_exact]; exact bind03022_0) certificate0300

private theorem bind03023_0 : Agrees (spec (fastBase 0 41 71) layout0161) scope0298 := by decide

theorem reject03023 : Rejected (base 0 41 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0161 (layoutValid_of_refines _ _ (base_refines_skeleton 0 41 71) _ validLayout0161) (by decide) scope0298 (by rw [← fastBase_exact]; exact bind03023_0) certificate0303

theorem allCases041 : ∀ y : Fin 72, Rejected (base 0 41 y) := by
  intro y
  fin_cases y

  · exact reject02952

  · exact reject02953

  · exact reject02954

  · exact reject02955

  · exact reject02956

  · exact reject02957

  · exact reject02958

  · exact reject02959

  · exact reject02960

  · exact reject02961

  · exact reject02962

  · exact reject02963

  · exact reject02964

  · exact reject02965

  · exact reject02966

  · exact reject02967

  · exact reject02968

  · exact reject02969

  · exact reject02970

  · exact reject02971

  · exact reject02972

  · exact reject02973

  · exact reject02974

  · exact reject02975

  · exact reject02976

  · exact reject02977

  · exact reject02978

  · exact reject02979

  · exact reject02980

  · exact reject02981

  · exact reject02982

  · exact reject02983

  · exact reject02984

  · exact reject02985

  · exact reject02986

  · exact reject02987

  · exact reject02988

  · exact reject02989

  · exact reject02990

  · exact reject02991

  · exact reject02992

  · exact reject02993

  · exact reject02994

  · exact reject02995

  · exact reject02996

  · exact reject02997

  · exact reject02998

  · exact reject02999

  · exact reject03000

  · exact reject03001

  · exact reject03002

  · exact reject03003

  · exact reject03004

  · exact reject03005

  · exact reject03006

  · exact reject03007

  · exact reject03008

  · exact reject03009

  · exact reject03010

  · exact reject03011

  · exact reject03012

  · exact reject03013

  · exact reject03014

  · exact reject03015

  · exact reject03016

  · exact reject03017

  · exact reject03018

  · exact reject03019

  · exact reject03020

  · exact reject03021

  · exact reject03022

  · exact reject03023

end PricingIntegration.RemainingGWitnesses
