import PricingIntegration.RemainingGLayouts032

import PricingIntegration.RemainingGLayouts033

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks011

import PricingIntegration.RemainingGScopeChecks012

import PricingIntegration.RemainingGScopeChecks013

import PricingIntegration.RemainingGScopeChecks020

import PricingIntegration.RemainingGScopeChecks021

import PricingIntegration.RemainingGScopeChecks022

import PricingIntegration.RemainingGScopeChecks032


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind04968_0 : Agrees (spec (fastBase 0 69 0) layout0260) scope0323 := by decide

theorem reject04968 : Rejected (base 0 69 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 0) _ validLayout0260) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind04968_0) certificate0330

private theorem bind04969_0 : Agrees (spec (fastBase 0 69 1) layout0261) scope0191 := by decide

theorem reject04969 : Rejected (base 0 69 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 1) _ validLayout0261) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind04969_0) certificate0194

private theorem bind04970_0 : Agrees (spec (fastBase 0 69 2) layout0261) scope0177 := by decide

theorem reject04970 : Rejected (base 0 69 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 2) _ validLayout0261) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind04970_0) certificate0180

private theorem bind04971_0 : Agrees (spec (fastBase 0 69 3) layout0261) scope0184 := by decide

theorem reject04971 : Rejected (base 0 69 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 3) _ validLayout0261) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind04971_0) certificate0187

private theorem bind04972_0 : Agrees (spec (fastBase 0 69 4) layout0260) scope0327 := by decide

private theorem bind04972_1 : Agrees (spec (fastBase 0 69 4) layout0262) scope0180 := by decide

theorem reject04972 : Rejected (base 0 69 4) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 4) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 4) _ validLayout0262) (by decide) (by decide) scope0327 scope0180 (by rw [← fastBase_exact]; exact bind04972_0) (by rw [← fastBase_exact]; exact bind04972_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0519 (by decide)

private theorem bind04973_0 : Agrees (spec (fastBase 0 69 5) layout0261) scope0186 := by decide

theorem reject04973 : Rejected (base 0 69 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 5) _ validLayout0261) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind04973_0) certificate0189

private theorem bind04974_0 : Agrees (spec (fastBase 0 69 6) layout0260) scope0330 := by decide

theorem reject04974 : Rejected (base 0 69 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 6) _ validLayout0260) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind04974_0) certificate0337

private theorem bind04975_0 : Agrees (spec (fastBase 0 69 7) layout0261) scope0185 := by decide

theorem reject04975 : Rejected (base 0 69 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 7) _ validLayout0261) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind04975_0) certificate0188

private theorem bind04976_0 : Agrees (spec (fastBase 0 69 8) layout0260) scope0332 := by decide

private theorem bind04976_1 : Agrees (spec (fastBase 0 69 8) layout0262) scope0425 := by decide

theorem reject04976 : Rejected (base 0 69 8) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 8) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 8) _ validLayout0262) (by decide) (by decide) scope0332 scope0425 (by rw [← fastBase_exact]; exact bind04976_0) (by rw [← fastBase_exact]; exact bind04976_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0520 (by decide)

private theorem bind04977_0 : Agrees (spec (fastBase 0 69 9) layout0260) scope0334 := by decide

theorem reject04977 : Rejected (base 0 69 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 9) _ validLayout0260) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind04977_0) certificate0341

private theorem bind04978_0 : Agrees (spec (fastBase 0 69 10) layout0260) scope0335 := by decide

theorem reject04978 : Rejected (base 0 69 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 10) _ validLayout0260) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind04978_0) certificate0342

private theorem bind04979_0 : Agrees (spec (fastBase 0 69 11) layout0261) scope0176 := by decide

theorem reject04979 : Rejected (base 0 69 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 11) _ validLayout0261) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind04979_0) certificate0179

private theorem bind04980_0 : Agrees (spec (fastBase 0 69 12) layout0261) scope0207 := by decide

theorem reject04980 : Rejected (base 0 69 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 12) _ validLayout0261) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind04980_0) certificate0210

private theorem bind04981_0 : Agrees (spec (fastBase 0 69 13) layout0261) scope0193 := by decide

theorem reject04981 : Rejected (base 0 69 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 13) _ validLayout0261) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind04981_0) certificate0196

private theorem bind04982_0 : Agrees (spec (fastBase 0 69 14) layout0261) scope0186 := by decide

theorem reject04982 : Rejected (base 0 69 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 14) _ validLayout0261) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind04982_0) certificate0189

private theorem bind04983_0 : Agrees (spec (fastBase 0 69 15) layout0261) scope0185 := by decide

theorem reject04983 : Rejected (base 0 69 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 15) _ validLayout0261) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind04983_0) certificate0188

private theorem bind04984_0 : Agrees (spec (fastBase 0 69 16) layout0263) scope0338 := by decide

theorem reject04984 : Rejected (base 0 69 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0263 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 16) _ validLayout0263) (by decide) scope0338 (by rw [← fastBase_exact]; exact bind04984_0) certificate0345

private theorem bind04985_0 : Agrees (spec (fastBase 0 69 17) layout0261) scope0203 := by decide

theorem reject04985 : Rejected (base 0 69 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 17) _ validLayout0261) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind04985_0) certificate0206

private theorem bind04986_0 : Agrees (spec (fastBase 0 69 18) layout0261) scope0191 := by decide

theorem reject04986 : Rejected (base 0 69 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 18) _ validLayout0261) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind04986_0) certificate0194

private theorem bind04987_0 : Agrees (spec (fastBase 0 69 19) layout0261) scope0196 := by decide

theorem reject04987 : Rejected (base 0 69 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 19) _ validLayout0261) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind04987_0) certificate0199

private theorem bind04988_0 : Agrees (spec (fastBase 0 69 20) layout0260) scope0480 := by decide

private theorem bind04988_1 : Agrees (spec (fastBase 0 69 20) layout0262) scope0427 := by decide

theorem reject04988 : Rejected (base 0 69 20) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 20) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 20) _ validLayout0262) (by decide) (by decide) scope0480 scope0427 (by rw [← fastBase_exact]; exact bind04988_0) (by rw [← fastBase_exact]; exact bind04988_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0521 certificate0522 (by decide)

private theorem bind04989_0 : Agrees (spec (fastBase 0 69 21) layout0260) scope0334 := by decide

theorem reject04989 : Rejected (base 0 69 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 21) _ validLayout0260) (by decide) scope0334 (by rw [← fastBase_exact]; exact bind04989_0) certificate0341

private theorem bind04990_0 : Agrees (spec (fastBase 0 69 22) layout0261) scope0199 := by decide

theorem reject04990 : Rejected (base 0 69 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 22) _ validLayout0261) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind04990_0) certificate0202

private theorem bind04991_0 : Agrees (spec (fastBase 0 69 23) layout0260) scope0325 := by decide

theorem reject04991 : Rejected (base 0 69 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 23) _ validLayout0260) (by decide) scope0325 (by rw [← fastBase_exact]; exact bind04991_0) certificate0332

private theorem bind04992_0 : Agrees (spec (fastBase 0 69 24) layout0261) scope0177 := by decide

theorem reject04992 : Rejected (base 0 69 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 24) _ validLayout0261) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind04992_0) certificate0180

private theorem bind04993_0 : Agrees (spec (fastBase 0 69 25) layout0261) scope0194 := by decide

theorem reject04993 : Rejected (base 0 69 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 25) _ validLayout0261) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind04993_0) certificate0197

private theorem bind04994_0 : Agrees (spec (fastBase 0 69 26) layout0260) scope0335 := by decide

theorem reject04994 : Rejected (base 0 69 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 26) _ validLayout0260) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind04994_0) certificate0342

private theorem bind04995_0 : Agrees (spec (fastBase 0 69 27) layout0261) scope0184 := by decide

theorem reject04995 : Rejected (base 0 69 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 27) _ validLayout0261) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind04995_0) certificate0187

private theorem bind04996_0 : Agrees (spec (fastBase 0 69 28) layout0261) scope0184 := by decide

theorem reject04996 : Rejected (base 0 69 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 28) _ validLayout0261) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind04996_0) certificate0187

private theorem bind04997_0 : Agrees (spec (fastBase 0 69 29) layout0261) scope0184 := by decide

theorem reject04997 : Rejected (base 0 69 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 29) _ validLayout0261) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind04997_0) certificate0187

private theorem bind04998_0 : Agrees (spec (fastBase 0 69 30) layout0261) scope0184 := by decide

theorem reject04998 : Rejected (base 0 69 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 30) _ validLayout0261) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind04998_0) certificate0187

private theorem bind04999_0 : Agrees (spec (fastBase 0 69 31) layout0261) scope0184 := by decide

theorem reject04999 : Rejected (base 0 69 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 31) _ validLayout0261) (by decide) scope0184 (by rw [← fastBase_exact]; exact bind04999_0) certificate0187

private theorem bind05000_0 : Agrees (spec (fastBase 0 69 32) layout0261) scope0200 := by decide

theorem reject05000 : Rejected (base 0 69 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 32) _ validLayout0261) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind05000_0) certificate0203

private theorem bind05001_0 : Agrees (spec (fastBase 0 69 33) layout0261) scope0177 := by decide

theorem reject05001 : Rejected (base 0 69 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 33) _ validLayout0261) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind05001_0) certificate0180

private theorem bind05002_0 : Agrees (spec (fastBase 0 69 34) layout0261) scope0192 := by decide

theorem reject05002 : Rejected (base 0 69 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 34) _ validLayout0261) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind05002_0) certificate0195

private theorem bind05003_0 : Agrees (spec (fastBase 0 69 35) layout0260) scope0332 := by decide

private theorem bind05003_1 : Agrees (spec (fastBase 0 69 35) layout0262) scope0180 := by decide

theorem reject05003 : Rejected (base 0 69 35) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 35) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 35) _ validLayout0262) (by decide) (by decide) scope0332 scope0180 (by rw [← fastBase_exact]; exact bind05003_0) (by rw [← fastBase_exact]; exact bind05003_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0519 (by decide)

private theorem bind05004_0 : Agrees (spec (fastBase 0 69 36) layout0261) scope0176 := by decide

theorem reject05004 : Rejected (base 0 69 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 36) _ validLayout0261) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind05004_0) certificate0179

private theorem bind05005_0 : Agrees (spec (fastBase 0 69 37) layout0260) scope0323 := by decide

theorem reject05005 : Rejected (base 0 69 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 37) _ validLayout0260) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind05005_0) certificate0330

private theorem bind05006_0 : Agrees (spec (fastBase 0 69 38) layout0261) scope0199 := by decide

theorem reject05006 : Rejected (base 0 69 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 38) _ validLayout0261) (by decide) scope0199 (by rw [← fastBase_exact]; exact bind05006_0) certificate0202

private theorem bind05007_0 : Agrees (spec (fastBase 0 69 39) layout0261) scope0186 := by decide

theorem reject05007 : Rejected (base 0 69 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 39) _ validLayout0261) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind05007_0) certificate0189

private theorem bind05008_0 : Agrees (spec (fastBase 0 69 40) layout0261) scope0202 := by decide

theorem reject05008 : Rejected (base 0 69 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 40) _ validLayout0261) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind05008_0) certificate0205

private theorem bind05009_0 : Agrees (spec (fastBase 0 69 41) layout0264) scope0481 := by decide

theorem reject05009 : Rejected (base 0 69 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0264 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 41) _ validLayout0264) (by decide) scope0481 (by rw [← fastBase_exact]; exact bind05009_0) certificate0523

private theorem bind05010_0 : Agrees (spec (fastBase 0 69 42) layout0261) scope0191 := by decide

theorem reject05010 : Rejected (base 0 69 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 42) _ validLayout0261) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind05010_0) certificate0194

private theorem bind05011_0 : Agrees (spec (fastBase 0 69 43) layout0261) scope0200 := by decide

theorem reject05011 : Rejected (base 0 69 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 43) _ validLayout0261) (by decide) scope0200 (by rw [← fastBase_exact]; exact bind05011_0) certificate0203

private theorem bind05012_0 : Agrees (spec (fastBase 0 69 44) layout0260) scope0332 := by decide

private theorem bind05012_1 : Agrees (spec (fastBase 0 69 44) layout0262) scope0427 := by decide

theorem reject05012 : Rejected (base 0 69 44) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 44) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 44) _ validLayout0262) (by decide) (by decide) scope0332 scope0427 (by rw [← fastBase_exact]; exact bind05012_0) (by rw [← fastBase_exact]; exact bind05012_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0522 (by decide)

private theorem bind05013_0 : Agrees (spec (fastBase 0 69 45) layout0261) scope0201 := by decide

theorem reject05013 : Rejected (base 0 69 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 45) _ validLayout0261) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind05013_0) certificate0204

private theorem bind05014_0 : Agrees (spec (fastBase 0 69 46) layout0261) scope0176 := by decide

theorem reject05014 : Rejected (base 0 69 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 46) _ validLayout0261) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind05014_0) certificate0179

private theorem bind05015_0 : Agrees (spec (fastBase 0 69 47) layout0260) scope0323 := by decide

theorem reject05015 : Rejected (base 0 69 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 47) _ validLayout0260) (by decide) scope0323 (by rw [← fastBase_exact]; exact bind05015_0) certificate0330

private theorem bind05016_0 : Agrees (spec (fastBase 0 69 48) layout0261) scope0185 := by decide

theorem reject05016 : Rejected (base 0 69 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 48) _ validLayout0261) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind05016_0) certificate0188

private theorem bind05017_0 : Agrees (spec (fastBase 0 69 49) layout0261) scope0203 := by decide

theorem reject05017 : Rejected (base 0 69 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 49) _ validLayout0261) (by decide) scope0203 (by rw [← fastBase_exact]; exact bind05017_0) certificate0206

private theorem bind05018_0 : Agrees (spec (fastBase 0 69 50) layout0260) scope0331 := by decide

theorem reject05018 : Rejected (base 0 69 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 50) _ validLayout0260) (by decide) scope0331 (by rw [← fastBase_exact]; exact bind05018_0) certificate0338

private theorem bind05019_0 : Agrees (spec (fastBase 0 69 51) layout0261) scope0202 := by decide

theorem reject05019 : Rejected (base 0 69 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 51) _ validLayout0261) (by decide) scope0202 (by rw [← fastBase_exact]; exact bind05019_0) certificate0205

private theorem bind05020_0 : Agrees (spec (fastBase 0 69 52) layout0260) scope0342 := by decide

theorem reject05020 : Rejected (base 0 69 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 52) _ validLayout0260) (by decide) scope0342 (by rw [← fastBase_exact]; exact bind05020_0) certificate0349

private theorem bind05021_0 : Agrees (spec (fastBase 0 69 53) layout0260) scope0327 := by decide

private theorem bind05021_1 : Agrees (spec (fastBase 0 69 53) layout0262) scope0425 := by decide

theorem reject05021 : Rejected (base 0 69 53) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 53) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 53) _ validLayout0262) (by decide) (by decide) scope0327 scope0425 (by rw [← fastBase_exact]; exact bind05021_0) (by rw [← fastBase_exact]; exact bind05021_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0520 (by decide)

private theorem bind05022_0 : Agrees (spec (fastBase 0 69 54) layout0260) scope0330 := by decide

theorem reject05022 : Rejected (base 0 69 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 54) _ validLayout0260) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind05022_0) certificate0337

private theorem bind05023_0 : Agrees (spec (fastBase 0 69 55) layout0260) scope0347 := by decide

theorem reject05023 : Rejected (base 0 69 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 55) _ validLayout0260) (by decide) scope0347 (by rw [← fastBase_exact]; exact bind05023_0) certificate0354

private theorem bind05024_0 : Agrees (spec (fastBase 0 69 56) layout0260) scope0332 := by decide

private theorem bind05024_1 : Agrees (spec (fastBase 0 69 56) layout0262) scope0425 := by decide

theorem reject05024 : Rejected (base 0 69 56) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 56) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 56) _ validLayout0262) (by decide) (by decide) scope0332 scope0425 (by rw [← fastBase_exact]; exact bind05024_0) (by rw [← fastBase_exact]; exact bind05024_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0339 certificate0520 (by decide)

private theorem bind05025_0 : Agrees (spec (fastBase 0 69 57) layout0261) scope0191 := by decide

theorem reject05025 : Rejected (base 0 69 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 57) _ validLayout0261) (by decide) scope0191 (by rw [← fastBase_exact]; exact bind05025_0) certificate0194

private theorem bind05026_0 : Agrees (spec (fastBase 0 69 58) layout0261) scope0207 := by decide

theorem reject05026 : Rejected (base 0 69 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 58) _ validLayout0261) (by decide) scope0207 (by rw [← fastBase_exact]; exact bind05026_0) certificate0210

private theorem bind05027_0 : Agrees (spec (fastBase 0 69 59) layout0260) scope0480 := by decide

private theorem bind05027_1 : Agrees (spec (fastBase 0 69 59) layout0262) scope0425 := by decide

theorem reject05027 : Rejected (base 0 69 59) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 59) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 59) _ validLayout0262) (by decide) (by decide) scope0480 scope0425 (by rw [← fastBase_exact]; exact bind05027_0) (by rw [← fastBase_exact]; exact bind05027_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0521 certificate0520 (by decide)

private theorem bind05028_0 : Agrees (spec (fastBase 0 69 60) layout0261) scope0185 := by decide

theorem reject05028 : Rejected (base 0 69 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 60) _ validLayout0261) (by decide) scope0185 (by rw [← fastBase_exact]; exact bind05028_0) certificate0188

private theorem bind05029_0 : Agrees (spec (fastBase 0 69 61) layout0261) scope0201 := by decide

theorem reject05029 : Rejected (base 0 69 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 61) _ validLayout0261) (by decide) scope0201 (by rw [← fastBase_exact]; exact bind05029_0) certificate0204

private theorem bind05030_0 : Agrees (spec (fastBase 0 69 62) layout0261) scope0177 := by decide

theorem reject05030 : Rejected (base 0 69 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 62) _ validLayout0261) (by decide) scope0177 (by rw [← fastBase_exact]; exact bind05030_0) certificate0180

private theorem bind05031_0 : Agrees (spec (fastBase 0 69 63) layout0261) scope0186 := by decide

theorem reject05031 : Rejected (base 0 69 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 63) _ validLayout0261) (by decide) scope0186 (by rw [← fastBase_exact]; exact bind05031_0) certificate0189

private theorem bind05032_0 : Agrees (spec (fastBase 0 69 64) layout0261) scope0193 := by decide

theorem reject05032 : Rejected (base 0 69 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 64) _ validLayout0261) (by decide) scope0193 (by rw [← fastBase_exact]; exact bind05032_0) certificate0196

private theorem bind05033_0 : Agrees (spec (fastBase 0 69 65) layout0260) scope0335 := by decide

theorem reject05033 : Rejected (base 0 69 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 65) _ validLayout0260) (by decide) scope0335 (by rw [← fastBase_exact]; exact bind05033_0) certificate0342

private theorem bind05034_0 : Agrees (spec (fastBase 0 69 66) layout0261) scope0192 := by decide

theorem reject05034 : Rejected (base 0 69 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 66) _ validLayout0261) (by decide) scope0192 (by rw [← fastBase_exact]; exact bind05034_0) certificate0195

private theorem bind05035_0 : Agrees (spec (fastBase 0 69 67) layout0261) scope0176 := by decide

theorem reject05035 : Rejected (base 0 69 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 67) _ validLayout0261) (by decide) scope0176 (by rw [← fastBase_exact]; exact bind05035_0) certificate0179

private theorem bind05036_0 : Agrees (spec (fastBase 0 69 68) layout0260) scope0327 := by decide

private theorem bind05036_1 : Agrees (spec (fastBase 0 69 68) layout0262) scope0180 := by decide

theorem reject05036 : Rejected (base 0 69 68) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0260 layout0262 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 68) _ validLayout0260) (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 68) _ validLayout0262) (by decide) (by decide) scope0327 scope0180 (by rw [← fastBase_exact]; exact bind05036_0) (by rw [← fastBase_exact]; exact bind05036_1) 0 5 0 5 (by decide) (by decide) 2 3 (by decide) certificate0334 certificate0519 (by decide)

private theorem bind05037_0 : Agrees (spec (fastBase 0 69 69) layout0260) scope0330 := by decide

theorem reject05037 : Rejected (base 0 69 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0260 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 69) _ validLayout0260) (by decide) scope0330 (by rw [← fastBase_exact]; exact bind05037_0) certificate0337

private theorem bind05038_0 : Agrees (spec (fastBase 0 69 70) layout0261) scope0196 := by decide

theorem reject05038 : Rejected (base 0 69 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 70) _ validLayout0261) (by decide) scope0196 (by rw [← fastBase_exact]; exact bind05038_0) certificate0199

private theorem bind05039_0 : Agrees (spec (fastBase 0 69 71) layout0261) scope0194 := by decide

theorem reject05039 : Rejected (base 0 69 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0261 (layoutValid_of_refines _ _ (base_refines_skeleton 0 69 71) _ validLayout0261) (by decide) scope0194 (by rw [← fastBase_exact]; exact bind05039_0) certificate0197

theorem allCases069 : ∀ y : Fin 72, Rejected (base 0 69 y) := by
  intro y
  fin_cases y

  · exact reject04968

  · exact reject04969

  · exact reject04970

  · exact reject04971

  · exact reject04972

  · exact reject04973

  · exact reject04974

  · exact reject04975

  · exact reject04976

  · exact reject04977

  · exact reject04978

  · exact reject04979

  · exact reject04980

  · exact reject04981

  · exact reject04982

  · exact reject04983

  · exact reject04984

  · exact reject04985

  · exact reject04986

  · exact reject04987

  · exact reject04988

  · exact reject04989

  · exact reject04990

  · exact reject04991

  · exact reject04992

  · exact reject04993

  · exact reject04994

  · exact reject04995

  · exact reject04996

  · exact reject04997

  · exact reject04998

  · exact reject04999

  · exact reject05000

  · exact reject05001

  · exact reject05002

  · exact reject05003

  · exact reject05004

  · exact reject05005

  · exact reject05006

  · exact reject05007

  · exact reject05008

  · exact reject05009

  · exact reject05010

  · exact reject05011

  · exact reject05012

  · exact reject05013

  · exact reject05014

  · exact reject05015

  · exact reject05016

  · exact reject05017

  · exact reject05018

  · exact reject05019

  · exact reject05020

  · exact reject05021

  · exact reject05022

  · exact reject05023

  · exact reject05024

  · exact reject05025

  · exact reject05026

  · exact reject05027

  · exact reject05028

  · exact reject05029

  · exact reject05030

  · exact reject05031

  · exact reject05032

  · exact reject05033

  · exact reject05034

  · exact reject05035

  · exact reject05036

  · exact reject05037

  · exact reject05038

  · exact reject05039

end PricingIntegration.RemainingGWitnesses
