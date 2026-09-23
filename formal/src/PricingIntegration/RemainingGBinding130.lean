import PricingIntegration.RemainingGLayouts028

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks017

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks036


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind09360_0 : Agrees (spec (fastBase 1 58 0) layout0225) scope0399 := by decide

theorem reject09360 : Rejected (base 1 58 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 0) _ validLayout0225) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09360_0) certificate0412

private theorem bind09361_0 : Agrees (spec (fastBase 1 58 1) layout0225) scope0392 := by decide

theorem reject09361 : Rejected (base 1 58 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 1) _ validLayout0225) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09361_0) certificate0405

private theorem bind09362_0 : Agrees (spec (fastBase 1 58 2) layout0226) scope0267 := by decide

theorem reject09362 : Rejected (base 1 58 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 2) _ validLayout0226) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind09362_0) certificate0270

private theorem bind09363_0 : Agrees (spec (fastBase 1 58 3) layout0225) scope0137 := by decide

theorem reject09363 : Rejected (base 1 58 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 3) _ validLayout0225) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09363_0) certificate0140

private theorem bind09364_0 : Agrees (spec (fastBase 1 58 4) layout0225) scope0393 := by decide

theorem reject09364 : Rejected (base 1 58 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 4) _ validLayout0225) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09364_0) certificate0406

private theorem bind09365_0 : Agrees (spec (fastBase 1 58 5) layout0225) scope0400 := by decide

theorem reject09365 : Rejected (base 1 58 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 5) _ validLayout0225) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09365_0) certificate0413

private theorem bind09366_0 : Agrees (spec (fastBase 1 58 6) layout0225) scope0535 := by decide

theorem reject09366 : Rejected (base 1 58 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 6) _ validLayout0225) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09366_0) certificate0577

private theorem bind09367_0 : Agrees (spec (fastBase 1 58 7) layout0225) scope0133 := by decide

theorem reject09367 : Rejected (base 1 58 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 7) _ validLayout0225) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09367_0) certificate0136

private theorem bind09368_0 : Agrees (spec (fastBase 1 58 8) layout0225) scope0534 := by decide

theorem reject09368 : Rejected (base 1 58 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 8) _ validLayout0225) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09368_0) certificate0576

private theorem bind09369_0 : Agrees (spec (fastBase 1 58 9) layout0225) scope0537 := by decide

theorem reject09369 : Rejected (base 1 58 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 9) _ validLayout0225) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09369_0) certificate0579

private theorem bind09370_0 : Agrees (spec (fastBase 1 58 10) layout0226) scope0290 := by decide

private theorem bind09370_1 : Agrees (spec (fastBase 1 58 10) layout0227) scope0273 := by decide

theorem reject09370 : Rejected (base 1 58 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0226 layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 10) _ validLayout0226) (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 10) _ validLayout0227) (by decide) (by decide) scope0290 scope0273 (by rw [← fastBase_exact]; exact bind09370_0) (by rw [← fastBase_exact]; exact bind09370_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0293 certificate0276 (by decide)

private theorem bind09371_0 : Agrees (spec (fastBase 1 58 11) layout0225) scope0536 := by decide

theorem reject09371 : Rejected (base 1 58 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 11) _ validLayout0225) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09371_0) certificate0578

private theorem bind09372_0 : Agrees (spec (fastBase 1 58 12) layout0225) scope0399 := by decide

theorem reject09372 : Rejected (base 1 58 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 12) _ validLayout0225) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09372_0) certificate0412

private theorem bind09373_0 : Agrees (spec (fastBase 1 58 13) layout0226) scope0267 := by decide

theorem reject09373 : Rejected (base 1 58 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 13) _ validLayout0226) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind09373_0) certificate0270

private theorem bind09374_0 : Agrees (spec (fastBase 1 58 14) layout0225) scope0394 := by decide

theorem reject09374 : Rejected (base 1 58 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 14) _ validLayout0225) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind09374_0) certificate0407

private theorem bind09375_0 : Agrees (spec (fastBase 1 58 15) layout0225) scope0133 := by decide

theorem reject09375 : Rejected (base 1 58 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 15) _ validLayout0225) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09375_0) certificate0136

private theorem bind09376_0 : Agrees (spec (fastBase 1 58 16) layout0226) scope0283 := by decide

theorem reject09376 : Rejected (base 1 58 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 16) _ validLayout0226) (by decide) scope0283 (by rw [← fastBase_exact]; exact bind09376_0) certificate0286

private theorem bind09377_0 : Agrees (spec (fastBase 1 58 17) layout0225) scope0392 := by decide

theorem reject09377 : Rejected (base 1 58 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 17) _ validLayout0225) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09377_0) certificate0405

private theorem bind09378_0 : Agrees (spec (fastBase 1 58 18) layout0225) scope0392 := by decide

theorem reject09378 : Rejected (base 1 58 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 18) _ validLayout0225) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09378_0) certificate0405

private theorem bind09379_0 : Agrees (spec (fastBase 1 58 19) layout0225) scope0392 := by decide

theorem reject09379 : Rejected (base 1 58 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 19) _ validLayout0225) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09379_0) certificate0405

private theorem bind09380_0 : Agrees (spec (fastBase 1 58 20) layout0225) scope0392 := by decide

theorem reject09380 : Rejected (base 1 58 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 20) _ validLayout0225) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09380_0) certificate0405

private theorem bind09381_0 : Agrees (spec (fastBase 1 58 21) layout0225) scope0392 := by decide

theorem reject09381 : Rejected (base 1 58 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 21) _ validLayout0225) (by decide) scope0392 (by rw [← fastBase_exact]; exact bind09381_0) certificate0405

private theorem bind09382_0 : Agrees (spec (fastBase 1 58 22) layout0225) scope0399 := by decide

theorem reject09382 : Rejected (base 1 58 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 22) _ validLayout0225) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09382_0) certificate0412

private theorem bind09383_0 : Agrees (spec (fastBase 1 58 23) layout0225) scope0396 := by decide

theorem reject09383 : Rejected (base 1 58 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 23) _ validLayout0225) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind09383_0) certificate0409

private theorem bind09384_0 : Agrees (spec (fastBase 1 58 24) layout0225) scope0137 := by decide

theorem reject09384 : Rejected (base 1 58 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 24) _ validLayout0225) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09384_0) certificate0140

private theorem bind09385_0 : Agrees (spec (fastBase 1 58 25) layout0225) scope0544 := by decide

theorem reject09385 : Rejected (base 1 58 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 25) _ validLayout0225) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind09385_0) certificate0586

private theorem bind09386_0 : Agrees (spec (fastBase 1 58 26) layout0226) scope0267 := by decide

theorem reject09386 : Rejected (base 1 58 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 26) _ validLayout0226) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind09386_0) certificate0270

private theorem bind09387_0 : Agrees (spec (fastBase 1 58 27) layout0225) scope0137 := by decide

theorem reject09387 : Rejected (base 1 58 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 27) _ validLayout0225) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09387_0) certificate0140

private theorem bind09388_0 : Agrees (spec (fastBase 1 58 28) layout0227) scope0288 := by decide

theorem reject09388 : Rejected (base 1 58 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 28) _ validLayout0227) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09388_0) certificate0291

private theorem bind09389_0 : Agrees (spec (fastBase 1 58 29) layout0225) scope0400 := by decide

theorem reject09389 : Rejected (base 1 58 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 29) _ validLayout0225) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09389_0) certificate0413

private theorem bind09390_0 : Agrees (spec (fastBase 1 58 30) layout0225) scope0394 := by decide

theorem reject09390 : Rejected (base 1 58 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 30) _ validLayout0225) (by decide) scope0394 (by rw [← fastBase_exact]; exact bind09390_0) certificate0407

private theorem bind09391_0 : Agrees (spec (fastBase 1 58 31) layout0226) scope0282 := by decide

theorem reject09391 : Rejected (base 1 58 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 31) _ validLayout0226) (by decide) scope0282 (by rw [← fastBase_exact]; exact bind09391_0) certificate0285

private theorem bind09392_0 : Agrees (spec (fastBase 1 58 32) layout0225) scope0393 := by decide

theorem reject09392 : Rejected (base 1 58 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 32) _ validLayout0225) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09392_0) certificate0406

private theorem bind09393_0 : Agrees (spec (fastBase 1 58 33) layout0226) scope0269 := by decide

theorem reject09393 : Rejected (base 1 58 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 33) _ validLayout0226) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind09393_0) certificate0272

private theorem bind09394_0 : Agrees (spec (fastBase 1 58 34) layout0225) scope0400 := by decide

theorem reject09394 : Rejected (base 1 58 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 34) _ validLayout0225) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09394_0) certificate0413

private theorem bind09395_0 : Agrees (spec (fastBase 1 58 35) layout0225) scope0542 := by decide

theorem reject09395 : Rejected (base 1 58 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 35) _ validLayout0225) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind09395_0) certificate0584

private theorem bind09396_0 : Agrees (spec (fastBase 1 58 36) layout0225) scope0536 := by decide

theorem reject09396 : Rejected (base 1 58 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 36) _ validLayout0225) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09396_0) certificate0578

private theorem bind09397_0 : Agrees (spec (fastBase 1 58 37) layout0225) scope0396 := by decide

theorem reject09397 : Rejected (base 1 58 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 37) _ validLayout0225) (by decide) scope0396 (by rw [← fastBase_exact]; exact bind09397_0) certificate0409

private theorem bind09398_0 : Agrees (spec (fastBase 1 58 38) layout0225) scope0393 := by decide

theorem reject09398 : Rejected (base 1 58 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 38) _ validLayout0225) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09398_0) certificate0406

private theorem bind09399_0 : Agrees (spec (fastBase 1 58 39) layout0225) scope0137 := by decide

theorem reject09399 : Rejected (base 1 58 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 39) _ validLayout0225) (by decide) scope0137 (by rw [← fastBase_exact]; exact bind09399_0) certificate0140

private theorem bind09400_0 : Agrees (spec (fastBase 1 58 40) layout0225) scope0543 := by decide

theorem reject09400 : Rejected (base 1 58 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 40) _ validLayout0225) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind09400_0) certificate0585

private theorem bind09401_0 : Agrees (spec (fastBase 1 58 41) layout0225) scope0400 := by decide

theorem reject09401 : Rejected (base 1 58 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 41) _ validLayout0225) (by decide) scope0400 (by rw [← fastBase_exact]; exact bind09401_0) certificate0413

private theorem bind09402_0 : Agrees (spec (fastBase 1 58 42) layout0225) scope0535 := by decide

theorem reject09402 : Rejected (base 1 58 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 42) _ validLayout0225) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09402_0) certificate0577

private theorem bind09403_0 : Agrees (spec (fastBase 1 58 43) layout0226) scope0287 := by decide

theorem reject09403 : Rejected (base 1 58 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 43) _ validLayout0226) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind09403_0) certificate0290

private theorem bind09404_0 : Agrees (spec (fastBase 1 58 44) layout0225) scope0534 := by decide

theorem reject09404 : Rejected (base 1 58 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 44) _ validLayout0225) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09404_0) certificate0576

private theorem bind09405_0 : Agrees (spec (fastBase 1 58 45) layout0225) scope0133 := by decide

theorem reject09405 : Rejected (base 1 58 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 45) _ validLayout0225) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09405_0) certificate0136

private theorem bind09406_0 : Agrees (spec (fastBase 1 58 46) layout0225) scope0395 := by decide

theorem reject09406 : Rejected (base 1 58 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 46) _ validLayout0225) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind09406_0) certificate0408

private theorem bind09407_0 : Agrees (spec (fastBase 1 58 47) layout0225) scope0399 := by decide

theorem reject09407 : Rejected (base 1 58 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 47) _ validLayout0225) (by decide) scope0399 (by rw [← fastBase_exact]; exact bind09407_0) certificate0412

private theorem bind09408_0 : Agrees (spec (fastBase 1 58 48) layout0225) scope0544 := by decide

theorem reject09408 : Rejected (base 1 58 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 48) _ validLayout0225) (by decide) scope0544 (by rw [← fastBase_exact]; exact bind09408_0) certificate0586

private theorem bind09409_0 : Agrees (spec (fastBase 1 58 49) layout0225) scope0535 := by decide

theorem reject09409 : Rejected (base 1 58 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 49) _ validLayout0225) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09409_0) certificate0577

private theorem bind09410_0 : Agrees (spec (fastBase 1 58 50) layout0225) scope0541 := by decide

theorem reject09410 : Rejected (base 1 58 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 50) _ validLayout0225) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind09410_0) certificate0583

private theorem bind09411_0 : Agrees (spec (fastBase 1 58 51) layout0225) scope0133 := by decide

theorem reject09411 : Rejected (base 1 58 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 51) _ validLayout0225) (by decide) scope0133 (by rw [← fastBase_exact]; exact bind09411_0) certificate0136

private theorem bind09412_0 : Agrees (spec (fastBase 1 58 52) layout0225) scope0541 := by decide

theorem reject09412 : Rejected (base 1 58 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 52) _ validLayout0225) (by decide) scope0541 (by rw [← fastBase_exact]; exact bind09412_0) certificate0583

private theorem bind09413_0 : Agrees (spec (fastBase 1 58 53) layout0225) scope0540 := by decide

theorem reject09413 : Rejected (base 1 58 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 53) _ validLayout0225) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind09413_0) certificate0582

private theorem bind09414_0 : Agrees (spec (fastBase 1 58 54) layout0225) scope0535 := by decide

theorem reject09414 : Rejected (base 1 58 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 54) _ validLayout0225) (by decide) scope0535 (by rw [← fastBase_exact]; exact bind09414_0) certificate0577

private theorem bind09415_0 : Agrees (spec (fastBase 1 58 55) layout0225) scope0537 := by decide

theorem reject09415 : Rejected (base 1 58 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 55) _ validLayout0225) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09415_0) certificate0579

private theorem bind09416_0 : Agrees (spec (fastBase 1 58 56) layout0225) scope0534 := by decide

theorem reject09416 : Rejected (base 1 58 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 56) _ validLayout0225) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09416_0) certificate0576

private theorem bind09417_0 : Agrees (spec (fastBase 1 58 57) layout0225) scope0537 := by decide

theorem reject09417 : Rejected (base 1 58 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 57) _ validLayout0225) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09417_0) certificate0579

private theorem bind09418_0 : Agrees (spec (fastBase 1 58 58) layout0225) scope0542 := by decide

theorem reject09418 : Rejected (base 1 58 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 58) _ validLayout0225) (by decide) scope0542 (by rw [← fastBase_exact]; exact bind09418_0) certificate0584

private theorem bind09419_0 : Agrees (spec (fastBase 1 58 59) layout0225) scope0534 := by decide

theorem reject09419 : Rejected (base 1 58 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 59) _ validLayout0225) (by decide) scope0534 (by rw [← fastBase_exact]; exact bind09419_0) certificate0576

private theorem bind09420_0 : Agrees (spec (fastBase 1 58 60) layout0225) scope0395 := by decide

theorem reject09420 : Rejected (base 1 58 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 60) _ validLayout0225) (by decide) scope0395 (by rw [← fastBase_exact]; exact bind09420_0) certificate0408

private theorem bind09421_0 : Agrees (spec (fastBase 1 58 61) layout0225) scope0536 := by decide

theorem reject09421 : Rejected (base 1 58 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 61) _ validLayout0225) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09421_0) certificate0578

private theorem bind09422_0 : Agrees (spec (fastBase 1 58 62) layout0227) scope0288 := by decide

theorem reject09422 : Rejected (base 1 58 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 62) _ validLayout0227) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind09422_0) certificate0291

private theorem bind09423_0 : Agrees (spec (fastBase 1 58 63) layout0226) scope0280 := by decide

theorem reject09423 : Rejected (base 1 58 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 63) _ validLayout0226) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind09423_0) certificate0283

private theorem bind09424_0 : Agrees (spec (fastBase 1 58 64) layout0226) scope0272 := by decide

private theorem bind09424_1 : Agrees (spec (fastBase 1 58 64) layout0227) scope0273 := by decide

theorem reject09424 : Rejected (base 1 58 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0226 layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 64) _ validLayout0226) (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 64) _ validLayout0227) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind09424_0) (by rw [← fastBase_exact]; exact bind09424_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind09425_0 : Agrees (spec (fastBase 1 58 65) layout0226) scope0274 := by decide

theorem reject09425 : Rejected (base 1 58 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 65) _ validLayout0226) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind09425_0) certificate0277

private theorem bind09426_0 : Agrees (spec (fastBase 1 58 66) layout0226) scope0287 := by decide

theorem reject09426 : Rejected (base 1 58 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 66) _ validLayout0226) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind09426_0) certificate0290

private theorem bind09427_0 : Agrees (spec (fastBase 1 58 67) layout0225) scope0543 := by decide

theorem reject09427 : Rejected (base 1 58 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 67) _ validLayout0225) (by decide) scope0543 (by rw [← fastBase_exact]; exact bind09427_0) certificate0585

private theorem bind09428_0 : Agrees (spec (fastBase 1 58 68) layout0225) scope0393 := by decide

theorem reject09428 : Rejected (base 1 58 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 68) _ validLayout0225) (by decide) scope0393 (by rw [← fastBase_exact]; exact bind09428_0) certificate0406

private theorem bind09429_0 : Agrees (spec (fastBase 1 58 69) layout0225) scope0540 := by decide

theorem reject09429 : Rejected (base 1 58 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 69) _ validLayout0225) (by decide) scope0540 (by rw [← fastBase_exact]; exact bind09429_0) certificate0582

private theorem bind09430_0 : Agrees (spec (fastBase 1 58 70) layout0225) scope0537 := by decide

theorem reject09430 : Rejected (base 1 58 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 70) _ validLayout0225) (by decide) scope0537 (by rw [← fastBase_exact]; exact bind09430_0) certificate0579

private theorem bind09431_0 : Agrees (spec (fastBase 1 58 71) layout0225) scope0536 := by decide

theorem reject09431 : Rejected (base 1 58 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 1 58 71) _ validLayout0225) (by decide) scope0536 (by rw [← fastBase_exact]; exact bind09431_0) certificate0578

theorem allCases130 : ∀ y : Fin 72, Rejected (base 1 58 y) := by
  intro y
  fin_cases y

  · exact reject09360

  · exact reject09361

  · exact reject09362

  · exact reject09363

  · exact reject09364

  · exact reject09365

  · exact reject09366

  · exact reject09367

  · exact reject09368

  · exact reject09369

  · exact reject09370

  · exact reject09371

  · exact reject09372

  · exact reject09373

  · exact reject09374

  · exact reject09375

  · exact reject09376

  · exact reject09377

  · exact reject09378

  · exact reject09379

  · exact reject09380

  · exact reject09381

  · exact reject09382

  · exact reject09383

  · exact reject09384

  · exact reject09385

  · exact reject09386

  · exact reject09387

  · exact reject09388

  · exact reject09389

  · exact reject09390

  · exact reject09391

  · exact reject09392

  · exact reject09393

  · exact reject09394

  · exact reject09395

  · exact reject09396

  · exact reject09397

  · exact reject09398

  · exact reject09399

  · exact reject09400

  · exact reject09401

  · exact reject09402

  · exact reject09403

  · exact reject09404

  · exact reject09405

  · exact reject09406

  · exact reject09407

  · exact reject09408

  · exact reject09409

  · exact reject09410

  · exact reject09411

  · exact reject09412

  · exact reject09413

  · exact reject09414

  · exact reject09415

  · exact reject09416

  · exact reject09417

  · exact reject09418

  · exact reject09419

  · exact reject09420

  · exact reject09421

  · exact reject09422

  · exact reject09423

  · exact reject09424

  · exact reject09425

  · exact reject09426

  · exact reject09427

  · exact reject09428

  · exact reject09429

  · exact reject09430

  · exact reject09431

end PricingIntegration.RemainingGWitnesses
