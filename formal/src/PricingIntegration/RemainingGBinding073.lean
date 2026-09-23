import PricingIntegration.RemainingGLayouts000

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks002

import PricingIntegration.RemainingGScopeChecks003

import PricingIntegration.RemainingGScopeChecks006

import PricingIntegration.RemainingGScopeChecks024

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks033

import PricingIntegration.RemainingGScopeChecks034


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind05256_0 : Agrees (spec (fastBase 1 1 0) layout0004) scope0385 := by decide

theorem reject05256 : Rejected (base 1 1 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 0) _ validLayout0004) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind05256_0) certificate0395

private theorem bind05257_0 : Agrees (spec (fastBase 1 1 1) layout0004) scope0388 := by decide

theorem reject05257 : Rejected (base 1 1 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 1) _ validLayout0004) (by decide) scope0388 (by rw [← fastBase_exact]; exact bind05257_0) certificate0400

private theorem bind05258_0 : Agrees (spec (fastBase 1 1 2) layout0004) scope0105 := by decide

theorem reject05258 : Rejected (base 1 1 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 2) _ validLayout0004) (by decide) scope0105 (by rw [← fastBase_exact]; exact bind05258_0) certificate0108

private theorem bind05259_0 : Agrees (spec (fastBase 1 1 3) layout0004) scope0387 := by decide

theorem reject05259 : Rejected (base 1 1 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 3) _ validLayout0004) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind05259_0) certificate0397

private theorem bind05260_0 : Agrees (spec (fastBase 1 1 4) layout0004) scope0106 := by decide

theorem reject05260 : Rejected (base 1 1 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 4) _ validLayout0004) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind05260_0) certificate0109

private theorem bind05261_0 : Agrees (spec (fastBase 1 1 5) layout0005) scope0031 := by decide

theorem reject05261 : Rejected (base 1 1 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 5) _ validLayout0005) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind05261_0) certificate0031

private theorem bind05262_0 : Agrees (spec (fastBase 1 1 6) layout0004) scope0391 := by decide

theorem reject05262 : Rejected (base 1 1 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 6) _ validLayout0004) (by decide) scope0391 (by rw [← fastBase_exact]; exact bind05262_0) certificate0404

private theorem bind05263_0 : Agrees (spec (fastBase 1 1 7) layout0004) scope0496 := by decide

theorem reject05263 : Rejected (base 1 1 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 7) _ validLayout0004) (by decide) scope0496 (by rw [← fastBase_exact]; exact bind05263_0) certificate0538

private theorem bind05264_0 : Agrees (spec (fastBase 1 1 8) layout0004) scope0497 := by decide

theorem reject05264 : Rejected (base 1 1 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 8) _ validLayout0004) (by decide) scope0497 (by rw [← fastBase_exact]; exact bind05264_0) certificate0539

private theorem bind05265_0 : Agrees (spec (fastBase 1 1 9) layout0004) scope0386 := by decide

theorem reject05265 : Rejected (base 1 1 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 9) _ validLayout0004) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind05265_0) certificate0396

private theorem bind05266_0 : Agrees (spec (fastBase 1 1 10) layout0005) scope0038 := by decide

theorem reject05266 : Rejected (base 1 1 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 10) _ validLayout0005) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind05266_0) certificate0038

private theorem bind05267_0 : Agrees (spec (fastBase 1 1 11) layout0004) scope0498 := by decide

theorem reject05267 : Rejected (base 1 1 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 11) _ validLayout0004) (by decide) scope0498 (by rw [← fastBase_exact]; exact bind05267_0) certificate0540

private theorem bind05268_0 : Agrees (spec (fastBase 1 1 12) layout0004) scope0388 := by decide

theorem reject05268 : Rejected (base 1 1 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 12) _ validLayout0004) (by decide) scope0388 (by rw [← fastBase_exact]; exact bind05268_0) certificate0400

private theorem bind05269_0 : Agrees (spec (fastBase 1 1 13) layout0004) scope0499 := by decide

theorem reject05269 : Rejected (base 1 1 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 13) _ validLayout0004) (by decide) scope0499 (by rw [← fastBase_exact]; exact bind05269_0) certificate0541

private theorem bind05270_0 : Agrees (spec (fastBase 1 1 14) layout0004) scope0385 := by decide

theorem reject05270 : Rejected (base 1 1 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 14) _ validLayout0004) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind05270_0) certificate0395

private theorem bind05271_0 : Agrees (spec (fastBase 1 1 15) layout0004) scope0496 := by decide

theorem reject05271 : Rejected (base 1 1 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 15) _ validLayout0004) (by decide) scope0496 (by rw [← fastBase_exact]; exact bind05271_0) certificate0538

private theorem bind05272_0 : Agrees (spec (fastBase 1 1 16) layout0004) scope0500 := by decide

theorem reject05272 : Rejected (base 1 1 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 16) _ validLayout0004) (by decide) scope0500 (by rw [← fastBase_exact]; exact bind05272_0) certificate0542

private theorem bind05273_0 : Agrees (spec (fastBase 1 1 17) layout0004) scope0385 := by decide

theorem reject05273 : Rejected (base 1 1 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 17) _ validLayout0004) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind05273_0) certificate0395

private theorem bind05274_0 : Agrees (spec (fastBase 1 1 18) layout0004) scope0501 := by decide

theorem reject05274 : Rejected (base 1 1 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 18) _ validLayout0004) (by decide) scope0501 (by rw [← fastBase_exact]; exact bind05274_0) certificate0543

private theorem bind05275_0 : Agrees (spec (fastBase 1 1 19) layout0004) scope0390 := by decide

theorem reject05275 : Rejected (base 1 1 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 19) _ validLayout0004) (by decide) scope0390 (by rw [← fastBase_exact]; exact bind05275_0) certificate0403

private theorem bind05276_0 : Agrees (spec (fastBase 1 1 20) layout0004) scope0388 := by decide

theorem reject05276 : Rejected (base 1 1 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 20) _ validLayout0004) (by decide) scope0388 (by rw [← fastBase_exact]; exact bind05276_0) certificate0400

private theorem bind05277_0 : Agrees (spec (fastBase 1 1 21) layout0004) scope0386 := by decide

theorem reject05277 : Rejected (base 1 1 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 21) _ validLayout0004) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind05277_0) certificate0396

private theorem bind05278_0 : Agrees (spec (fastBase 1 1 22) layout0005) scope0043 := by decide

theorem reject05278 : Rejected (base 1 1 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 22) _ validLayout0005) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind05278_0) certificate0043

private theorem bind05279_0 : Agrees (spec (fastBase 1 1 23) layout0004) scope0502 := by decide

theorem reject05279 : Rejected (base 1 1 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 23) _ validLayout0004) (by decide) scope0502 (by rw [← fastBase_exact]; exact bind05279_0) certificate0544

private theorem bind05280_0 : Agrees (spec (fastBase 1 1 24) layout0004) scope0387 := by decide

theorem reject05280 : Rejected (base 1 1 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 24) _ validLayout0004) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind05280_0) certificate0397

private theorem bind05281_0 : Agrees (spec (fastBase 1 1 25) layout0004) scope0105 := by decide

theorem reject05281 : Rejected (base 1 1 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 25) _ validLayout0004) (by decide) scope0105 (by rw [← fastBase_exact]; exact bind05281_0) certificate0108

private theorem bind05282_0 : Agrees (spec (fastBase 1 1 26) layout0005) scope0028 := by decide

theorem reject05282 : Rejected (base 1 1 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 26) _ validLayout0005) (by decide) scope0028 (by rw [← fastBase_exact]; exact bind05282_0) certificate0028

private theorem bind05283_0 : Agrees (spec (fastBase 1 1 27) layout0004) scope0499 := by decide

theorem reject05283 : Rejected (base 1 1 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 27) _ validLayout0004) (by decide) scope0499 (by rw [← fastBase_exact]; exact bind05283_0) certificate0541

private theorem bind05284_0 : Agrees (spec (fastBase 1 1 28) layout0004) scope0105 := by decide

theorem reject05284 : Rejected (base 1 1 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 28) _ validLayout0004) (by decide) scope0105 (by rw [← fastBase_exact]; exact bind05284_0) certificate0108

private theorem bind05285_0 : Agrees (spec (fastBase 1 1 29) layout0004) scope0387 := by decide

theorem reject05285 : Rejected (base 1 1 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 29) _ validLayout0004) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind05285_0) certificate0397

private theorem bind05286_0 : Agrees (spec (fastBase 1 1 30) layout0004) scope0496 := by decide

theorem reject05286 : Rejected (base 1 1 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 30) _ validLayout0004) (by decide) scope0496 (by rw [← fastBase_exact]; exact bind05286_0) certificate0538

private theorem bind05287_0 : Agrees (spec (fastBase 1 1 31) layout0004) scope0503 := by decide

theorem reject05287 : Rejected (base 1 1 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 31) _ validLayout0004) (by decide) scope0503 (by rw [← fastBase_exact]; exact bind05287_0) certificate0545

private theorem bind05288_0 : Agrees (spec (fastBase 1 1 32) layout0004) scope0504 := by decide

theorem reject05288 : Rejected (base 1 1 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 32) _ validLayout0004) (by decide) scope0504 (by rw [← fastBase_exact]; exact bind05288_0) certificate0546

private theorem bind05289_0 : Agrees (spec (fastBase 1 1 33) layout0004) scope0505 := by decide

theorem reject05289 : Rejected (base 1 1 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 33) _ validLayout0004) (by decide) scope0505 (by rw [← fastBase_exact]; exact bind05289_0) certificate0547

private theorem bind05290_0 : Agrees (spec (fastBase 1 1 34) layout0004) scope0106 := by decide

theorem reject05290 : Rejected (base 1 1 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 34) _ validLayout0004) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind05290_0) certificate0109

private theorem bind05291_0 : Agrees (spec (fastBase 1 1 35) layout0004) scope0497 := by decide

theorem reject05291 : Rejected (base 1 1 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 35) _ validLayout0004) (by decide) scope0497 (by rw [← fastBase_exact]; exact bind05291_0) certificate0539

private theorem bind05292_0 : Agrees (spec (fastBase 1 1 36) layout0004) scope0498 := by decide

theorem reject05292 : Rejected (base 1 1 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 36) _ validLayout0004) (by decide) scope0498 (by rw [← fastBase_exact]; exact bind05292_0) certificate0540

private theorem bind05293_0 : Agrees (spec (fastBase 1 1 37) layout0005) scope0031 := by decide

theorem reject05293 : Rejected (base 1 1 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 37) _ validLayout0005) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind05293_0) certificate0031

private theorem bind05294_0 : Agrees (spec (fastBase 1 1 38) layout0005) scope0030 := by decide

theorem reject05294 : Rejected (base 1 1 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 38) _ validLayout0005) (by decide) scope0030 (by rw [← fastBase_exact]; exact bind05294_0) certificate0030

private theorem bind05295_0 : Agrees (spec (fastBase 1 1 39) layout0005) scope0031 := by decide

theorem reject05295 : Rejected (base 1 1 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 39) _ validLayout0005) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind05295_0) certificate0031

private theorem bind05296_0 : Agrees (spec (fastBase 1 1 40) layout0005) scope0037 := by decide

theorem reject05296 : Rejected (base 1 1 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 40) _ validLayout0005) (by decide) scope0037 (by rw [← fastBase_exact]; exact bind05296_0) certificate0037

private theorem bind05297_0 : Agrees (spec (fastBase 1 1 41) layout0005) scope0031 := by decide

theorem reject05297 : Rejected (base 1 1 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 41) _ validLayout0005) (by decide) scope0031 (by rw [← fastBase_exact]; exact bind05297_0) certificate0031

private theorem bind05298_0 : Agrees (spec (fastBase 1 1 42) layout0004) scope0391 := by decide

theorem reject05298 : Rejected (base 1 1 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 42) _ validLayout0004) (by decide) scope0391 (by rw [← fastBase_exact]; exact bind05298_0) certificate0404

private theorem bind05299_0 : Agrees (spec (fastBase 1 1 43) layout0004) scope0391 := by decide

theorem reject05299 : Rejected (base 1 1 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 43) _ validLayout0004) (by decide) scope0391 (by rw [← fastBase_exact]; exact bind05299_0) certificate0404

private theorem bind05300_0 : Agrees (spec (fastBase 1 1 44) layout0004) scope0391 := by decide

theorem reject05300 : Rejected (base 1 1 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 44) _ validLayout0004) (by decide) scope0391 (by rw [← fastBase_exact]; exact bind05300_0) certificate0404

private theorem bind05301_0 : Agrees (spec (fastBase 1 1 45) layout0004) scope0391 := by decide

theorem reject05301 : Rejected (base 1 1 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 45) _ validLayout0004) (by decide) scope0391 (by rw [← fastBase_exact]; exact bind05301_0) certificate0404

private theorem bind05302_0 : Agrees (spec (fastBase 1 1 46) layout0004) scope0391 := by decide

theorem reject05302 : Rejected (base 1 1 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 46) _ validLayout0004) (by decide) scope0391 (by rw [← fastBase_exact]; exact bind05302_0) certificate0404

private theorem bind05303_0 : Agrees (spec (fastBase 1 1 47) layout0004) scope0385 := by decide

theorem reject05303 : Rejected (base 1 1 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 47) _ validLayout0004) (by decide) scope0385 (by rw [← fastBase_exact]; exact bind05303_0) certificate0395

private theorem bind05304_0 : Agrees (spec (fastBase 1 1 48) layout0004) scope0387 := by decide

theorem reject05304 : Rejected (base 1 1 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 48) _ validLayout0004) (by decide) scope0387 (by rw [← fastBase_exact]; exact bind05304_0) certificate0397

private theorem bind05305_0 : Agrees (spec (fastBase 1 1 49) layout0004) scope0496 := by decide

theorem reject05305 : Rejected (base 1 1 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 49) _ validLayout0004) (by decide) scope0496 (by rw [← fastBase_exact]; exact bind05305_0) certificate0538

private theorem bind05306_0 : Agrees (spec (fastBase 1 1 50) layout0004) scope0501 := by decide

theorem reject05306 : Rejected (base 1 1 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 50) _ validLayout0004) (by decide) scope0501 (by rw [← fastBase_exact]; exact bind05306_0) certificate0543

private theorem bind05307_0 : Agrees (spec (fastBase 1 1 51) layout0005) scope0043 := by decide

theorem reject05307 : Rejected (base 1 1 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 51) _ validLayout0005) (by decide) scope0043 (by rw [← fastBase_exact]; exact bind05307_0) certificate0043

private theorem bind05308_0 : Agrees (spec (fastBase 1 1 52) layout0004) scope0390 := by decide

theorem reject05308 : Rejected (base 1 1 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 52) _ validLayout0004) (by decide) scope0390 (by rw [← fastBase_exact]; exact bind05308_0) certificate0403

private theorem bind05309_0 : Agrees (spec (fastBase 1 1 53) layout0004) scope0106 := by decide

theorem reject05309 : Rejected (base 1 1 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 53) _ validLayout0004) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind05309_0) certificate0109

private theorem bind05310_0 : Agrees (spec (fastBase 1 1 54) layout0004) scope0497 := by decide

theorem reject05310 : Rejected (base 1 1 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 54) _ validLayout0004) (by decide) scope0497 (by rw [← fastBase_exact]; exact bind05310_0) certificate0539

private theorem bind05311_0 : Agrees (spec (fastBase 1 1 55) layout0004) scope0386 := by decide

theorem reject05311 : Rejected (base 1 1 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 55) _ validLayout0004) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind05311_0) certificate0396

private theorem bind05312_0 : Agrees (spec (fastBase 1 1 56) layout0005) scope0047 := by decide

theorem reject05312 : Rejected (base 1 1 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 56) _ validLayout0005) (by decide) scope0047 (by rw [← fastBase_exact]; exact bind05312_0) certificate0047

private theorem bind05313_0 : Agrees (spec (fastBase 1 1 57) layout0004) scope0388 := by decide

theorem reject05313 : Rejected (base 1 1 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 57) _ validLayout0004) (by decide) scope0388 (by rw [← fastBase_exact]; exact bind05313_0) certificate0400

private theorem bind05314_0 : Agrees (spec (fastBase 1 1 58) layout0004) scope0386 := by decide

theorem reject05314 : Rejected (base 1 1 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 58) _ validLayout0004) (by decide) scope0386 (by rw [← fastBase_exact]; exact bind05314_0) certificate0396

private theorem bind05315_0 : Agrees (spec (fastBase 1 1 59) layout0004) scope0497 := by decide

theorem reject05315 : Rejected (base 1 1 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 59) _ validLayout0004) (by decide) scope0497 (by rw [← fastBase_exact]; exact bind05315_0) certificate0539

private theorem bind05316_0 : Agrees (spec (fastBase 1 1 60) layout0004) scope0500 := by decide

theorem reject05316 : Rejected (base 1 1 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 60) _ validLayout0004) (by decide) scope0500 (by rw [← fastBase_exact]; exact bind05316_0) certificate0542

private theorem bind05317_0 : Agrees (spec (fastBase 1 1 61) layout0004) scope0504 := by decide

theorem reject05317 : Rejected (base 1 1 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 61) _ validLayout0004) (by decide) scope0504 (by rw [← fastBase_exact]; exact bind05317_0) certificate0546

private theorem bind05318_0 : Agrees (spec (fastBase 1 1 62) layout0004) scope0105 := by decide

theorem reject05318 : Rejected (base 1 1 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 62) _ validLayout0004) (by decide) scope0105 (by rw [← fastBase_exact]; exact bind05318_0) certificate0108

private theorem bind05319_0 : Agrees (spec (fastBase 1 1 63) layout0005) scope0038 := by decide

theorem reject05319 : Rejected (base 1 1 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 63) _ validLayout0005) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind05319_0) certificate0038

private theorem bind05320_0 : Agrees (spec (fastBase 1 1 64) layout0004) scope0503 := by decide

theorem reject05320 : Rejected (base 1 1 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 64) _ validLayout0004) (by decide) scope0503 (by rw [← fastBase_exact]; exact bind05320_0) certificate0545

private theorem bind05321_0 : Agrees (spec (fastBase 1 1 65) layout0004) scope0505 := by decide

theorem reject05321 : Rejected (base 1 1 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 65) _ validLayout0004) (by decide) scope0505 (by rw [← fastBase_exact]; exact bind05321_0) certificate0547

private theorem bind05322_0 : Agrees (spec (fastBase 1 1 66) layout0004) scope0498 := by decide

theorem reject05322 : Rejected (base 1 1 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 66) _ validLayout0004) (by decide) scope0498 (by rw [← fastBase_exact]; exact bind05322_0) certificate0540

private theorem bind05323_0 : Agrees (spec (fastBase 1 1 67) layout0004) scope0502 := by decide

theorem reject05323 : Rejected (base 1 1 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 67) _ validLayout0004) (by decide) scope0502 (by rw [← fastBase_exact]; exact bind05323_0) certificate0544

private theorem bind05324_0 : Agrees (spec (fastBase 1 1 68) layout0004) scope0106 := by decide

theorem reject05324 : Rejected (base 1 1 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 68) _ validLayout0004) (by decide) scope0106 (by rw [← fastBase_exact]; exact bind05324_0) certificate0109

private theorem bind05325_0 : Agrees (spec (fastBase 1 1 69) layout0004) scope0498 := by decide

theorem reject05325 : Rejected (base 1 1 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0004 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 69) _ validLayout0004) (by decide) scope0498 (by rw [← fastBase_exact]; exact bind05325_0) certificate0540

private theorem bind05326_0 : Agrees (spec (fastBase 1 1 70) layout0005) scope0050 := by decide

theorem reject05326 : Rejected (base 1 1 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 70) _ validLayout0005) (by decide) scope0050 (by rw [← fastBase_exact]; exact bind05326_0) certificate0052

private theorem bind05327_0 : Agrees (spec (fastBase 1 1 71) layout0005) scope0038 := by decide

theorem reject05327 : Rejected (base 1 1 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0005 (layoutValid_of_refines _ _ (base_refines_skeleton 1 1 71) _ validLayout0005) (by decide) scope0038 (by rw [← fastBase_exact]; exact bind05327_0) certificate0038

theorem allCases073 : ∀ y : Fin 72, Rejected (base 1 1 y) := by
  intro y
  fin_cases y

  · exact reject05256

  · exact reject05257

  · exact reject05258

  · exact reject05259

  · exact reject05260

  · exact reject05261

  · exact reject05262

  · exact reject05263

  · exact reject05264

  · exact reject05265

  · exact reject05266

  · exact reject05267

  · exact reject05268

  · exact reject05269

  · exact reject05270

  · exact reject05271

  · exact reject05272

  · exact reject05273

  · exact reject05274

  · exact reject05275

  · exact reject05276

  · exact reject05277

  · exact reject05278

  · exact reject05279

  · exact reject05280

  · exact reject05281

  · exact reject05282

  · exact reject05283

  · exact reject05284

  · exact reject05285

  · exact reject05286

  · exact reject05287

  · exact reject05288

  · exact reject05289

  · exact reject05290

  · exact reject05291

  · exact reject05292

  · exact reject05293

  · exact reject05294

  · exact reject05295

  · exact reject05296

  · exact reject05297

  · exact reject05298

  · exact reject05299

  · exact reject05300

  · exact reject05301

  · exact reject05302

  · exact reject05303

  · exact reject05304

  · exact reject05305

  · exact reject05306

  · exact reject05307

  · exact reject05308

  · exact reject05309

  · exact reject05310

  · exact reject05311

  · exact reject05312

  · exact reject05313

  · exact reject05314

  · exact reject05315

  · exact reject05316

  · exact reject05317

  · exact reject05318

  · exact reject05319

  · exact reject05320

  · exact reject05321

  · exact reject05322

  · exact reject05323

  · exact reject05324

  · exact reject05325

  · exact reject05326

  · exact reject05327

end PricingIntegration.RemainingGWitnesses
