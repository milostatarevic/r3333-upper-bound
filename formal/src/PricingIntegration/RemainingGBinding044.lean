import PricingIntegration.RemainingGLayouts022

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks015

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks027

import PricingIntegration.RemainingGScopeChecks028


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind03168_0 : Agrees (spec (fastBase 0 44 0) layout0176) scope0240 := by decide

theorem reject03168 : Rejected (base 0 44 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 0) _ validLayout0176) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind03168_0) certificate0243

private theorem bind03169_0 : Agrees (spec (fastBase 0 44 1) layout0176) scope0239 := by decide

theorem reject03169 : Rejected (base 0 44 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 1) _ validLayout0176) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind03169_0) certificate0242

private theorem bind03170_0 : Agrees (spec (fastBase 0 44 2) layout0176) scope0246 := by decide

theorem reject03170 : Rejected (base 0 44 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 2) _ validLayout0176) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind03170_0) certificate0249

private theorem bind03171_0 : Agrees (spec (fastBase 0 44 3) layout0176) scope0247 := by decide

theorem reject03171 : Rejected (base 0 44 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 3) _ validLayout0176) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind03171_0) certificate0250

private theorem bind03172_0 : Agrees (spec (fastBase 0 44 4) layout0176) scope0248 := by decide

theorem reject03172 : Rejected (base 0 44 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 4) _ validLayout0176) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind03172_0) certificate0251

private theorem bind03173_0 : Agrees (spec (fastBase 0 44 5) layout0177) scope0249 := by decide

private theorem bind03173_1 : Agrees (spec (fastBase 0 44 5) layout0178) scope0425 := by decide

theorem reject03173 : Rejected (base 0 44 5) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 5) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 5) _ validLayout0178) (by decide) (by decide) scope0249 scope0425 (by rw [← fastBase_exact]; exact bind03173_0) (by rw [← fastBase_exact]; exact bind03173_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0449 certificate0450 (by decide)

private theorem bind03174_0 : Agrees (spec (fastBase 0 44 6) layout0176) scope0241 := by decide

theorem reject03174 : Rejected (base 0 44 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 6) _ validLayout0176) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind03174_0) certificate0244

private theorem bind03175_0 : Agrees (spec (fastBase 0 44 7) layout0176) scope0242 := by decide

theorem reject03175 : Rejected (base 0 44 7) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 7) _ validLayout0176) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind03175_0) certificate0245

private theorem bind03176_0 : Agrees (spec (fastBase 0 44 8) layout0176) scope0243 := by decide

theorem reject03176 : Rejected (base 0 44 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 8) _ validLayout0176) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind03176_0) certificate0246

private theorem bind03177_0 : Agrees (spec (fastBase 0 44 9) layout0177) scope0244 := by decide

private theorem bind03177_1 : Agrees (spec (fastBase 0 44 9) layout0178) scope0187 := by decide

theorem reject03177 : Rejected (base 0 44 9) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 9) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 9) _ validLayout0178) (by decide) (by decide) scope0244 scope0187 (by rw [← fastBase_exact]; exact bind03177_0) (by rw [← fastBase_exact]; exact bind03177_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0451 certificate0452 (by decide)

private theorem bind03178_0 : Agrees (spec (fastBase 0 44 10) layout0176) scope0252 := by decide

theorem reject03178 : Rejected (base 0 44 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 10) _ validLayout0176) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind03178_0) certificate0255

private theorem bind03179_0 : Agrees (spec (fastBase 0 44 11) layout0176) scope0251 := by decide

theorem reject03179 : Rejected (base 0 44 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 11) _ validLayout0176) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind03179_0) certificate0254

private theorem bind03180_0 : Agrees (spec (fastBase 0 44 12) layout0176) scope0255 := by decide

theorem reject03180 : Rejected (base 0 44 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 12) _ validLayout0176) (by decide) scope0255 (by rw [← fastBase_exact]; exact bind03180_0) certificate0258

private theorem bind03181_0 : Agrees (spec (fastBase 0 44 13) layout0176) scope0240 := by decide

theorem reject03181 : Rejected (base 0 44 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 13) _ validLayout0176) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind03181_0) certificate0243

private theorem bind03182_0 : Agrees (spec (fastBase 0 44 14) layout0177) scope0256 := by decide

theorem reject03182 : Rejected (base 0 44 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0177 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 14) _ validLayout0177) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind03182_0) certificate0259

private theorem bind03183_0 : Agrees (spec (fastBase 0 44 15) layout0176) scope0242 := by decide

theorem reject03183 : Rejected (base 0 44 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 15) _ validLayout0176) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind03183_0) certificate0245

private theorem bind03184_0 : Agrees (spec (fastBase 0 44 16) layout0176) scope0243 := by decide

theorem reject03184 : Rejected (base 0 44 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 16) _ validLayout0176) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind03184_0) certificate0246

private theorem bind03185_0 : Agrees (spec (fastBase 0 44 17) layout0176) scope0253 := by decide

theorem reject03185 : Rejected (base 0 44 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 17) _ validLayout0176) (by decide) scope0253 (by rw [← fastBase_exact]; exact bind03185_0) certificate0256

private theorem bind03186_0 : Agrees (spec (fastBase 0 44 18) layout0176) scope0254 := by decide

theorem reject03186 : Rejected (base 0 44 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 18) _ validLayout0176) (by decide) scope0254 (by rw [← fastBase_exact]; exact bind03186_0) certificate0257

private theorem bind03187_0 : Agrees (spec (fastBase 0 44 19) layout0176) scope0248 := by decide

theorem reject03187 : Rejected (base 0 44 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 19) _ validLayout0176) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind03187_0) certificate0251

private theorem bind03188_0 : Agrees (spec (fastBase 0 44 20) layout0176) scope0241 := by decide

theorem reject03188 : Rejected (base 0 44 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 20) _ validLayout0176) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind03188_0) certificate0244

private theorem bind03189_0 : Agrees (spec (fastBase 0 44 21) layout0176) scope0239 := by decide

theorem reject03189 : Rejected (base 0 44 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 21) _ validLayout0176) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind03189_0) certificate0242

private theorem bind03190_0 : Agrees (spec (fastBase 0 44 22) layout0176) scope0246 := by decide

theorem reject03190 : Rejected (base 0 44 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 22) _ validLayout0176) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind03190_0) certificate0249

private theorem bind03191_0 : Agrees (spec (fastBase 0 44 23) layout0176) scope0246 := by decide

theorem reject03191 : Rejected (base 0 44 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 23) _ validLayout0176) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind03191_0) certificate0249

private theorem bind03192_0 : Agrees (spec (fastBase 0 44 24) layout0176) scope0246 := by decide

theorem reject03192 : Rejected (base 0 44 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 24) _ validLayout0176) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind03192_0) certificate0249

private theorem bind03193_0 : Agrees (spec (fastBase 0 44 25) layout0176) scope0246 := by decide

theorem reject03193 : Rejected (base 0 44 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 25) _ validLayout0176) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind03193_0) certificate0249

private theorem bind03194_0 : Agrees (spec (fastBase 0 44 26) layout0176) scope0246 := by decide

theorem reject03194 : Rejected (base 0 44 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 26) _ validLayout0176) (by decide) scope0246 (by rw [← fastBase_exact]; exact bind03194_0) certificate0249

private theorem bind03195_0 : Agrees (spec (fastBase 0 44 27) layout0177) scope0426 := by decide

private theorem bind03195_1 : Agrees (spec (fastBase 0 44 27) layout0178) scope0427 := by decide

theorem reject03195 : Rejected (base 0 44 27) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 27) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 27) _ validLayout0178) (by decide) (by decide) scope0426 scope0427 (by rw [← fastBase_exact]; exact bind03195_0) (by rw [← fastBase_exact]; exact bind03195_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0453 certificate0454 (by decide)

private theorem bind03196_0 : Agrees (spec (fastBase 0 44 28) layout0176) scope0247 := by decide

theorem reject03196 : Rejected (base 0 44 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 28) _ validLayout0176) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind03196_0) certificate0250

private theorem bind03197_0 : Agrees (spec (fastBase 0 44 29) layout0177) scope0249 := by decide

private theorem bind03197_1 : Agrees (spec (fastBase 0 44 29) layout0178) scope0427 := by decide

theorem reject03197 : Rejected (base 0 44 29) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 29) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 29) _ validLayout0178) (by decide) (by decide) scope0249 scope0427 (by rw [← fastBase_exact]; exact bind03197_0) (by rw [← fastBase_exact]; exact bind03197_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0449 certificate0454 (by decide)

private theorem bind03198_0 : Agrees (spec (fastBase 0 44 30) layout0176) scope0261 := by decide

theorem reject03198 : Rejected (base 0 44 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 30) _ validLayout0176) (by decide) scope0261 (by rw [← fastBase_exact]; exact bind03198_0) certificate0264

private theorem bind03199_0 : Agrees (spec (fastBase 0 44 31) layout0176) scope0251 := by decide

theorem reject03199 : Rejected (base 0 44 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 31) _ validLayout0176) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind03199_0) certificate0254

private theorem bind03200_0 : Agrees (spec (fastBase 0 44 32) layout0176) scope0239 := by decide

theorem reject03200 : Rejected (base 0 44 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 32) _ validLayout0176) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind03200_0) certificate0242

private theorem bind03201_0 : Agrees (spec (fastBase 0 44 33) layout0176) scope0248 := by decide

theorem reject03201 : Rejected (base 0 44 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 33) _ validLayout0176) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind03201_0) certificate0251

private theorem bind03202_0 : Agrees (spec (fastBase 0 44 34) layout0177) scope0262 := by decide

theorem reject03202 : Rejected (base 0 44 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0177 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 34) _ validLayout0177) (by decide) scope0262 (by rw [← fastBase_exact]; exact bind03202_0) certificate0265

private theorem bind03203_0 : Agrees (spec (fastBase 0 44 35) layout0176) scope0257 := by decide

theorem reject03203 : Rejected (base 0 44 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 35) _ validLayout0176) (by decide) scope0257 (by rw [← fastBase_exact]; exact bind03203_0) certificate0260

private theorem bind03204_0 : Agrees (spec (fastBase 0 44 36) layout0176) scope0251 := by decide

theorem reject03204 : Rejected (base 0 44 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 36) _ validLayout0176) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind03204_0) certificate0254

private theorem bind03205_0 : Agrees (spec (fastBase 0 44 37) layout0176) scope0256 := by decide

theorem reject03205 : Rejected (base 0 44 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 37) _ validLayout0176) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind03205_0) certificate0259

private theorem bind03206_0 : Agrees (spec (fastBase 0 44 38) layout0176) scope0262 := by decide

theorem reject03206 : Rejected (base 0 44 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 38) _ validLayout0176) (by decide) scope0262 (by rw [← fastBase_exact]; exact bind03206_0) certificate0265

private theorem bind03207_0 : Agrees (spec (fastBase 0 44 39) layout0176) scope0247 := by decide

theorem reject03207 : Rejected (base 0 44 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 39) _ validLayout0176) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind03207_0) certificate0250

private theorem bind03208_0 : Agrees (spec (fastBase 0 44 40) layout0177) scope0249 := by decide

private theorem bind03208_1 : Agrees (spec (fastBase 0 44 40) layout0178) scope0187 := by decide

theorem reject03208 : Rejected (base 0 44 40) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 40) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 40) _ validLayout0178) (by decide) (by decide) scope0249 scope0187 (by rw [← fastBase_exact]; exact bind03208_0) (by rw [← fastBase_exact]; exact bind03208_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0449 certificate0452 (by decide)

private theorem bind03209_0 : Agrees (spec (fastBase 0 44 41) layout0176) scope0252 := by decide

theorem reject03209 : Rejected (base 0 44 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 41) _ validLayout0176) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind03209_0) certificate0255

private theorem bind03210_0 : Agrees (spec (fastBase 0 44 42) layout0176) scope0239 := by decide

theorem reject03210 : Rejected (base 0 44 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 42) _ validLayout0176) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind03210_0) certificate0242

private theorem bind03211_0 : Agrees (spec (fastBase 0 44 43) layout0176) scope0241 := by decide

theorem reject03211 : Rejected (base 0 44 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 43) _ validLayout0176) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind03211_0) certificate0244

private theorem bind03212_0 : Agrees (spec (fastBase 0 44 44) layout0176) scope0243 := by decide

theorem reject03212 : Rejected (base 0 44 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 44) _ validLayout0176) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind03212_0) certificate0246

private theorem bind03213_0 : Agrees (spec (fastBase 0 44 45) layout0176) scope0255 := by decide

theorem reject03213 : Rejected (base 0 44 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 45) _ validLayout0176) (by decide) scope0255 (by rw [← fastBase_exact]; exact bind03213_0) certificate0258

private theorem bind03214_0 : Agrees (spec (fastBase 0 44 46) layout0176) scope0257 := by decide

theorem reject03214 : Rejected (base 0 44 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 46) _ validLayout0176) (by decide) scope0257 (by rw [← fastBase_exact]; exact bind03214_0) certificate0260

private theorem bind03215_0 : Agrees (spec (fastBase 0 44 47) layout0176) scope0240 := by decide

theorem reject03215 : Rejected (base 0 44 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 47) _ validLayout0176) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind03215_0) certificate0243

private theorem bind03216_0 : Agrees (spec (fastBase 0 44 48) layout0176) scope0256 := by decide

theorem reject03216 : Rejected (base 0 44 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 48) _ validLayout0176) (by decide) scope0256 (by rw [← fastBase_exact]; exact bind03216_0) certificate0259

private theorem bind03217_0 : Agrees (spec (fastBase 0 44 49) layout0176) scope0258 := by decide

theorem reject03217 : Rejected (base 0 44 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 49) _ validLayout0176) (by decide) scope0258 (by rw [← fastBase_exact]; exact bind03217_0) certificate0261

private theorem bind03218_0 : Agrees (spec (fastBase 0 44 50) layout0176) scope0242 := by decide

theorem reject03218 : Rejected (base 0 44 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 50) _ validLayout0176) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind03218_0) certificate0245

private theorem bind03219_0 : Agrees (spec (fastBase 0 44 51) layout0176) scope0252 := by decide

theorem reject03219 : Rejected (base 0 44 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 51) _ validLayout0176) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind03219_0) certificate0255

private theorem bind03220_0 : Agrees (spec (fastBase 0 44 52) layout0176) scope0240 := by decide

theorem reject03220 : Rejected (base 0 44 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 52) _ validLayout0176) (by decide) scope0240 (by rw [← fastBase_exact]; exact bind03220_0) certificate0243

private theorem bind03221_0 : Agrees (spec (fastBase 0 44 53) layout0176) scope0253 := by decide

theorem reject03221 : Rejected (base 0 44 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 53) _ validLayout0176) (by decide) scope0253 (by rw [← fastBase_exact]; exact bind03221_0) certificate0256

private theorem bind03222_0 : Agrees (spec (fastBase 0 44 54) layout0176) scope0241 := by decide

theorem reject03222 : Rejected (base 0 44 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 54) _ validLayout0176) (by decide) scope0241 (by rw [← fastBase_exact]; exact bind03222_0) certificate0244

private theorem bind03223_0 : Agrees (spec (fastBase 0 44 55) layout0176) scope0243 := by decide

theorem reject03223 : Rejected (base 0 44 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 55) _ validLayout0176) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind03223_0) certificate0246

private theorem bind03224_0 : Agrees (spec (fastBase 0 44 56) layout0176) scope0258 := by decide

theorem reject03224 : Rejected (base 0 44 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 56) _ validLayout0176) (by decide) scope0258 (by rw [← fastBase_exact]; exact bind03224_0) certificate0261

private theorem bind03225_0 : Agrees (spec (fastBase 0 44 57) layout0177) scope0239 := by decide

theorem reject03225 : Rejected (base 0 44 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0177 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 57) _ validLayout0177) (by decide) scope0239 (by rw [← fastBase_exact]; exact bind03225_0) certificate0242

private theorem bind03226_0 : Agrees (spec (fastBase 0 44 58) layout0177) scope0244 := by decide

private theorem bind03226_1 : Agrees (spec (fastBase 0 44 58) layout0178) scope0425 := by decide

theorem reject03226 : Rejected (base 0 44 58) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 58) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 58) _ validLayout0178) (by decide) (by decide) scope0244 scope0425 (by rw [← fastBase_exact]; exact bind03226_0) (by rw [← fastBase_exact]; exact bind03226_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0451 certificate0450 (by decide)

private theorem bind03227_0 : Agrees (spec (fastBase 0 44 59) layout0177) scope0243 := by decide

theorem reject03227 : Rejected (base 0 44 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0177 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 59) _ validLayout0177) (by decide) scope0243 (by rw [← fastBase_exact]; exact bind03227_0) certificate0246

private theorem bind03228_0 : Agrees (spec (fastBase 0 44 60) layout0178) scope0423 := by decide

theorem reject03228 : Rejected (base 0 44 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 60) _ validLayout0178) (by decide) scope0423 (by rw [← fastBase_exact]; exact bind03228_0) certificate0447

private theorem bind03229_0 : Agrees (spec (fastBase 0 44 61) layout0177) scope0244 := by decide

private theorem bind03229_1 : Agrees (spec (fastBase 0 44 61) layout0178) scope0187 := by decide

theorem reject03229 : Rejected (base 0 44 61) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 61) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 61) _ validLayout0178) (by decide) (by decide) scope0244 scope0187 (by rw [← fastBase_exact]; exact bind03229_0) (by rw [← fastBase_exact]; exact bind03229_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0451 certificate0452 (by decide)

private theorem bind03230_0 : Agrees (spec (fastBase 0 44 62) layout0176) scope0252 := by decide

theorem reject03230 : Rejected (base 0 44 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 62) _ validLayout0176) (by decide) scope0252 (by rw [← fastBase_exact]; exact bind03230_0) certificate0255

private theorem bind03231_0 : Agrees (spec (fastBase 0 44 63) layout0177) scope0249 := by decide

private theorem bind03231_1 : Agrees (spec (fastBase 0 44 63) layout0178) scope0425 := by decide

theorem reject03231 : Rejected (base 0 44 63) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0177 layout0178 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 63) _ validLayout0177) (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 63) _ validLayout0178) (by decide) (by decide) scope0249 scope0425 (by rw [← fastBase_exact]; exact bind03231_0) (by rw [← fastBase_exact]; exact bind03231_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0449 certificate0450 (by decide)

private theorem bind03232_0 : Agrees (spec (fastBase 0 44 64) layout0176) scope0242 := by decide

theorem reject03232 : Rejected (base 0 44 64) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 64) _ validLayout0176) (by decide) scope0242 (by rw [← fastBase_exact]; exact bind03232_0) certificate0245

private theorem bind03233_0 : Agrees (spec (fastBase 0 44 65) layout0179) scope0428 := by decide

theorem reject03233 : Rejected (base 0 44 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0179 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 65) _ validLayout0179) (by decide) scope0428 (by rw [← fastBase_exact]; exact bind03233_0) certificate0455

private theorem bind03234_0 : Agrees (spec (fastBase 0 44 66) layout0176) scope0261 := by decide

theorem reject03234 : Rejected (base 0 44 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 66) _ validLayout0176) (by decide) scope0261 (by rw [← fastBase_exact]; exact bind03234_0) certificate0264

private theorem bind03235_0 : Agrees (spec (fastBase 0 44 67) layout0176) scope0247 := by decide

theorem reject03235 : Rejected (base 0 44 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 67) _ validLayout0176) (by decide) scope0247 (by rw [← fastBase_exact]; exact bind03235_0) certificate0250

private theorem bind03236_0 : Agrees (spec (fastBase 0 44 68) layout0176) scope0248 := by decide

theorem reject03236 : Rejected (base 0 44 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 68) _ validLayout0176) (by decide) scope0248 (by rw [← fastBase_exact]; exact bind03236_0) certificate0251

private theorem bind03237_0 : Agrees (spec (fastBase 0 44 69) layout0176) scope0254 := by decide

theorem reject03237 : Rejected (base 0 44 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 69) _ validLayout0176) (by decide) scope0254 (by rw [← fastBase_exact]; exact bind03237_0) certificate0257

private theorem bind03238_0 : Agrees (spec (fastBase 0 44 70) layout0176) scope0251 := by decide

theorem reject03238 : Rejected (base 0 44 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 70) _ validLayout0176) (by decide) scope0251 (by rw [← fastBase_exact]; exact bind03238_0) certificate0254

private theorem bind03239_0 : Agrees (spec (fastBase 0 44 71) layout0176) scope0262 := by decide

theorem reject03239 : Rejected (base 0 44 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0176 (layoutValid_of_refines _ _ (base_refines_skeleton 0 44 71) _ validLayout0176) (by decide) scope0262 (by rw [← fastBase_exact]; exact bind03239_0) certificate0265

theorem allCases044 : ∀ y : Fin 72, Rejected (base 0 44 y) := by
  intro y
  fin_cases y

  · exact reject03168

  · exact reject03169

  · exact reject03170

  · exact reject03171

  · exact reject03172

  · exact reject03173

  · exact reject03174

  · exact reject03175

  · exact reject03176

  · exact reject03177

  · exact reject03178

  · exact reject03179

  · exact reject03180

  · exact reject03181

  · exact reject03182

  · exact reject03183

  · exact reject03184

  · exact reject03185

  · exact reject03186

  · exact reject03187

  · exact reject03188

  · exact reject03189

  · exact reject03190

  · exact reject03191

  · exact reject03192

  · exact reject03193

  · exact reject03194

  · exact reject03195

  · exact reject03196

  · exact reject03197

  · exact reject03198

  · exact reject03199

  · exact reject03200

  · exact reject03201

  · exact reject03202

  · exact reject03203

  · exact reject03204

  · exact reject03205

  · exact reject03206

  · exact reject03207

  · exact reject03208

  · exact reject03209

  · exact reject03210

  · exact reject03211

  · exact reject03212

  · exact reject03213

  · exact reject03214

  · exact reject03215

  · exact reject03216

  · exact reject03217

  · exact reject03218

  · exact reject03219

  · exact reject03220

  · exact reject03221

  · exact reject03222

  · exact reject03223

  · exact reject03224

  · exact reject03225

  · exact reject03226

  · exact reject03227

  · exact reject03228

  · exact reject03229

  · exact reject03230

  · exact reject03231

  · exact reject03232

  · exact reject03233

  · exact reject03234

  · exact reject03235

  · exact reject03236

  · exact reject03237

  · exact reject03238

  · exact reject03239

end PricingIntegration.RemainingGWitnesses
