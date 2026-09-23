import PricingIntegration.RemainingGLayouts028

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks008

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks016

import PricingIntegration.RemainingGScopeChecks017

import PricingIntegration.RemainingGScopeChecks018

import PricingIntegration.RemainingGScopeChecks030

import PricingIntegration.RemainingGScopeChecks031


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind04176_0 : Agrees (spec (fastBase 0 58 0) layout0225) scope0150 := by decide

theorem reject04176 : Rejected (base 0 58 0) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 0) _ validLayout0225) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04176_0) certificate0153

private theorem bind04177_0 : Agrees (spec (fastBase 0 58 1) layout0225) scope0144 := by decide

theorem reject04177 : Rejected (base 0 58 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 1) _ validLayout0225) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04177_0) certificate0147

private theorem bind04178_0 : Agrees (spec (fastBase 0 58 2) layout0226) scope0267 := by decide

theorem reject04178 : Rejected (base 0 58 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 2) _ validLayout0226) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind04178_0) certificate0270

private theorem bind04179_0 : Agrees (spec (fastBase 0 58 3) layout0225) scope0155 := by decide

theorem reject04179 : Rejected (base 0 58 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 3) _ validLayout0225) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04179_0) certificate0158

private theorem bind04180_0 : Agrees (spec (fastBase 0 58 4) layout0225) scope0140 := by decide

theorem reject04180 : Rejected (base 0 58 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 4) _ validLayout0225) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04180_0) certificate0143

private theorem bind04181_0 : Agrees (spec (fastBase 0 58 5) layout0226) scope0270 := by decide

theorem reject04181 : Rejected (base 0 58 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 5) _ validLayout0226) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind04181_0) certificate0273

private theorem bind04182_0 : Agrees (spec (fastBase 0 58 6) layout0225) scope0141 := by decide

theorem reject04182 : Rejected (base 0 58 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 6) _ validLayout0225) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04182_0) certificate0144

private theorem bind04183_0 : Agrees (spec (fastBase 0 58 7) layout0226) scope0272 := by decide

private theorem bind04183_1 : Agrees (spec (fastBase 0 58 7) layout0227) scope0276 := by decide

theorem reject04183 : Rejected (base 0 58 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0226 layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 7) _ validLayout0226) (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 7) _ validLayout0227) (by decide) (by decide) scope0272 scope0276 (by rw [← fastBase_exact]; exact bind04183_0) (by rw [← fastBase_exact]; exact bind04183_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0295 certificate0296 (by decide)

private theorem bind04184_0 : Agrees (spec (fastBase 0 58 8) layout0226) scope0274 := by decide

theorem reject04184 : Rejected (base 0 58 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 8) _ validLayout0226) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind04184_0) certificate0277

private theorem bind04185_0 : Agrees (spec (fastBase 0 58 9) layout0225) scope0145 := by decide

theorem reject04185 : Rejected (base 0 58 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 9) _ validLayout0225) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04185_0) certificate0148

private theorem bind04186_0 : Agrees (spec (fastBase 0 58 10) layout0226) scope0290 := by decide

private theorem bind04186_1 : Agrees (spec (fastBase 0 58 10) layout0227) scope0273 := by decide

theorem reject04186 : Rejected (base 0 58 10) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0226 layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 10) _ validLayout0226) (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 10) _ validLayout0227) (by decide) (by decide) scope0290 scope0273 (by rw [← fastBase_exact]; exact bind04186_0) (by rw [← fastBase_exact]; exact bind04186_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0293 certificate0276 (by decide)

private theorem bind04187_0 : Agrees (spec (fastBase 0 58 11) layout0226) scope0278 := by decide

theorem reject04187 : Rejected (base 0 58 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 11) _ validLayout0226) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind04187_0) certificate0281

private theorem bind04188_0 : Agrees (spec (fastBase 0 58 12) layout0225) scope0150 := by decide

theorem reject04188 : Rejected (base 0 58 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 12) _ validLayout0225) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04188_0) certificate0153

private theorem bind04189_0 : Agrees (spec (fastBase 0 58 13) layout0226) scope0267 := by decide

theorem reject04189 : Rejected (base 0 58 13) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 13) _ validLayout0226) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind04189_0) certificate0270

private theorem bind04190_0 : Agrees (spec (fastBase 0 58 14) layout0225) scope0171 := by decide

theorem reject04190 : Rejected (base 0 58 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 14) _ validLayout0225) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind04190_0) certificate0174

private theorem bind04191_0 : Agrees (spec (fastBase 0 58 15) layout0226) scope0265 := by decide

theorem reject04191 : Rejected (base 0 58 15) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 15) _ validLayout0226) (by decide) scope0265 (by rw [← fastBase_exact]; exact bind04191_0) certificate0268

private theorem bind04192_0 : Agrees (spec (fastBase 0 58 16) layout0225) scope0163 := by decide

theorem reject04192 : Rejected (base 0 58 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 16) _ validLayout0225) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind04192_0) certificate0166

private theorem bind04193_0 : Agrees (spec (fastBase 0 58 17) layout0225) scope0144 := by decide

theorem reject04193 : Rejected (base 0 58 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 17) _ validLayout0225) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04193_0) certificate0147

private theorem bind04194_0 : Agrees (spec (fastBase 0 58 18) layout0225) scope0144 := by decide

theorem reject04194 : Rejected (base 0 58 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 18) _ validLayout0225) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04194_0) certificate0147

private theorem bind04195_0 : Agrees (spec (fastBase 0 58 19) layout0225) scope0144 := by decide

theorem reject04195 : Rejected (base 0 58 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 19) _ validLayout0225) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04195_0) certificate0147

private theorem bind04196_0 : Agrees (spec (fastBase 0 58 20) layout0225) scope0144 := by decide

theorem reject04196 : Rejected (base 0 58 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 20) _ validLayout0225) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04196_0) certificate0147

private theorem bind04197_0 : Agrees (spec (fastBase 0 58 21) layout0225) scope0144 := by decide

theorem reject04197 : Rejected (base 0 58 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 21) _ validLayout0225) (by decide) scope0144 (by rw [← fastBase_exact]; exact bind04197_0) certificate0147

private theorem bind04198_0 : Agrees (spec (fastBase 0 58 22) layout0225) scope0150 := by decide

theorem reject04198 : Rejected (base 0 58 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 22) _ validLayout0225) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04198_0) certificate0153

private theorem bind04199_0 : Agrees (spec (fastBase 0 58 23) layout0225) scope0167 := by decide

theorem reject04199 : Rejected (base 0 58 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 23) _ validLayout0225) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind04199_0) certificate0170

private theorem bind04200_0 : Agrees (spec (fastBase 0 58 24) layout0225) scope0155 := by decide

theorem reject04200 : Rejected (base 0 58 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 24) _ validLayout0225) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04200_0) certificate0158

private theorem bind04201_0 : Agrees (spec (fastBase 0 58 25) layout0225) scope0168 := by decide

theorem reject04201 : Rejected (base 0 58 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 25) _ validLayout0225) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind04201_0) certificate0171

private theorem bind04202_0 : Agrees (spec (fastBase 0 58 26) layout0226) scope0267 := by decide

theorem reject04202 : Rejected (base 0 58 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 26) _ validLayout0226) (by decide) scope0267 (by rw [← fastBase_exact]; exact bind04202_0) certificate0270

private theorem bind04203_0 : Agrees (spec (fastBase 0 58 27) layout0225) scope0155 := by decide

theorem reject04203 : Rejected (base 0 58 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 27) _ validLayout0225) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04203_0) certificate0158

private theorem bind04204_0 : Agrees (spec (fastBase 0 58 28) layout0227) scope0288 := by decide

theorem reject04204 : Rejected (base 0 58 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 28) _ validLayout0227) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind04204_0) certificate0291

private theorem bind04205_0 : Agrees (spec (fastBase 0 58 29) layout0226) scope0270 := by decide

theorem reject04205 : Rejected (base 0 58 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 29) _ validLayout0226) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind04205_0) certificate0273

private theorem bind04206_0 : Agrees (spec (fastBase 0 58 30) layout0225) scope0171 := by decide

theorem reject04206 : Rejected (base 0 58 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 30) _ validLayout0225) (by decide) scope0171 (by rw [← fastBase_exact]; exact bind04206_0) certificate0174

private theorem bind04207_0 : Agrees (spec (fastBase 0 58 31) layout0225) scope0160 := by decide

theorem reject04207 : Rejected (base 0 58 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 31) _ validLayout0225) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind04207_0) certificate0163

private theorem bind04208_0 : Agrees (spec (fastBase 0 58 32) layout0225) scope0140 := by decide

theorem reject04208 : Rejected (base 0 58 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 32) _ validLayout0225) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04208_0) certificate0143

private theorem bind04209_0 : Agrees (spec (fastBase 0 58 33) layout0225) scope0160 := by decide

theorem reject04209 : Rejected (base 0 58 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 33) _ validLayout0225) (by decide) scope0160 (by rw [← fastBase_exact]; exact bind04209_0) certificate0163

private theorem bind04210_0 : Agrees (spec (fastBase 0 58 34) layout0226) scope0270 := by decide

theorem reject04210 : Rejected (base 0 58 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 34) _ validLayout0226) (by decide) scope0270 (by rw [← fastBase_exact]; exact bind04210_0) certificate0273

private theorem bind04211_0 : Agrees (spec (fastBase 0 58 35) layout0225) scope0158 := by decide

theorem reject04211 : Rejected (base 0 58 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 35) _ validLayout0225) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind04211_0) certificate0161

private theorem bind04212_0 : Agrees (spec (fastBase 0 58 36) layout0226) scope0269 := by decide

theorem reject04212 : Rejected (base 0 58 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 36) _ validLayout0226) (by decide) scope0269 (by rw [← fastBase_exact]; exact bind04212_0) certificate0272

private theorem bind04213_0 : Agrees (spec (fastBase 0 58 37) layout0225) scope0167 := by decide

theorem reject04213 : Rejected (base 0 58 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 37) _ validLayout0225) (by decide) scope0167 (by rw [← fastBase_exact]; exact bind04213_0) certificate0170

private theorem bind04214_0 : Agrees (spec (fastBase 0 58 38) layout0225) scope0140 := by decide

theorem reject04214 : Rejected (base 0 58 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 38) _ validLayout0225) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04214_0) certificate0143

private theorem bind04215_0 : Agrees (spec (fastBase 0 58 39) layout0225) scope0155 := by decide

theorem reject04215 : Rejected (base 0 58 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 39) _ validLayout0225) (by decide) scope0155 (by rw [← fastBase_exact]; exact bind04215_0) certificate0158

private theorem bind04216_0 : Agrees (spec (fastBase 0 58 40) layout0225) scope0165 := by decide

theorem reject04216 : Rejected (base 0 58 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 40) _ validLayout0225) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind04216_0) certificate0168

private theorem bind04217_0 : Agrees (spec (fastBase 0 58 41) layout0226) scope0457 := by decide

private theorem bind04217_1 : Agrees (spec (fastBase 0 58 41) layout0227) scope0273 := by decide

theorem reject04217 : Rejected (base 0 58 41) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0226 layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 41) _ validLayout0226) (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 41) _ validLayout0227) (by decide) (by decide) scope0457 scope0273 (by rw [← fastBase_exact]; exact bind04217_0) (by rw [← fastBase_exact]; exact bind04217_1) 1 6 1 6 (by decide) (by decide) 2 3 (by decide) certificate0492 certificate0493 (by decide)

private theorem bind04218_0 : Agrees (spec (fastBase 0 58 42) layout0225) scope0141 := by decide

theorem reject04218 : Rejected (base 0 58 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 42) _ validLayout0225) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04218_0) certificate0144

private theorem bind04219_0 : Agrees (spec (fastBase 0 58 43) layout0225) scope0163 := by decide

theorem reject04219 : Rejected (base 0 58 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 43) _ validLayout0225) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind04219_0) certificate0166

private theorem bind04220_0 : Agrees (spec (fastBase 0 58 44) layout0226) scope0274 := by decide

theorem reject04220 : Rejected (base 0 58 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 44) _ validLayout0226) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind04220_0) certificate0277

private theorem bind04221_0 : Agrees (spec (fastBase 0 58 45) layout0227) scope0291 := by decide

theorem reject04221 : Rejected (base 0 58 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 45) _ validLayout0227) (by decide) scope0291 (by rw [← fastBase_exact]; exact bind04221_0) certificate0294

private theorem bind04222_0 : Agrees (spec (fastBase 0 58 46) layout0225) scope0162 := by decide

theorem reject04222 : Rejected (base 0 58 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 46) _ validLayout0225) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind04222_0) certificate0165

private theorem bind04223_0 : Agrees (spec (fastBase 0 58 47) layout0225) scope0150 := by decide

theorem reject04223 : Rejected (base 0 58 47) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 47) _ validLayout0225) (by decide) scope0150 (by rw [← fastBase_exact]; exact bind04223_0) certificate0153

private theorem bind04224_0 : Agrees (spec (fastBase 0 58 48) layout0225) scope0168 := by decide

theorem reject04224 : Rejected (base 0 58 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 48) _ validLayout0225) (by decide) scope0168 (by rw [← fastBase_exact]; exact bind04224_0) certificate0171

private theorem bind04225_0 : Agrees (spec (fastBase 0 58 49) layout0225) scope0141 := by decide

theorem reject04225 : Rejected (base 0 58 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 49) _ validLayout0225) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04225_0) certificate0144

private theorem bind04226_0 : Agrees (spec (fastBase 0 58 50) layout0225) scope0157 := by decide

theorem reject04226 : Rejected (base 0 58 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 50) _ validLayout0225) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind04226_0) certificate0160

private theorem bind04227_0 : Agrees (spec (fastBase 0 58 51) layout0228) scope0458 := by decide

private theorem bind04227_1 : Agrees (spec (fastBase 0 58 51) layout0229) scope0277 := by decide

theorem reject04227 : Rejected (base 0 58 51) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0228 layout0229 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 51) _ validLayout0228) (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 51) _ validLayout0229) (by decide) (by decide) scope0458 scope0277 (by rw [← fastBase_exact]; exact bind04227_0) (by rw [← fastBase_exact]; exact bind04227_1) 3 8 3 8 (by decide) (by decide) 2 3 (by decide) certificate0494 certificate0280 (by decide)

private theorem bind04228_0 : Agrees (spec (fastBase 0 58 52) layout0225) scope0157 := by decide

theorem reject04228 : Rejected (base 0 58 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 52) _ validLayout0225) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind04228_0) certificate0160

private theorem bind04229_0 : Agrees (spec (fastBase 0 58 53) layout0225) scope0156 := by decide

theorem reject04229 : Rejected (base 0 58 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 53) _ validLayout0225) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind04229_0) certificate0159

private theorem bind04230_0 : Agrees (spec (fastBase 0 58 54) layout0225) scope0141 := by decide

theorem reject04230 : Rejected (base 0 58 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 54) _ validLayout0225) (by decide) scope0141 (by rw [← fastBase_exact]; exact bind04230_0) certificate0144

private theorem bind04231_0 : Agrees (spec (fastBase 0 58 55) layout0225) scope0145 := by decide

theorem reject04231 : Rejected (base 0 58 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 55) _ validLayout0225) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04231_0) certificate0148

private theorem bind04232_0 : Agrees (spec (fastBase 0 58 56) layout0227) scope0459 := by decide

theorem reject04232 : Rejected (base 0 58 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 56) _ validLayout0227) (by decide) scope0459 (by rw [← fastBase_exact]; exact bind04232_0) certificate0495

private theorem bind04233_0 : Agrees (spec (fastBase 0 58 57) layout0225) scope0145 := by decide

theorem reject04233 : Rejected (base 0 58 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 57) _ validLayout0225) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04233_0) certificate0148

private theorem bind04234_0 : Agrees (spec (fastBase 0 58 58) layout0225) scope0158 := by decide

theorem reject04234 : Rejected (base 0 58 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 58) _ validLayout0225) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind04234_0) certificate0161

private theorem bind04235_0 : Agrees (spec (fastBase 0 58 59) layout0227) scope0459 := by decide

theorem reject04235 : Rejected (base 0 58 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 59) _ validLayout0227) (by decide) scope0459 (by rw [← fastBase_exact]; exact bind04235_0) certificate0495

private theorem bind04236_0 : Agrees (spec (fastBase 0 58 60) layout0225) scope0162 := by decide

theorem reject04236 : Rejected (base 0 58 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 60) _ validLayout0225) (by decide) scope0162 (by rw [← fastBase_exact]; exact bind04236_0) certificate0165

private theorem bind04237_0 : Agrees (spec (fastBase 0 58 61) layout0226) scope0278 := by decide

theorem reject04237 : Rejected (base 0 58 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 61) _ validLayout0226) (by decide) scope0278 (by rw [← fastBase_exact]; exact bind04237_0) certificate0281

private theorem bind04238_0 : Agrees (spec (fastBase 0 58 62) layout0227) scope0288 := by decide

theorem reject04238 : Rejected (base 0 58 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 62) _ validLayout0227) (by decide) scope0288 (by rw [← fastBase_exact]; exact bind04238_0) certificate0291

private theorem bind04239_0 : Agrees (spec (fastBase 0 58 63) layout0226) scope0280 := by decide

theorem reject04239 : Rejected (base 0 58 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 63) _ validLayout0226) (by decide) scope0280 (by rw [← fastBase_exact]; exact bind04239_0) certificate0283

private theorem bind04240_0 : Agrees (spec (fastBase 0 58 64) layout0226) scope0272 := by decide

private theorem bind04240_1 : Agrees (spec (fastBase 0 58 64) layout0227) scope0273 := by decide

theorem reject04240 : Rejected (base 0 58 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0226 layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 64) _ validLayout0226) (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 64) _ validLayout0227) (by decide) (by decide) scope0272 scope0273 (by rw [← fastBase_exact]; exact bind04240_0) (by rw [← fastBase_exact]; exact bind04240_1) 0 5 0 5 (by decide) (by decide) 3 2 (by decide) certificate0275 certificate0276 (by decide)

private theorem bind04241_0 : Agrees (spec (fastBase 0 58 65) layout0226) scope0274 := by decide

theorem reject04241 : Rejected (base 0 58 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 65) _ validLayout0226) (by decide) scope0274 (by rw [← fastBase_exact]; exact bind04241_0) certificate0277

private theorem bind04242_0 : Agrees (spec (fastBase 0 58 66) layout0226) scope0287 := by decide

theorem reject04242 : Rejected (base 0 58 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0226 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 66) _ validLayout0226) (by decide) scope0287 (by rw [← fastBase_exact]; exact bind04242_0) certificate0290

private theorem bind04243_0 : Agrees (spec (fastBase 0 58 67) layout0225) scope0165 := by decide

theorem reject04243 : Rejected (base 0 58 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 67) _ validLayout0225) (by decide) scope0165 (by rw [← fastBase_exact]; exact bind04243_0) certificate0168

private theorem bind04244_0 : Agrees (spec (fastBase 0 58 68) layout0225) scope0140 := by decide

theorem reject04244 : Rejected (base 0 58 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 68) _ validLayout0225) (by decide) scope0140 (by rw [← fastBase_exact]; exact bind04244_0) certificate0143

private theorem bind04245_0 : Agrees (spec (fastBase 0 58 69) layout0225) scope0156 := by decide

theorem reject04245 : Rejected (base 0 58 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 69) _ validLayout0225) (by decide) scope0156 (by rw [← fastBase_exact]; exact bind04245_0) certificate0159

private theorem bind04246_0 : Agrees (spec (fastBase 0 58 70) layout0225) scope0145 := by decide

theorem reject04246 : Rejected (base 0 58 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0225 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 70) _ validLayout0225) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind04246_0) certificate0148

private theorem bind04247_0 : Agrees (spec (fastBase 0 58 71) layout0227) scope0460 := by decide

theorem reject04247 : Rejected (base 0 58 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0227 (layoutValid_of_refines _ _ (base_refines_skeleton 0 58 71) _ validLayout0227) (by decide) scope0460 (by rw [← fastBase_exact]; exact bind04247_0) certificate0496

theorem allCases058 : ∀ y : Fin 72, Rejected (base 0 58 y) := by
  intro y
  fin_cases y

  · exact reject04176

  · exact reject04177

  · exact reject04178

  · exact reject04179

  · exact reject04180

  · exact reject04181

  · exact reject04182

  · exact reject04183

  · exact reject04184

  · exact reject04185

  · exact reject04186

  · exact reject04187

  · exact reject04188

  · exact reject04189

  · exact reject04190

  · exact reject04191

  · exact reject04192

  · exact reject04193

  · exact reject04194

  · exact reject04195

  · exact reject04196

  · exact reject04197

  · exact reject04198

  · exact reject04199

  · exact reject04200

  · exact reject04201

  · exact reject04202

  · exact reject04203

  · exact reject04204

  · exact reject04205

  · exact reject04206

  · exact reject04207

  · exact reject04208

  · exact reject04209

  · exact reject04210

  · exact reject04211

  · exact reject04212

  · exact reject04213

  · exact reject04214

  · exact reject04215

  · exact reject04216

  · exact reject04217

  · exact reject04218

  · exact reject04219

  · exact reject04220

  · exact reject04221

  · exact reject04222

  · exact reject04223

  · exact reject04224

  · exact reject04225

  · exact reject04226

  · exact reject04227

  · exact reject04228

  · exact reject04229

  · exact reject04230

  · exact reject04231

  · exact reject04232

  · exact reject04233

  · exact reject04234

  · exact reject04235

  · exact reject04236

  · exact reject04237

  · exact reject04238

  · exact reject04239

  · exact reject04240

  · exact reject04241

  · exact reject04242

  · exact reject04243

  · exact reject04244

  · exact reject04245

  · exact reject04246

  · exact reject04247

end PricingIntegration.RemainingGWitnesses
