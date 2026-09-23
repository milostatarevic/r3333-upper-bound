import PricingC.GCoreExcluded
import PricingC.GBindings002
import PricingC.GScopeChecks016
import PricingC.GScopeChecks017
import PricingC.GScopeChecks018
import PricingC.GScopeChecks019
import PricingC.GScopeChecks020
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks006

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed0200 : CoreExcluded (baseCore 0 8 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 8) owner_valid033
  scope267 binding0200_0 certificate267

theorem case_closed0201 : CoreExcluded (baseCore 0 8 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 8) owner_valid002
  scope268 binding0201_0 certificate268

theorem case_closed0202 : CoreExcluded (baseCore 0 8 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 8) owner_valid034
  scope269 binding0202_0 certificate269

theorem case_closed0203 : CoreExcluded (baseCore 0 8 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 8) owner_valid035
  scope270 binding0203_0 certificate270

theorem case_closed0204 : CoreExcluded (baseCore 0 8 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 8) owner_valid036
  scope271 binding0204_0 certificate271

theorem case_closed0205 : CoreExcluded (baseCore 0 8 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout145 layout146
  (layout_for_all_rows 5 layout145 layout_valid145 0 8)
  (layout_for_all_rows 5 layout146 layout_valid146 0 8)
  owner_valid145 owner_valid146 scope272 scope273
  binding0205_0 binding0205_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate272 certificate273 (by decide)

theorem case_closed0206 : CoreExcluded (baseCore 0 8 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout147 layout110
  (layout_for_all_rows 6 layout147 layout_valid147 0 8)
  (layout_for_all_rows 6 layout110 layout_valid110 0 8)
  owner_valid147 owner_valid110 scope272 scope273
  binding0206_0 binding0206_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate272 certificate273 (by decide)

theorem case_closed0207 : CoreExcluded (baseCore 0 8 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout133 layout148
  (layout_for_all_rows 7 layout133 layout_valid133 0 8)
  (layout_for_all_rows 7 layout148 layout_valid148 0 8)
  owner_valid133 owner_valid148 scope274 scope275
  binding0207_0 binding0207_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate274 certificate275 (by decide)

theorem case_closed0208 : CoreExcluded (baseCore 0 8 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout114 layout115
  (layout_for_all_rows 8 layout114 layout_valid114 0 8)
  (layout_for_all_rows 8 layout115 layout_valid115 0 8)
  owner_valid114 owner_valid115 scope274 scope275
  binding0208_0 binding0208_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate274 certificate275 (by decide)

theorem case_closed0209 : CoreExcluded (baseCore 0 8 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 0 8)
  (layout_for_all_rows 9 layout061 layout_valid061 0 8)
  owner_valid116 owner_valid061 scope276 scope277
  binding0209_0 binding0209_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate276 certificate277 (by decide)

theorem case_closed0210 : CoreExcluded (baseCore 0 8 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout039 layout063
  (layout_for_all_rows 10 layout039 layout_valid039 0 8)
  (layout_for_all_rows 10 layout063 layout_valid063 0 8)
  owner_valid039 owner_valid063 scope278 scope279
  binding0210_0 binding0210_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate278 certificate279 (by decide)

theorem case_closed0211 : CoreExcluded (baseCore 0 8 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout149 layout040
  (layout_for_all_rows 11 layout149 layout_valid149 0 8)
  (layout_for_all_rows 11 layout040 layout_valid040 0 8)
  owner_valid149 owner_valid040 scope280 scope281
  binding0211_0 binding0211_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate280 certificate281 (by decide)

theorem case_closed0212 : CoreExcluded (baseCore 0 8 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout042 layout119
  (layout_for_all_rows 12 layout042 layout_valid042 0 8)
  (layout_for_all_rows 12 layout119 layout_valid119 0 8)
  owner_valid042 owner_valid119 scope282 scope283
  binding0212_0 binding0212_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate282 certificate283 (by decide)

theorem case_closed0213 : CoreExcluded (baseCore 0 8 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 8) owner_valid019
  scope284 binding0213_0 certificate284

theorem case_closed0214 : CoreExcluded (baseCore 0 8 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout139
  (layout_for_all_rows 14 layout139 layout_valid139 0 8) owner_valid139
  scope285 binding0214_0 certificate285

theorem case_closed0215 : CoreExcluded (baseCore 0 8 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout150
  (layout_for_all_rows 15 layout150 layout_valid150 0 8) owner_valid150
  scope286 binding0215_0 certificate286

theorem case_closed0216 : CoreExcluded (baseCore 0 8 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 8) owner_valid022
  scope287 binding0216_0 certificate287

theorem case_closed0217 : CoreExcluded (baseCore 0 8 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 8) owner_valid023
  scope288 binding0217_0 certificate288

theorem case_closed0218 : CoreExcluded (baseCore 0 8 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 8) owner_valid024
  scope289 binding0218_0 certificate289

theorem case_closed0219 : CoreExcluded (baseCore 0 8 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 8) owner_valid025
  scope290 binding0219_0 certificate290

theorem case_closed0220 : CoreExcluded (baseCore 0 8 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 8) owner_valid026
  scope291 binding0220_0 certificate291

theorem case_closed0221 : CoreExcluded (baseCore 0 8 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 8) owner_valid087
  scope292 binding0221_0 certificate292

theorem case_closed0222 : CoreExcluded (baseCore 0 8 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout144
  (layout_for_all_rows 22 layout144 layout_valid144 0 8) owner_valid144
  scope293 binding0222_0 certificate293

theorem case_closed0223 : CoreExcluded (baseCore 0 8 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout151
  (layout_for_all_rows 23 layout151 layout_valid151 0 8) owner_valid151
  scope294 binding0223_0 certificate294

theorem case_closed0224 : CoreExcluded (baseCore 0 8 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 8) owner_valid032
  scope295 binding0224_0 certificate295

theorem case_closed0225 : CoreExcluded (baseCore 0 9 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout000 layout088
  (layout_for_all_rows 0 layout000 layout_valid000 0 9)
  (layout_for_all_rows 0 layout088 layout_valid088 0 9)
  owner_valid000 owner_valid088 scope296 scope297
  binding0225_0 binding0225_1
  0 8 0 8 (by decide) (by decide) 3 2 (by decide)
  certificate296 certificate297 (by decide)

theorem case_closed0226 : CoreExcluded (baseCore 0 9 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout152 layout076
  (layout_for_all_rows 1 layout152 layout_valid152 0 9)
  (layout_for_all_rows 1 layout076 layout_valid076 0 9)
  owner_valid152 owner_valid076 scope298 scope299
  binding0226_0 binding0226_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate298 certificate299 (by decide)

theorem case_closed0227 : CoreExcluded (baseCore 0 9 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout153 layout154
  (layout_for_all_rows 2 layout153 layout_valid153 0 9)
  (layout_for_all_rows 2 layout154 layout_valid154 0 9)
  owner_valid153 owner_valid154 scope300 scope301
  binding0227_0 binding0227_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate300 certificate301 (by decide)

theorem case_closed0228 : CoreExcluded (baseCore 0 9 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 9) owner_valid035
  scope302 binding0228_0 certificate302

theorem case_closed0229 : CoreExcluded (baseCore 0 9 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout008 layout155
  (layout_for_all_rows 4 layout008 layout_valid008 0 9)
  (layout_for_all_rows 4 layout155 layout_valid155 0 9)
  owner_valid008 owner_valid155 scope303 scope304
  binding0229_0 binding0229_1
  0 8 0 8 (by decide) (by decide) 2 3 (by decide)
  certificate303 certificate304 (by decide)

theorem case_closed0230 : CoreExcluded (baseCore 0 9 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 9) owner_valid009
  scope305 binding0230_0 certificate305

theorem case_closed0231 : CoreExcluded (baseCore 0 9 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 9) owner_valid010
  scope306 binding0231_0 certificate306

theorem case_closed0232 : CoreExcluded (baseCore 0 9 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 9) owner_valid011
  scope307 binding0232_0 certificate307

theorem case_closed0233 : CoreExcluded (baseCore 0 9 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 9) owner_valid012
  scope308 binding0233_0 certificate308

theorem case_closed0234 : CoreExcluded (baseCore 0 9 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 9) owner_valid038
  scope309 binding0234_0 certificate309

theorem case_closed0235 : CoreExcluded (baseCore 0 9 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 9) owner_valid079
  scope310 binding0235_0 certificate310

theorem case_closed0236 : CoreExcluded (baseCore 0 9 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout156 layout157
  (layout_for_all_rows 11 layout156 layout_valid156 0 9)
  (layout_for_all_rows 11 layout157 layout_valid157 0 9)
  owner_valid156 owner_valid157 scope311 scope312
  binding0236_0 binding0236_1
  2 6 6 2 (by decide) (by decide) 3 2 (by decide)
  certificate311 certificate312 (by decide)

theorem case_closed0237 : CoreExcluded (baseCore 0 9 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout158 layout159
  (layout_for_all_rows 12 layout158 layout_valid158 0 9)
  (layout_for_all_rows 12 layout159 layout_valid159 0 9)
  owner_valid158 owner_valid159 scope313 scope314
  binding0237_0 binding0237_1
  1 8 7 3 (by decide) (by decide) 3 2 (by decide)
  certificate313 certificate314 (by decide)

theorem case_closed0238 : CoreExcluded (baseCore 0 9 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout160 layout161
  (layout_for_all_rows 13 layout160 layout_valid160 0 9)
  (layout_for_all_rows 13 layout161 layout_valid161 0 9)
  owner_valid160 owner_valid161 scope315 scope316
  binding0238_0 binding0238_1
  1 5 7 0 (by decide) (by decide) 3 2 (by decide)
  certificate315 certificate316 (by decide)

theorem case_closed0239 : CoreExcluded (baseCore 0 9 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout162 layout163
  (layout_for_all_rows 14 layout162 layout_valid162 0 9)
  (layout_for_all_rows 14 layout163 layout_valid163 0 9)
  owner_valid162 owner_valid163 scope317 scope318
  binding0239_0 binding0239_1
  0 6 6 2 (by decide) (by decide) 3 2 (by decide)
  certificate317 certificate318 (by decide)

theorem case_closed0240 : CoreExcluded (baseCore 0 9 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 9) owner_valid021
  scope319 binding0240_0 certificate319

theorem case_closed0241 : CoreExcluded (baseCore 0 9 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 9) owner_valid022
  scope320 binding0241_0 certificate320

theorem case_closed0242 : CoreExcluded (baseCore 0 9 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 9) owner_valid023
  scope321 binding0242_0 certificate321

theorem case_closed0243 : CoreExcluded (baseCore 0 9 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 9) owner_valid024
  scope322 binding0243_0 certificate322

theorem case_closed0244 : CoreExcluded (baseCore 0 9 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 9) owner_valid025
  scope323 binding0244_0 certificate323

theorem case_closed0245 : CoreExcluded (baseCore 0 9 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 9) owner_valid026
  scope324 binding0245_0 certificate324

theorem case_closed0246 : CoreExcluded (baseCore 0 9 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 9) owner_valid087
  scope325 binding0246_0 certificate325

theorem case_closed0247 : CoreExcluded (baseCore 0 9 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 9) owner_valid072
  scope326 binding0247_0 certificate326

theorem case_closed0248 : CoreExcluded (baseCore 0 9 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 9) owner_valid031
  scope327 binding0248_0 certificate327

theorem case_closed0249 : CoreExcluded (baseCore 0 9 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 9) owner_valid032
  scope328 binding0249_0 certificate328

theorem case_closed0250 : CoreExcluded (baseCore 0 10 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout164 layout001
  (layout_for_all_rows 0 layout164 layout_valid164 0 10)
  (layout_for_all_rows 0 layout001 layout_valid001 0 10)
  owner_valid164 owner_valid001 scope329 scope330
  binding0250_0 binding0250_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate329 certificate330 (by decide)

theorem case_closed0251 : CoreExcluded (baseCore 0 10 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout165 layout089
  (layout_for_all_rows 1 layout165 layout_valid165 0 10)
  (layout_for_all_rows 1 layout089 layout_valid089 0 10)
  owner_valid165 owner_valid089 scope331 scope332
  binding0251_0 binding0251_1
  2 8 1 7 (by decide) (by decide) 3 2 (by decide)
  certificate331 certificate332 (by decide)

theorem case_closed0252 : CoreExcluded (baseCore 0 10 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout153 layout154
  (layout_for_all_rows 2 layout153 layout_valid153 0 10)
  (layout_for_all_rows 2 layout154 layout_valid154 0 10)
  owner_valid153 owner_valid154 scope333 scope334
  binding0252_0 binding0252_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate333 certificate334 (by decide)

theorem case_closed0253 : CoreExcluded (baseCore 0 10 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout166 layout167
  (layout_for_all_rows 3 layout166 layout_valid166 0 10)
  (layout_for_all_rows 3 layout167 layout_valid167 0 10)
  owner_valid166 owner_valid167 scope335 scope336
  binding0253_0 binding0253_1
  2 8 1 7 (by decide) (by decide) 2 3 (by decide)
  certificate335 certificate336 (by decide)

theorem case_closed0254 : CoreExcluded (baseCore 0 10 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 10) owner_valid036
  scope337 binding0254_0 certificate337

theorem case_closed0255 : CoreExcluded (baseCore 0 10 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 10) owner_valid009
  scope338 binding0255_0 certificate338

theorem case_closed0256 : CoreExcluded (baseCore 0 10 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 10) owner_valid010
  scope339 binding0256_0 certificate339

theorem case_closed0257 : CoreExcluded (baseCore 0 10 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout168 layout169
  (layout_for_all_rows 7 layout168 layout_valid168 0 10)
  (layout_for_all_rows 7 layout169 layout_valid169 0 10)
  owner_valid168 owner_valid169 scope340 scope341
  binding0257_0 binding0257_1
  1 5 6 1 (by decide) (by decide) 3 2 (by decide)
  certificate340 certificate341 (by decide)

theorem case_closed0258 : CoreExcluded (baseCore 0 10 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout170 layout171
  (layout_for_all_rows 8 layout170 layout_valid170 0 10)
  (layout_for_all_rows 8 layout171 layout_valid171 0 10)
  owner_valid170 owner_valid171 scope340 scope342
  binding0258_0 binding0258_1
  0 6 6 2 (by decide) (by decide) 3 2 (by decide)
  certificate342 certificate343 (by decide)

theorem case_closed0259 : CoreExcluded (baseCore 0 10 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 10) owner_valid038
  scope343 binding0259_0 certificate344

theorem case_closed0260 : CoreExcluded (baseCore 0 10 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 10) owner_valid079
  scope344 binding0260_0 certificate345

theorem case_closed0261 : CoreExcluded (baseCore 0 10 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 10) owner_valid017
  scope345 binding0261_0 certificate346

theorem case_closed0262 : CoreExcluded (baseCore 0 10 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 10) owner_valid018
  scope346 binding0262_0 certificate347

theorem case_closed0263 : CoreExcluded (baseCore 0 10 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 10) owner_valid019
  scope347 binding0263_0 certificate348

theorem case_closed0264 : CoreExcluded (baseCore 0 10 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 10) owner_valid020
  scope348 binding0264_0 certificate349

theorem case_closed0265 : CoreExcluded (baseCore 0 10 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout172 layout173
  (layout_for_all_rows 15 layout172 layout_valid172 0 10)
  (layout_for_all_rows 15 layout173 layout_valid173 0 10)
  owner_valid172 owner_valid173 scope349 scope350
  binding0265_0 binding0265_1
  2 6 6 2 (by decide) (by decide) 3 2 (by decide)
  certificate350 certificate351 (by decide)

theorem case_closed0266 : CoreExcluded (baseCore 0 10 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout174 layout175
  (layout_for_all_rows 16 layout174 layout_valid174 0 10)
  (layout_for_all_rows 16 layout175 layout_valid175 0 10)
  owner_valid174 owner_valid175 scope351 scope352
  binding0266_0 binding0266_1
  2 8 7 3 (by decide) (by decide) 2 3 (by decide)
  certificate352 certificate353 (by decide)

theorem case_closed0267 : CoreExcluded (baseCore 0 10 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 10) owner_valid023
  scope353 binding0267_0 certificate354

theorem case_closed0268 : CoreExcluded (baseCore 0 10 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 10) owner_valid024
  scope354 binding0268_0 certificate355

theorem case_closed0269 : CoreExcluded (baseCore 0 10 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 10) owner_valid025
  scope355 binding0269_0 certificate356

theorem case_closed0270 : CoreExcluded (baseCore 0 10 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 10) owner_valid026
  scope356 binding0270_0 certificate357

theorem case_closed0271 : CoreExcluded (baseCore 0 10 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 10) owner_valid087
  scope357 binding0271_0 certificate358

theorem case_closed0272 : CoreExcluded (baseCore 0 10 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 10) owner_valid072
  scope358 binding0272_0 certificate359

theorem case_closed0273 : CoreExcluded (baseCore 0 10 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 10) owner_valid031
  scope359 binding0273_0 certificate360

theorem case_closed0274 : CoreExcluded (baseCore 0 10 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 10) owner_valid032
  scope360 binding0274_0 certificate361

theorem case_closed0275 : CoreExcluded (baseCore 0 11 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 11) owner_valid033
  scope361 binding0275_0 certificate362

theorem case_closed0276 : CoreExcluded (baseCore 0 11 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 11) owner_valid002
  scope362 binding0276_0 certificate363

theorem case_closed0277 : CoreExcluded (baseCore 0 11 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 11) owner_valid034
  scope363 binding0277_0 certificate364

theorem case_closed0278 : CoreExcluded (baseCore 0 11 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 11) owner_valid035
  scope364 binding0278_0 certificate365

theorem case_closed0279 : CoreExcluded (baseCore 0 11 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 11) owner_valid036
  scope365 binding0279_0 certificate366

theorem case_closed0280 : CoreExcluded (baseCore 0 11 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout176 layout108
  (layout_for_all_rows 5 layout176 layout_valid176 0 11)
  (layout_for_all_rows 5 layout108 layout_valid108 0 11)
  owner_valid176 owner_valid108 scope366 scope367
  binding0280_0 binding0280_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate367 certificate368 (by decide)

theorem case_closed0281 : CoreExcluded (baseCore 0 11 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout177 layout178
  (layout_for_all_rows 6 layout177 layout_valid177 0 11)
  (layout_for_all_rows 6 layout178 layout_valid178 0 11)
  owner_valid177 owner_valid178 scope366 scope367
  binding0281_0 binding0281_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate367 certificate368 (by decide)

theorem case_closed0282 : CoreExcluded (baseCore 0 11 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 11) owner_valid011
  scope368 binding0282_0 certificate369

theorem case_closed0283 : CoreExcluded (baseCore 0 11 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 0 11) owner_valid134
  scope368 binding0283_0 certificate369

theorem case_closed0284 : CoreExcluded (baseCore 0 11 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 11) owner_valid038
  scope369 binding0284_0 certificate370

theorem case_closed0285 : CoreExcluded (baseCore 0 11 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 11) owner_valid079
  scope370 binding0285_0 certificate371

theorem case_closed0286 : CoreExcluded (baseCore 0 11 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 11) owner_valid149
  scope371 binding0286_0 certificate372

theorem case_closed0287 : CoreExcluded (baseCore 0 11 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 11) owner_valid018
  scope371 binding0287_0 certificate372

theorem case_closed0288 : CoreExcluded (baseCore 0 11 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout137 layout179
  (layout_for_all_rows 13 layout137 layout_valid137 0 11)
  (layout_for_all_rows 13 layout179 layout_valid179 0 11)
  owner_valid137 owner_valid179 scope372 scope373
  binding0288_0 binding0288_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate373 certificate374 (by decide)

theorem case_closed0289 : CoreExcluded (baseCore 0 11 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout123 layout124
  (layout_for_all_rows 14 layout123 layout_valid123 0 11)
  (layout_for_all_rows 14 layout124 layout_valid124 0 11)
  owner_valid123 owner_valid124 scope374 scope375
  binding0289_0 binding0289_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate375 certificate376 (by decide)

theorem case_closed0290 : CoreExcluded (baseCore 0 11 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout150
  (layout_for_all_rows 15 layout064 layout_valid064 0 11)
  (layout_for_all_rows 15 layout150 layout_valid150 0 11)
  owner_valid064 owner_valid150 scope376 scope377
  binding0290_0 binding0290_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate377 certificate378 (by decide)

theorem case_closed0291 : CoreExcluded (baseCore 0 11 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout180 layout066
  (layout_for_all_rows 16 layout180 layout_valid180 0 11)
  (layout_for_all_rows 16 layout066 layout_valid066 0 11)
  owner_valid180 owner_valid066 scope378 scope379
  binding0291_0 binding0291_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate379 certificate380 (by decide)

theorem case_closed0292 : CoreExcluded (baseCore 0 11 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 0 11)
  (layout_for_all_rows 17 layout046 layout_valid046 0 11)
  owner_valid129 owner_valid046 scope380 scope381
  binding0292_0 binding0292_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate381 certificate382 (by decide)

theorem case_closed0293 : CoreExcluded (baseCore 0 11 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout068 layout048
  (layout_for_all_rows 18 layout068 layout_valid068 0 11)
  (layout_for_all_rows 18 layout048 layout_valid048 0 11)
  owner_valid068 owner_valid048 scope382 scope383
  binding0293_0 binding0293_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate383 certificate384 (by decide)

theorem case_closed0294 : CoreExcluded (baseCore 0 11 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 11) owner_valid025
  scope384 binding0294_0 certificate385

theorem case_closed0295 : CoreExcluded (baseCore 0 11 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout142
  (layout_for_all_rows 20 layout142 layout_valid142 0 11) owner_valid142
  scope385 binding0295_0 certificate386

theorem case_closed0296 : CoreExcluded (baseCore 0 11 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 11) owner_valid087
  scope386 binding0296_0 certificate387

theorem case_closed0297 : CoreExcluded (baseCore 0 11 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 11) owner_valid072
  scope387 binding0297_0 certificate388

theorem case_closed0298 : CoreExcluded (baseCore 0 11 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 11) owner_valid031
  scope388 binding0298_0 certificate389

theorem case_closed0299 : CoreExcluded (baseCore 0 11 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout181
  (layout_for_all_rows 24 layout181 layout_valid181 0 11) owner_valid181
  scope389 binding0299_0 certificate390

theorem block_closed002 (i : Fin 100) : CoreExcluded (caseCore (blockCase 2 i)) := by
 fin_cases i
 · exact case_closed0200
 · exact case_closed0201
 · exact case_closed0202
 · exact case_closed0203
 · exact case_closed0204
 · exact case_closed0205
 · exact case_closed0206
 · exact case_closed0207
 · exact case_closed0208
 · exact case_closed0209
 · exact case_closed0210
 · exact case_closed0211
 · exact case_closed0212
 · exact case_closed0213
 · exact case_closed0214
 · exact case_closed0215
 · exact case_closed0216
 · exact case_closed0217
 · exact case_closed0218
 · exact case_closed0219
 · exact case_closed0220
 · exact case_closed0221
 · exact case_closed0222
 · exact case_closed0223
 · exact case_closed0224
 · exact case_closed0225
 · exact case_closed0226
 · exact case_closed0227
 · exact case_closed0228
 · exact case_closed0229
 · exact case_closed0230
 · exact case_closed0231
 · exact case_closed0232
 · exact case_closed0233
 · exact case_closed0234
 · exact case_closed0235
 · exact case_closed0236
 · exact case_closed0237
 · exact case_closed0238
 · exact case_closed0239
 · exact case_closed0240
 · exact case_closed0241
 · exact case_closed0242
 · exact case_closed0243
 · exact case_closed0244
 · exact case_closed0245
 · exact case_closed0246
 · exact case_closed0247
 · exact case_closed0248
 · exact case_closed0249
 · exact case_closed0250
 · exact case_closed0251
 · exact case_closed0252
 · exact case_closed0253
 · exact case_closed0254
 · exact case_closed0255
 · exact case_closed0256
 · exact case_closed0257
 · exact case_closed0258
 · exact case_closed0259
 · exact case_closed0260
 · exact case_closed0261
 · exact case_closed0262
 · exact case_closed0263
 · exact case_closed0264
 · exact case_closed0265
 · exact case_closed0266
 · exact case_closed0267
 · exact case_closed0268
 · exact case_closed0269
 · exact case_closed0270
 · exact case_closed0271
 · exact case_closed0272
 · exact case_closed0273
 · exact case_closed0274
 · exact case_closed0275
 · exact case_closed0276
 · exact case_closed0277
 · exact case_closed0278
 · exact case_closed0279
 · exact case_closed0280
 · exact case_closed0281
 · exact case_closed0282
 · exact case_closed0283
 · exact case_closed0284
 · exact case_closed0285
 · exact case_closed0286
 · exact case_closed0287
 · exact case_closed0288
 · exact case_closed0289
 · exact case_closed0290
 · exact case_closed0291
 · exact case_closed0292
 · exact case_closed0293
 · exact case_closed0294
 · exact case_closed0295
 · exact case_closed0296
 · exact case_closed0297
 · exact case_closed0298
 · exact case_closed0299
end PricingC.GIsomorphic