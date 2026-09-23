import PricingC.GCoreExcluded
import PricingC.GBindings004
import PricingC.GScopeChecks000
import PricingC.GScopeChecks001
import PricingC.GScopeChecks002
import PricingC.GScopeChecks003
import PricingC.GScopeChecks005
import PricingC.GScopeChecks006
import PricingC.GScopeChecks007
import PricingC.GScopeChecks008
import PricingC.GScopeChecks009
import PricingC.GScopeChecks016
import PricingC.GScopeChecks017
import PricingC.GScopeChecks018
import PricingC.GScopeChecks026
import PricingC.GScopeChecks027
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks007

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed0400 : CoreExcluded (baseCore 0 16 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 16) owner_valid033
  scope267 binding0400_0 certificate267

theorem case_closed0401 : CoreExcluded (baseCore 0 16 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 16) owner_valid002
  scope268 binding0401_0 certificate268

theorem case_closed0402 : CoreExcluded (baseCore 0 16 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 16) owner_valid034
  scope269 binding0402_0 certificate269

theorem case_closed0403 : CoreExcluded (baseCore 0 16 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 16) owner_valid035
  scope270 binding0403_0 certificate270

theorem case_closed0404 : CoreExcluded (baseCore 0 16 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 16) owner_valid036
  scope271 binding0404_0 certificate271

theorem case_closed0405 : CoreExcluded (baseCore 0 16 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 16) owner_valid037
  scope010 binding0405_0 certificate010

theorem case_closed0406 : CoreExcluded (baseCore 0 16 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 16) owner_valid058
  scope009 binding0406_0 certificate009

theorem case_closed0407 : CoreExcluded (baseCore 0 16 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 0 16) owner_valid059
  scope012 binding0407_0 certificate012

theorem case_closed0408 : CoreExcluded (baseCore 0 16 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 0 16) owner_valid134
  scope011 binding0408_0 certificate011

theorem case_closed0409 : CoreExcluded (baseCore 0 16 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 0 16)
  (layout_for_all_rows 9 layout061 layout_valid061 0 16)
  owner_valid116 owner_valid061 scope410 scope277
  binding0409_0 binding0409_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate418 certificate277 (by decide)

theorem case_closed0410 : CoreExcluded (baseCore 0 16 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout039 layout063
  (layout_for_all_rows 10 layout039 layout_valid039 0 16)
  (layout_for_all_rows 10 layout063 layout_valid063 0 16)
  owner_valid039 owner_valid063 scope411 scope279
  binding0410_0 binding0410_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate419 certificate279 (by decide)

theorem case_closed0411 : CoreExcluded (baseCore 0 16 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 16) owner_valid149
  scope018 binding0411_0 certificate018

theorem case_closed0412 : CoreExcluded (baseCore 0 16 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 16) owner_valid042
  scope017 binding0412_0 certificate017

theorem case_closed0413 : CoreExcluded (baseCore 0 16 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 16) owner_valid019
  scope284 binding0413_0 certificate284

theorem case_closed0414 : CoreExcluded (baseCore 0 16 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 0 16) owner_valid138
  scope020 binding0414_0 certificate020

theorem case_closed0415 : CoreExcluded (baseCore 0 16 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 0 16) owner_valid064
  scope021 binding0415_0 certificate021

theorem case_closed0416 : CoreExcluded (baseCore 0 16 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 16) owner_valid022
  scope287 binding0416_0 certificate287

theorem case_closed0417 : CoreExcluded (baseCore 0 16 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 16) owner_valid023
  scope288 binding0417_0 certificate288

theorem case_closed0418 : CoreExcluded (baseCore 0 16 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 16) owner_valid024
  scope289 binding0418_0 certificate289

theorem case_closed0419 : CoreExcluded (baseCore 0 16 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 16) owner_valid025
  scope290 binding0419_0 certificate290

theorem case_closed0420 : CoreExcluded (baseCore 0 16 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 16) owner_valid026
  scope291 binding0420_0 certificate291

theorem case_closed0421 : CoreExcluded (baseCore 0 16 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 16) owner_valid087
  scope292 binding0421_0 certificate292

theorem case_closed0422 : CoreExcluded (baseCore 0 16 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout144
  (layout_for_all_rows 22 layout144 layout_valid144 0 16) owner_valid144
  scope293 binding0422_0 certificate293

theorem case_closed0423 : CoreExcluded (baseCore 0 16 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 16) owner_valid054
  scope031 binding0423_0 certificate031

theorem case_closed0424 : CoreExcluded (baseCore 0 16 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 16) owner_valid032
  scope295 binding0424_0 certificate295

theorem case_closed0425 : CoreExcluded (baseCore 0 17 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout000
  (layout_for_all_rows 0 layout000 layout_valid000 0 17) owner_valid000
  scope412 binding0425_0 certificate420

theorem case_closed0426 : CoreExcluded (baseCore 0 17 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 17) owner_valid002
  scope002 binding0426_0 certificate002

theorem case_closed0427 : CoreExcluded (baseCore 0 17 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout004
  (layout_for_all_rows 2 layout004 layout_valid004 0 17) owner_valid004
  scope413 binding0427_0 certificate421

theorem case_closed0428 : CoreExcluded (baseCore 0 17 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout005
  (layout_for_all_rows 3 layout005 layout_valid005 0 17) owner_valid005
  scope414 binding0428_0 certificate422

theorem case_closed0429 : CoreExcluded (baseCore 0 17 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout008
  (layout_for_all_rows 4 layout008 layout_valid008 0 17) owner_valid008
  scope415 binding0429_0 certificate423

theorem case_closed0430 : CoreExcluded (baseCore 0 17 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 17) owner_valid009
  scope009 binding0430_0 certificate009

theorem case_closed0431 : CoreExcluded (baseCore 0 17 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 17) owner_valid010
  scope010 binding0431_0 certificate010

theorem case_closed0432 : CoreExcluded (baseCore 0 17 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 17) owner_valid011
  scope011 binding0432_0 certificate011

theorem case_closed0433 : CoreExcluded (baseCore 0 17 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 17) owner_valid012
  scope012 binding0433_0 certificate012

theorem case_closed0434 : CoreExcluded (baseCore 0 17 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout116
  (layout_for_all_rows 9 layout116 layout_valid116 0 17) owner_valid116
  scope416 binding0434_0 certificate424

theorem case_closed0435 : CoreExcluded (baseCore 0 17 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout062
  (layout_for_all_rows 10 layout062 layout_valid062 0 17) owner_valid062
  scope416 binding0435_0 certificate424

theorem case_closed0436 : CoreExcluded (baseCore 0 17 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 17) owner_valid017
  scope017 binding0436_0 certificate017

theorem case_closed0437 : CoreExcluded (baseCore 0 17 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 17) owner_valid018
  scope018 binding0437_0 certificate018

theorem case_closed0438 : CoreExcluded (baseCore 0 17 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 17) owner_valid019
  scope019 binding0438_0 certificate019

theorem case_closed0439 : CoreExcluded (baseCore 0 17 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 17) owner_valid020
  scope020 binding0439_0 certificate020

theorem case_closed0440 : CoreExcluded (baseCore 0 17 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 17) owner_valid021
  scope021 binding0440_0 certificate021

theorem case_closed0441 : CoreExcluded (baseCore 0 17 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 17) owner_valid022
  scope022 binding0441_0 certificate022

theorem case_closed0442 : CoreExcluded (baseCore 0 17 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 17) owner_valid023
  scope023 binding0442_0 certificate023

theorem case_closed0443 : CoreExcluded (baseCore 0 17 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 17) owner_valid024
  scope024 binding0443_0 certificate024

theorem case_closed0444 : CoreExcluded (baseCore 0 17 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 17) owner_valid025
  scope025 binding0444_0 certificate025

theorem case_closed0445 : CoreExcluded (baseCore 0 17 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 17) owner_valid026
  scope026 binding0445_0 certificate026

theorem case_closed0446 : CoreExcluded (baseCore 0 17 21) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout050 layout051
  (layout_for_all_rows 21 layout050 layout_valid050 0 17)
  (layout_for_all_rows 21 layout051 layout_valid051 0 17)
  owner_valid050 owner_valid051 scope406 scope057
  binding0446_0 binding0446_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate425 certificate057 (by decide)

theorem case_closed0447 : CoreExcluded (baseCore 0 17 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout052 layout053
  (layout_for_all_rows 22 layout052 layout_valid052 0 17)
  (layout_for_all_rows 22 layout053 layout_valid053 0 17)
  owner_valid052 owner_valid053 scope407 scope059
  binding0447_0 binding0447_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate426 certificate427 (by decide)

theorem case_closed0448 : CoreExcluded (baseCore 0 17 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 17) owner_valid031
  scope031 binding0448_0 certificate031

theorem case_closed0449 : CoreExcluded (baseCore 0 17 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 17) owner_valid032
  scope032 binding0449_0 certificate032

theorem case_closed0450 : CoreExcluded (baseCore 0 18 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 18) owner_valid033
  scope095 binding0450_0 certificate095

theorem case_closed0451 : CoreExcluded (baseCore 0 18 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 0 18) owner_valid075
  scope034 binding0451_0 certificate034

theorem case_closed0452 : CoreExcluded (baseCore 0 18 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 0 18) owner_valid003
  scope035 binding0452_0 certificate035

theorem case_closed0453 : CoreExcluded (baseCore 0 18 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 0 18) owner_valid077
  scope036 binding0453_0 certificate036

theorem case_closed0454 : CoreExcluded (baseCore 0 18 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 0 18) owner_valid007
  scope037 binding0454_0 certificate037

theorem case_closed0455 : CoreExcluded (baseCore 0 18 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 18) owner_valid009
  scope104 binding0455_0 certificate104

theorem case_closed0456 : CoreExcluded (baseCore 0 18 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 18) owner_valid010
  scope105 binding0456_0 certificate105

theorem case_closed0457 : CoreExcluded (baseCore 0 18 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 18) owner_valid011
  scope106 binding0457_0 certificate106

theorem case_closed0458 : CoreExcluded (baseCore 0 18 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 18) owner_valid012
  scope107 binding0458_0 certificate107

theorem case_closed0459 : CoreExcluded (baseCore 0 18 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 18) owner_valid038
  scope108 binding0459_0 certificate108

theorem case_closed0460 : CoreExcluded (baseCore 0 18 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 18) owner_valid079
  scope109 binding0460_0 certificate109

theorem case_closed0461 : CoreExcluded (baseCore 0 18 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 18) owner_valid017
  scope110 binding0461_0 certificate110

theorem case_closed0462 : CoreExcluded (baseCore 0 18 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 18) owner_valid018
  scope111 binding0462_0 certificate111

theorem case_closed0463 : CoreExcluded (baseCore 0 18 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 18) owner_valid019
  scope112 binding0463_0 certificate112

theorem case_closed0464 : CoreExcluded (baseCore 0 18 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 18) owner_valid020
  scope113 binding0464_0 certificate113

theorem case_closed0465 : CoreExcluded (baseCore 0 18 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 18) owner_valid021
  scope114 binding0465_0 certificate114

theorem case_closed0466 : CoreExcluded (baseCore 0 18 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 18) owner_valid022
  scope115 binding0466_0 certificate115

theorem case_closed0467 : CoreExcluded (baseCore 0 18 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout045 layout046
  (layout_for_all_rows 17 layout045 layout_valid045 0 18)
  (layout_for_all_rows 17 layout046 layout_valid046 0 18)
  owner_valid045 owner_valid046 scope116 scope051
  binding0467_0 binding0467_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate428 certificate051 (by decide)

theorem case_closed0468 : CoreExcluded (baseCore 0 18 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout068 layout186
  (layout_for_all_rows 18 layout068 layout_valid068 0 18)
  (layout_for_all_rows 18 layout186 layout_valid186 0 18)
  owner_valid068 owner_valid186 scope052 scope417
  binding0468_0 binding0468_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate052 certificate429 (by decide)

theorem case_closed0469 : CoreExcluded (baseCore 0 18 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout049
  (layout_for_all_rows 19 layout049 layout_valid049 0 18) owner_valid049
  scope054 binding0469_0 certificate054

theorem case_closed0470 : CoreExcluded (baseCore 0 18 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 18) owner_valid070
  scope055 binding0470_0 certificate055

theorem case_closed0471 : CoreExcluded (baseCore 0 18 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 18) owner_valid087
  scope124 binding0471_0 certificate124

theorem case_closed0472 : CoreExcluded (baseCore 0 18 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 18) owner_valid072
  scope125 binding0472_0 certificate125

theorem case_closed0473 : CoreExcluded (baseCore 0 18 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 18) owner_valid031
  scope126 binding0473_0 certificate126

theorem case_closed0474 : CoreExcluded (baseCore 0 18 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 18) owner_valid032
  scope127 binding0474_0 certificate127

theorem case_closed0475 : CoreExcluded (baseCore 0 19 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 0 19) owner_valid187
  scope033 binding0475_0 certificate033

theorem case_closed0476 : CoreExcluded (baseCore 0 19 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 0 19) owner_valid075
  scope034 binding0476_0 certificate034

theorem case_closed0477 : CoreExcluded (baseCore 0 19 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 19) owner_valid034
  scope132 binding0477_0 certificate132

theorem case_closed0478 : CoreExcluded (baseCore 0 19 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 0 19) owner_valid077
  scope036 binding0478_0 certificate036

theorem case_closed0479 : CoreExcluded (baseCore 0 19 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 0 19) owner_valid007
  scope037 binding0479_0 certificate037

theorem case_closed0480 : CoreExcluded (baseCore 0 19 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 19) owner_valid037
  scope038 binding0480_0 certificate038

theorem case_closed0481 : CoreExcluded (baseCore 0 19 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout147
  (layout_for_all_rows 6 layout147 layout_valid147 0 19) owner_valid147
  scope418 binding0481_0 certificate430

theorem case_closed0482 : CoreExcluded (baseCore 0 19 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 19) owner_valid011
  scope141 binding0482_0 certificate141

theorem case_closed0483 : CoreExcluded (baseCore 0 19 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 19) owner_valid012
  scope142 binding0483_0 certificate142

theorem case_closed0484 : CoreExcluded (baseCore 0 19 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 19) owner_valid038
  scope143 binding0484_0 certificate143

theorem case_closed0485 : CoreExcluded (baseCore 0 19 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 19) owner_valid079
  scope144 binding0485_0 certificate144

theorem case_closed0486 : CoreExcluded (baseCore 0 19 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 19) owner_valid017
  scope145 binding0486_0 certificate145

theorem case_closed0487 : CoreExcluded (baseCore 0 19 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 19) owner_valid018
  scope146 binding0487_0 certificate146

theorem case_closed0488 : CoreExcluded (baseCore 0 19 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 19) owner_valid019
  scope147 binding0488_0 certificate147

theorem case_closed0489 : CoreExcluded (baseCore 0 19 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 19) owner_valid020
  scope148 binding0489_0 certificate148

theorem case_closed0490 : CoreExcluded (baseCore 0 19 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 19) owner_valid021
  scope149 binding0490_0 certificate149

theorem case_closed0491 : CoreExcluded (baseCore 0 19 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 19) owner_valid022
  scope150 binding0491_0 certificate150

theorem case_closed0492 : CoreExcluded (baseCore 0 19 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 19) owner_valid023
  scope151 binding0492_0 certificate151

theorem case_closed0493 : CoreExcluded (baseCore 0 19 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 19) owner_valid024
  scope152 binding0493_0 certificate152

theorem case_closed0494 : CoreExcluded (baseCore 0 19 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 19) owner_valid025
  scope153 binding0494_0 certificate153

theorem case_closed0495 : CoreExcluded (baseCore 0 19 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 19) owner_valid026
  scope154 binding0495_0 certificate154

theorem case_closed0496 : CoreExcluded (baseCore 0 19 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 19) owner_valid087
  scope155 binding0496_0 certificate155

theorem case_closed0497 : CoreExcluded (baseCore 0 19 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 19) owner_valid072
  scope156 binding0497_0 certificate156

theorem case_closed0498 : CoreExcluded (baseCore 0 19 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout055
  (layout_for_all_rows 23 layout054 layout_valid054 0 19)
  (layout_for_all_rows 23 layout055 layout_valid055 0 19)
  owner_valid054 owner_valid055 scope060 scope157
  binding0498_0 binding0498_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate431 certificate432 (by decide)

theorem case_closed0499 : CoreExcluded (baseCore 0 19 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout056 layout057
  (layout_for_all_rows 24 layout056 layout_valid056 0 19)
  (layout_for_all_rows 24 layout057 layout_valid057 0 19)
  owner_valid056 owner_valid057 scope159 scope063
  binding0499_0 binding0499_1
  2 5 2 5 (by decide) (by decide) 3 2 (by decide)
  certificate159 certificate433 (by decide)

theorem block_closed004 (i : Fin 100) : CoreExcluded (caseCore (blockCase 4 i)) := by
 fin_cases i
 · exact case_closed0400
 · exact case_closed0401
 · exact case_closed0402
 · exact case_closed0403
 · exact case_closed0404
 · exact case_closed0405
 · exact case_closed0406
 · exact case_closed0407
 · exact case_closed0408
 · exact case_closed0409
 · exact case_closed0410
 · exact case_closed0411
 · exact case_closed0412
 · exact case_closed0413
 · exact case_closed0414
 · exact case_closed0415
 · exact case_closed0416
 · exact case_closed0417
 · exact case_closed0418
 · exact case_closed0419
 · exact case_closed0420
 · exact case_closed0421
 · exact case_closed0422
 · exact case_closed0423
 · exact case_closed0424
 · exact case_closed0425
 · exact case_closed0426
 · exact case_closed0427
 · exact case_closed0428
 · exact case_closed0429
 · exact case_closed0430
 · exact case_closed0431
 · exact case_closed0432
 · exact case_closed0433
 · exact case_closed0434
 · exact case_closed0435
 · exact case_closed0436
 · exact case_closed0437
 · exact case_closed0438
 · exact case_closed0439
 · exact case_closed0440
 · exact case_closed0441
 · exact case_closed0442
 · exact case_closed0443
 · exact case_closed0444
 · exact case_closed0445
 · exact case_closed0446
 · exact case_closed0447
 · exact case_closed0448
 · exact case_closed0449
 · exact case_closed0450
 · exact case_closed0451
 · exact case_closed0452
 · exact case_closed0453
 · exact case_closed0454
 · exact case_closed0455
 · exact case_closed0456
 · exact case_closed0457
 · exact case_closed0458
 · exact case_closed0459
 · exact case_closed0460
 · exact case_closed0461
 · exact case_closed0462
 · exact case_closed0463
 · exact case_closed0464
 · exact case_closed0465
 · exact case_closed0466
 · exact case_closed0467
 · exact case_closed0468
 · exact case_closed0469
 · exact case_closed0470
 · exact case_closed0471
 · exact case_closed0472
 · exact case_closed0473
 · exact case_closed0474
 · exact case_closed0475
 · exact case_closed0476
 · exact case_closed0477
 · exact case_closed0478
 · exact case_closed0479
 · exact case_closed0480
 · exact case_closed0481
 · exact case_closed0482
 · exact case_closed0483
 · exact case_closed0484
 · exact case_closed0485
 · exact case_closed0486
 · exact case_closed0487
 · exact case_closed0488
 · exact case_closed0489
 · exact case_closed0490
 · exact case_closed0491
 · exact case_closed0492
 · exact case_closed0493
 · exact case_closed0494
 · exact case_closed0495
 · exact case_closed0496
 · exact case_closed0497
 · exact case_closed0498
 · exact case_closed0499
end PricingC.GIsomorphic