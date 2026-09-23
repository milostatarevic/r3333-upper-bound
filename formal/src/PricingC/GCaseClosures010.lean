import PricingC.GCoreExcluded
import PricingC.GBindings010
import PricingC.GScopeChecks002
import PricingC.GScopeChecks003
import PricingC.GScopeChecks004
import PricingC.GScopeChecks005
import PricingC.GScopeChecks011
import PricingC.GScopeChecks012
import PricingC.GScopeChecks013
import PricingC.GScopeChecks014
import PricingC.GScopeChecks018
import PricingC.GScopeChecks019
import PricingC.GScopeChecks020
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks034
import PricingC.GScopeChecks035
import PricingC.GScopeChecks036
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks006

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed1000 : CoreExcluded (baseCore 0 40 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout000 layout088
  (layout_for_all_rows 0 layout000 layout_valid000 0 40)
  (layout_for_all_rows 0 layout088 layout_valid088 0 40)
  owner_valid000 owner_valid088 scope403 scope297
  binding1000_0 binding1000_1
  0 8 0 8 (by decide) (by decide) 3 2 (by decide)
  certificate554 certificate297 (by decide)

theorem case_closed1001 : CoreExcluded (baseCore 0 40 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout152 layout076
  (layout_for_all_rows 1 layout152 layout_valid152 0 40)
  (layout_for_all_rows 1 layout076 layout_valid076 0 40)
  owner_valid152 owner_valid076 scope298 scope472
  binding1001_0 binding1001_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate298 certificate555 (by decide)

theorem case_closed1002 : CoreExcluded (baseCore 0 40 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout153 layout154
  (layout_for_all_rows 2 layout153 layout_valid153 0 40)
  (layout_for_all_rows 2 layout154 layout_valid154 0 40)
  owner_valid153 owner_valid154 scope300 scope483
  binding1002_0 binding1002_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate300 certificate556 (by decide)

theorem case_closed1003 : CoreExcluded (baseCore 0 40 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 40) owner_valid035
  scope302 binding1003_0 certificate302

theorem case_closed1004 : CoreExcluded (baseCore 0 40 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout008 layout155
  (layout_for_all_rows 4 layout008 layout_valid008 0 40)
  (layout_for_all_rows 4 layout155 layout_valid155 0 40)
  owner_valid008 owner_valid155 scope169 scope304
  binding1004_0 binding1004_1
  0 8 0 8 (by decide) (by decide) 2 3 (by decide)
  certificate557 certificate304 (by decide)

theorem case_closed1005 : CoreExcluded (baseCore 0 40 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 40) owner_valid009
  scope305 binding1005_0 certificate305

theorem case_closed1006 : CoreExcluded (baseCore 0 40 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 40) owner_valid010
  scope306 binding1006_0 certificate306

theorem case_closed1007 : CoreExcluded (baseCore 0 40 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 40) owner_valid011
  scope307 binding1007_0 certificate307

theorem case_closed1008 : CoreExcluded (baseCore 0 40 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 40) owner_valid012
  scope308 binding1008_0 certificate308

theorem case_closed1009 : CoreExcluded (baseCore 0 40 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 40) owner_valid038
  scope309 binding1009_0 certificate309

theorem case_closed1010 : CoreExcluded (baseCore 0 40 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 40) owner_valid079
  scope310 binding1010_0 certificate310

theorem case_closed1011 : CoreExcluded (baseCore 0 40 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout040 layout118
  (layout_for_all_rows 11 layout040 layout_valid040 0 40)
  (layout_for_all_rows 11 layout118 layout_valid118 0 40)
  owner_valid040 owner_valid118 scope183 scope137
  binding1011_0 binding1011_1
  3 5 3 5 (by decide) (by decide) 3 2 (by decide)
  certificate558 certificate559 (by decide)

theorem case_closed1012 : CoreExcluded (baseCore 0 40 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout119 layout120
  (layout_for_all_rows 12 layout119 layout_valid119 0 40)
  (layout_for_all_rows 12 layout120 layout_valid120 0 40)
  owner_valid119 owner_valid120 scope185 scope139
  binding1012_0 binding1012_1
  3 5 3 5 (by decide) (by decide) 2 3 (by decide)
  certificate560 certificate561 (by decide)

theorem case_closed1013 : CoreExcluded (baseCore 0 40 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout121 layout122
  (layout_for_all_rows 13 layout121 layout_valid121 0 40)
  (layout_for_all_rows 13 layout122 layout_valid122 0 40)
  owner_valid121 owner_valid122 scope484 scope188
  binding1013_0 binding1013_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate562 certificate563 (by decide)

theorem case_closed1014 : CoreExcluded (baseCore 0 40 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout123 layout124
  (layout_for_all_rows 14 layout123 layout_valid123 0 40)
  (layout_for_all_rows 14 layout124 layout_valid124 0 40)
  owner_valid123 owner_valid124 scope485 scope190
  binding1014_0 binding1014_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate564 certificate565 (by decide)

theorem case_closed1015 : CoreExcluded (baseCore 0 40 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 40) owner_valid021
  scope319 binding1015_0 certificate319

theorem case_closed1016 : CoreExcluded (baseCore 0 40 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 40) owner_valid022
  scope320 binding1016_0 certificate320

theorem case_closed1017 : CoreExcluded (baseCore 0 40 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 40) owner_valid023
  scope321 binding1017_0 certificate321

theorem case_closed1018 : CoreExcluded (baseCore 0 40 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 40) owner_valid024
  scope322 binding1018_0 certificate322

theorem case_closed1019 : CoreExcluded (baseCore 0 40 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 40) owner_valid025
  scope323 binding1019_0 certificate323

theorem case_closed1020 : CoreExcluded (baseCore 0 40 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 40) owner_valid026
  scope324 binding1020_0 certificate324

theorem case_closed1021 : CoreExcluded (baseCore 0 40 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 40) owner_valid087
  scope325 binding1021_0 certificate325

theorem case_closed1022 : CoreExcluded (baseCore 0 40 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 40) owner_valid072
  scope326 binding1022_0 certificate326

theorem case_closed1023 : CoreExcluded (baseCore 0 40 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 40) owner_valid031
  scope327 binding1023_0 certificate327

theorem case_closed1024 : CoreExcluded (baseCore 0 40 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 40) owner_valid032
  scope328 binding1024_0 certificate328

theorem case_closed1025 : CoreExcluded (baseCore 0 41 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout164 layout001
  (layout_for_all_rows 0 layout164 layout_valid164 0 41)
  (layout_for_all_rows 0 layout001 layout_valid001 0 41)
  owner_valid164 owner_valid001 scope329 scope471
  binding1025_0 binding1025_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate566 certificate567 (by decide)

theorem case_closed1026 : CoreExcluded (baseCore 0 41 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout165 layout089
  (layout_for_all_rows 1 layout165 layout_valid165 0 41)
  (layout_for_all_rows 1 layout089 layout_valid089 0 41)
  owner_valid165 owner_valid089 scope331 scope480
  binding1026_0 binding1026_1
  3 7 2 6 (by decide) (by decide) 2 3 (by decide)
  certificate568 certificate569 (by decide)

theorem case_closed1027 : CoreExcluded (baseCore 0 41 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout153 layout154
  (layout_for_all_rows 2 layout153 layout_valid153 0 41)
  (layout_for_all_rows 2 layout154 layout_valid154 0 41)
  owner_valid153 owner_valid154 scope333 scope483
  binding1027_0 binding1027_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate570 certificate571 (by decide)

theorem case_closed1028 : CoreExcluded (baseCore 0 41 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout166 layout167
  (layout_for_all_rows 3 layout166 layout_valid166 0 41)
  (layout_for_all_rows 3 layout167 layout_valid167 0 41)
  owner_valid166 owner_valid167 scope335 scope486
  binding1028_0 binding1028_1
  3 7 2 6 (by decide) (by decide) 3 2 (by decide)
  certificate572 certificate573 (by decide)

theorem case_closed1029 : CoreExcluded (baseCore 0 41 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 41) owner_valid036
  scope337 binding1029_0 certificate337

theorem case_closed1030 : CoreExcluded (baseCore 0 41 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 41) owner_valid009
  scope338 binding1030_0 certificate338

theorem case_closed1031 : CoreExcluded (baseCore 0 41 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 41) owner_valid010
  scope339 binding1031_0 certificate339

theorem case_closed1032 : CoreExcluded (baseCore 0 41 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout112 layout113
  (layout_for_all_rows 7 layout112 layout_valid112 0 41)
  (layout_for_all_rows 7 layout113 layout_valid113 0 41)
  owner_valid112 owner_valid113 scope487 scope176
  binding1032_0 binding1032_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate574 certificate176 (by decide)

theorem case_closed1033 : CoreExcluded (baseCore 0 41 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout114 layout115
  (layout_for_all_rows 8 layout114 layout_valid114 0 41)
  (layout_for_all_rows 8 layout115 layout_valid115 0 41)
  owner_valid114 owner_valid115 scope488 scope178
  binding1033_0 binding1033_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate575 certificate178 (by decide)

theorem case_closed1034 : CoreExcluded (baseCore 0 41 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 41) owner_valid038
  scope343 binding1034_0 certificate344

theorem case_closed1035 : CoreExcluded (baseCore 0 41 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 41) owner_valid079
  scope344 binding1035_0 certificate345

theorem case_closed1036 : CoreExcluded (baseCore 0 41 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 41) owner_valid017
  scope345 binding1036_0 certificate346

theorem case_closed1037 : CoreExcluded (baseCore 0 41 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 41) owner_valid018
  scope346 binding1037_0 certificate347

theorem case_closed1038 : CoreExcluded (baseCore 0 41 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 41) owner_valid019
  scope347 binding1038_0 certificate348

theorem case_closed1039 : CoreExcluded (baseCore 0 41 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 41) owner_valid020
  scope348 binding1039_0 certificate349

theorem case_closed1040 : CoreExcluded (baseCore 0 41 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout125 layout126
  (layout_for_all_rows 15 layout125 layout_valid125 0 41)
  (layout_for_all_rows 15 layout126 layout_valid126 0 41)
  owner_valid125 owner_valid126 scope489 scope192
  binding1040_0 binding1040_1
  2 8 1 7 (by decide) (by decide) 3 2 (by decide)
  certificate576 certificate192 (by decide)

theorem case_closed1041 : CoreExcluded (baseCore 0 41 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout127 layout128
  (layout_for_all_rows 16 layout127 layout_valid127 0 41)
  (layout_for_all_rows 16 layout128 layout_valid128 0 41)
  owner_valid127 owner_valid128 scope351 scope194
  binding1041_0 binding1041_1
  2 8 1 7 (by decide) (by decide) 2 3 (by decide)
  certificate352 certificate194 (by decide)

theorem case_closed1042 : CoreExcluded (baseCore 0 41 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 41) owner_valid023
  scope353 binding1042_0 certificate354

theorem case_closed1043 : CoreExcluded (baseCore 0 41 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 41) owner_valid024
  scope354 binding1043_0 certificate355

theorem case_closed1044 : CoreExcluded (baseCore 0 41 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 41) owner_valid025
  scope355 binding1044_0 certificate356

theorem case_closed1045 : CoreExcluded (baseCore 0 41 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 41) owner_valid026
  scope356 binding1045_0 certificate357

theorem case_closed1046 : CoreExcluded (baseCore 0 41 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 41) owner_valid087
  scope357 binding1046_0 certificate358

theorem case_closed1047 : CoreExcluded (baseCore 0 41 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 41) owner_valid072
  scope358 binding1047_0 certificate359

theorem case_closed1048 : CoreExcluded (baseCore 0 41 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 41) owner_valid031
  scope359 binding1048_0 certificate360

theorem case_closed1049 : CoreExcluded (baseCore 0 41 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 41) owner_valid032
  scope360 binding1049_0 certificate361

theorem case_closed1050 : CoreExcluded (baseCore 0 42 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 42) owner_valid033
  scope033 binding1050_0 certificate033

theorem case_closed1051 : CoreExcluded (baseCore 0 42 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 42) owner_valid002
  scope034 binding1051_0 certificate034

theorem case_closed1052 : CoreExcluded (baseCore 0 42 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 42) owner_valid034
  scope035 binding1052_0 certificate035

theorem case_closed1053 : CoreExcluded (baseCore 0 42 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 42) owner_valid035
  scope036 binding1053_0 certificate036

theorem case_closed1054 : CoreExcluded (baseCore 0 42 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 42) owner_valid036
  scope037 binding1054_0 certificate037

theorem case_closed1055 : CoreExcluded (baseCore 0 42 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 42) owner_valid037
  scope217 binding1055_0 certificate217

theorem case_closed1056 : CoreExcluded (baseCore 0 42 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 42) owner_valid010
  scope038 binding1056_0 certificate038

theorem case_closed1057 : CoreExcluded (baseCore 0 42 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 42) owner_valid011
  scope039 binding1057_0 certificate039

theorem case_closed1058 : CoreExcluded (baseCore 0 42 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 42) owner_valid012
  scope040 binding1058_0 certificate040

theorem case_closed1059 : CoreExcluded (baseCore 0 42 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 42) owner_valid038
  scope041 binding1059_0 certificate041

theorem case_closed1060 : CoreExcluded (baseCore 0 42 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 0 42) owner_valid039
  scope220 binding1060_0 certificate220

theorem case_closed1061 : CoreExcluded (baseCore 0 42 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 42) owner_valid149
  scope223 binding1061_0 certificate223

theorem case_closed1062 : CoreExcluded (baseCore 0 42 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 42) owner_valid042
  scope222 binding1062_0 certificate222

theorem case_closed1063 : CoreExcluded (baseCore 0 42 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 0 42) owner_valid137
  scope224 binding1063_0 certificate224

theorem case_closed1064 : CoreExcluded (baseCore 0 42 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 42) owner_valid020
  scope047 binding1064_0 certificate047

theorem case_closed1065 : CoreExcluded (baseCore 0 42 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 42) owner_valid021
  scope048 binding1065_0 certificate048

theorem case_closed1066 : CoreExcluded (baseCore 0 42 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 42) owner_valid022
  scope049 binding1066_0 certificate049

theorem case_closed1067 : CoreExcluded (baseCore 0 42 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 0 42) owner_valid129
  scope228 binding1067_0 certificate228

theorem case_closed1068 : CoreExcluded (baseCore 0 42 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 0 42) owner_valid130
  scope229 binding1068_0 certificate229

theorem case_closed1069 : CoreExcluded (baseCore 0 42 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 0 42) owner_valid131
  scope230 binding1069_0 certificate230

theorem case_closed1070 : CoreExcluded (baseCore 0 42 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 42) owner_valid026
  scope055 binding1070_0 certificate055

theorem case_closed1071 : CoreExcluded (baseCore 0 42 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 0 42) owner_valid050
  scope232 binding1071_0 certificate232

theorem case_closed1072 : CoreExcluded (baseCore 0 42 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 0 42) owner_valid052
  scope233 binding1072_0 certificate233

theorem case_closed1073 : CoreExcluded (baseCore 0 42 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 42) owner_valid054
  scope234 binding1073_0 certificate234

theorem case_closed1074 : CoreExcluded (baseCore 0 42 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 0 42) owner_valid074
  scope235 binding1074_0 certificate235

theorem case_closed1075 : CoreExcluded (baseCore 0 43 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 43) owner_valid033
  scope064 binding1075_0 certificate064

theorem case_closed1076 : CoreExcluded (baseCore 0 43 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 43) owner_valid002
  scope065 binding1076_0 certificate065

theorem case_closed1077 : CoreExcluded (baseCore 0 43 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 43) owner_valid034
  scope066 binding1077_0 certificate066

theorem case_closed1078 : CoreExcluded (baseCore 0 43 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 43) owner_valid035
  scope067 binding1078_0 certificate067

theorem case_closed1079 : CoreExcluded (baseCore 0 43 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 43) owner_valid036
  scope068 binding1079_0 certificate068

theorem case_closed1080 : CoreExcluded (baseCore 0 43 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 43) owner_valid009
  scope069 binding1080_0 certificate069

theorem case_closed1081 : CoreExcluded (baseCore 0 43 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 43) owner_valid058
  scope216 binding1081_0 certificate216

theorem case_closed1082 : CoreExcluded (baseCore 0 43 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 0 43) owner_valid059
  scope219 binding1082_0 certificate219

theorem case_closed1083 : CoreExcluded (baseCore 0 43 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 43) owner_valid012
  scope070 binding1083_0 certificate070

theorem case_closed1084 : CoreExcluded (baseCore 0 43 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 43) owner_valid136
  scope221 binding1084_0 certificate221

theorem case_closed1085 : CoreExcluded (baseCore 0 43 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 0 43) owner_valid039
  scope220 binding1085_0 certificate220

theorem case_closed1086 : CoreExcluded (baseCore 0 43 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 43) owner_valid017
  scope075 binding1086_0 certificate075

theorem case_closed1087 : CoreExcluded (baseCore 0 43 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 43) owner_valid018
  scope076 binding1087_0 certificate076

theorem case_closed1088 : CoreExcluded (baseCore 0 43 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 43) owner_valid019
  scope077 binding1088_0 certificate077

theorem case_closed1089 : CoreExcluded (baseCore 0 43 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 43) owner_valid020
  scope078 binding1089_0 certificate078

theorem case_closed1090 : CoreExcluded (baseCore 0 43 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 0 43) owner_valid064
  scope226 binding1090_0 certificate226

theorem case_closed1091 : CoreExcluded (baseCore 0 43 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 0 43) owner_valid180
  scope227 binding1091_0 certificate227

theorem case_closed1092 : CoreExcluded (baseCore 0 43 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 43) owner_valid023
  scope083 binding1092_0 certificate083

theorem case_closed1093 : CoreExcluded (baseCore 0 43 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 0 43) owner_valid130
  scope229 binding1093_0 certificate229

theorem case_closed1094 : CoreExcluded (baseCore 0 43 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 0 43) owner_valid131
  scope230 binding1094_0 certificate230

theorem case_closed1095 : CoreExcluded (baseCore 0 43 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 43) owner_valid070
  scope231 binding1095_0 certificate231

theorem case_closed1096 : CoreExcluded (baseCore 0 43 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 0 43) owner_valid050
  scope232 binding1096_0 certificate232

theorem case_closed1097 : CoreExcluded (baseCore 0 43 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 43) owner_valid072
  scope090 binding1097_0 certificate090

theorem case_closed1098 : CoreExcluded (baseCore 0 43 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 43) owner_valid054
  scope234 binding1098_0 certificate234

theorem case_closed1099 : CoreExcluded (baseCore 0 43 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 0 43) owner_valid074
  scope235 binding1099_0 certificate235

theorem block_closed010 (i : Fin 100) : CoreExcluded (caseCore (blockCase 10 i)) := by
 fin_cases i
 · exact case_closed1000
 · exact case_closed1001
 · exact case_closed1002
 · exact case_closed1003
 · exact case_closed1004
 · exact case_closed1005
 · exact case_closed1006
 · exact case_closed1007
 · exact case_closed1008
 · exact case_closed1009
 · exact case_closed1010
 · exact case_closed1011
 · exact case_closed1012
 · exact case_closed1013
 · exact case_closed1014
 · exact case_closed1015
 · exact case_closed1016
 · exact case_closed1017
 · exact case_closed1018
 · exact case_closed1019
 · exact case_closed1020
 · exact case_closed1021
 · exact case_closed1022
 · exact case_closed1023
 · exact case_closed1024
 · exact case_closed1025
 · exact case_closed1026
 · exact case_closed1027
 · exact case_closed1028
 · exact case_closed1029
 · exact case_closed1030
 · exact case_closed1031
 · exact case_closed1032
 · exact case_closed1033
 · exact case_closed1034
 · exact case_closed1035
 · exact case_closed1036
 · exact case_closed1037
 · exact case_closed1038
 · exact case_closed1039
 · exact case_closed1040
 · exact case_closed1041
 · exact case_closed1042
 · exact case_closed1043
 · exact case_closed1044
 · exact case_closed1045
 · exact case_closed1046
 · exact case_closed1047
 · exact case_closed1048
 · exact case_closed1049
 · exact case_closed1050
 · exact case_closed1051
 · exact case_closed1052
 · exact case_closed1053
 · exact case_closed1054
 · exact case_closed1055
 · exact case_closed1056
 · exact case_closed1057
 · exact case_closed1058
 · exact case_closed1059
 · exact case_closed1060
 · exact case_closed1061
 · exact case_closed1062
 · exact case_closed1063
 · exact case_closed1064
 · exact case_closed1065
 · exact case_closed1066
 · exact case_closed1067
 · exact case_closed1068
 · exact case_closed1069
 · exact case_closed1070
 · exact case_closed1071
 · exact case_closed1072
 · exact case_closed1073
 · exact case_closed1074
 · exact case_closed1075
 · exact case_closed1076
 · exact case_closed1077
 · exact case_closed1078
 · exact case_closed1079
 · exact case_closed1080
 · exact case_closed1081
 · exact case_closed1082
 · exact case_closed1083
 · exact case_closed1084
 · exact case_closed1085
 · exact case_closed1086
 · exact case_closed1087
 · exact case_closed1088
 · exact case_closed1089
 · exact case_closed1090
 · exact case_closed1091
 · exact case_closed1092
 · exact case_closed1093
 · exact case_closed1094
 · exact case_closed1095
 · exact case_closed1096
 · exact case_closed1097
 · exact case_closed1098
 · exact case_closed1099
end PricingC.GIsomorphic