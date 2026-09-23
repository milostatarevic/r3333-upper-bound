import PricingC.GCoreExcluded
import PricingC.GBindings031
import PricingC.GScopeChecks000
import PricingC.GScopeChecks001
import PricingC.GScopeChecks005
import PricingC.GScopeChecks012
import PricingC.GScopeChecks013
import PricingC.GScopeChecks014
import PricingC.GScopeChecks015
import PricingC.GScopeChecks016
import PricingC.GScopeChecks017
import PricingC.GScopeChecks018
import PricingC.GScopeChecks019
import PricingC.GScopeChecks022
import PricingC.GScopeChecks025
import PricingC.GScopeChecks027
import PricingC.GScopeChecks028
import PricingC.GScopeChecks036
import PricingC.GScopeChecks037
import PricingC.GScopeChecks038
import PricingC.GScopeChecks039
import PricingC.GScopeChecks041
import PricingC.GScopeChecks042
import PricingC.GScopeChecks046
import PricingC.GScopeChecks047
import PricingC.GScopeChecks048
import PricingC.GScopeChecks049
import PricingC.GScopeChecks056
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks006
import PricingC.GLayoutChecks007

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed3100 : CoreExcluded (baseCore 1 52 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 52) owner_valid033
  scope426 binding3100_0 certificate441

theorem case_closed3101 : CoreExcluded (baseCore 1 52 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 52) owner_valid002
  scope425 binding3101_0 certificate440

theorem case_closed3102 : CoreExcluded (baseCore 1 52 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 52) owner_valid034
  scope552 binding3102_0 certificate677

theorem case_closed3103 : CoreExcluded (baseCore 1 52 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 52) owner_valid035
  scope427 binding3103_0 certificate442

theorem case_closed3104 : CoreExcluded (baseCore 1 52 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 52) owner_valid036
  scope428 binding3104_0 certificate443

theorem case_closed3105 : CoreExcluded (baseCore 1 52 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout037 layout108
  (layout_for_all_rows 5 layout037 layout_valid037 1 52)
  (layout_for_all_rows 5 layout108 layout_valid108 1 52)
  owner_valid037 owner_valid108 scope711 scope725
  binding3105_0 binding3105_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate900 certificate901 (by decide)

theorem case_closed3106 : CoreExcluded (baseCore 1 52 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 52) owner_valid010
  scope429 binding3106_0 certificate444

theorem case_closed3107 : CoreExcluded (baseCore 1 52 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 52) owner_valid011
  scope553 binding3107_0 certificate678

theorem case_closed3108 : CoreExcluded (baseCore 1 52 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 52) owner_valid012
  scope554 binding3108_0 certificate679

theorem case_closed3109 : CoreExcluded (baseCore 1 52 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout013 layout014
  (layout_for_all_rows 9 layout013 layout_valid013 1 52)
  (layout_for_all_rows 9 layout014 layout_valid014 1 52)
  owner_valid013 owner_valid014 scope726 scope014
  binding3109_0 binding3109_1
  2 9 7 4 (by decide) (by decide) 3 2 (by decide)
  certificate902 certificate014 (by decide)

theorem case_closed3110 : CoreExcluded (baseCore 1 52 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout015 layout016
  (layout_for_all_rows 10 layout015 layout_valid015 1 52)
  (layout_for_all_rows 10 layout016 layout_valid016 1 52)
  owner_valid015 owner_valid016 scope727 scope016
  binding3110_0 binding3110_1
  0 6 6 2 (by decide) (by decide) 2 3 (by decide)
  certificate903 certificate016 (by decide)

theorem case_closed3111 : CoreExcluded (baseCore 1 52 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 52) owner_valid017
  scope084 binding3111_0 certificate084

theorem case_closed3112 : CoreExcluded (baseCore 1 52 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout042 layout119
  (layout_for_all_rows 12 layout042 layout_valid042 1 52)
  (layout_for_all_rows 12 layout119 layout_valid119 1 52)
  owner_valid042 owner_valid119 scope282 scope283
  binding3112_0 binding3112_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate282 certificate283 (by decide)

theorem case_closed3113 : CoreExcluded (baseCore 1 52 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 52) owner_valid137
  scope284 binding3113_0 certificate284

theorem case_closed3114 : CoreExcluded (baseCore 1 52 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 52) owner_valid020
  scope433 binding3114_0 certificate451

theorem case_closed3115 : CoreExcluded (baseCore 1 52 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout150
  (layout_for_all_rows 15 layout150 layout_valid150 1 52) owner_valid150
  scope286 binding3115_0 certificate286

theorem case_closed3116 : CoreExcluded (baseCore 1 52 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 52) owner_valid180
  scope287 binding3116_0 certificate287

theorem case_closed3117 : CoreExcluded (baseCore 1 52 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 52) owner_valid023
  scope556 binding3117_0 certificate682

theorem case_closed3118 : CoreExcluded (baseCore 1 52 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 52) owner_valid024
  scope557 binding3118_0 certificate683

theorem case_closed3119 : CoreExcluded (baseCore 1 52 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 52) owner_valid131
  scope290 binding3119_0 certificate290

theorem case_closed3120 : CoreExcluded (baseCore 1 52 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 52) owner_valid070
  scope291 binding3120_0 certificate291

theorem case_closed3121 : CoreExcluded (baseCore 1 52 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 52) owner_valid050
  scope292 binding3121_0 certificate292

theorem case_closed3122 : CoreExcluded (baseCore 1 52 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 52) owner_valid072
  scope559 binding3122_0 certificate685

theorem case_closed3123 : CoreExcluded (baseCore 1 52 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 1 52)
  (layout_for_all_rows 23 layout073 layout_valid073 1 52)
  owner_valid054 owner_valid073 scope728 scope729
  binding3123_0 binding3123_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate904 certificate905 (by decide)

theorem case_closed3124 : CoreExcluded (baseCore 1 52 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 52) owner_valid074
  scope295 binding3124_0 certificate295

theorem case_closed3125 : CoreExcluded (baseCore 1 53 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 53) owner_valid187
  scope267 binding3125_0 certificate267

theorem case_closed3126 : CoreExcluded (baseCore 1 53 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 53) owner_valid075
  scope268 binding3126_0 certificate268

theorem case_closed3127 : CoreExcluded (baseCore 1 53 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 53) owner_valid003
  scope269 binding3127_0 certificate269

theorem case_closed3128 : CoreExcluded (baseCore 1 53 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 53) owner_valid077
  scope270 binding3128_0 certificate270

theorem case_closed3129 : CoreExcluded (baseCore 1 53 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 53) owner_valid007
  scope271 binding3129_0 certificate271

theorem case_closed3130 : CoreExcluded (baseCore 1 53 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout108
  (layout_for_all_rows 5 layout108 layout_valid108 1 53) owner_valid108
  scope730 binding3130_0 certificate906

theorem case_closed3131 : CoreExcluded (baseCore 1 53 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout110
  (layout_for_all_rows 6 layout110 layout_valid110 1 53) owner_valid110
  scope731 binding3131_0 certificate907

theorem case_closed3132 : CoreExcluded (baseCore 1 53 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout113
  (layout_for_all_rows 7 layout113 layout_valid113 1 53) owner_valid113
  scope732 binding3132_0 certificate908

theorem case_closed3133 : CoreExcluded (baseCore 1 53 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout115
  (layout_for_all_rows 8 layout115 layout_valid115 1 53) owner_valid115
  scope733 binding3133_0 certificate909

theorem case_closed3134 : CoreExcluded (baseCore 1 53 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 1 53)
  (layout_for_all_rows 9 layout061 layout_valid061 1 53)
  owner_valid116 owner_valid061 scope276 scope351
  binding3134_0 binding3134_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate276 certificate756 (by decide)

theorem case_closed3135 : CoreExcluded (baseCore 1 53 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout039 layout063
  (layout_for_all_rows 10 layout039 layout_valid039 1 53)
  (layout_for_all_rows 10 layout063 layout_valid063 1 53)
  owner_valid039 owner_valid063 scope278 scope489
  binding3135_0 binding3135_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate278 certificate757 (by decide)

theorem case_closed3136 : CoreExcluded (baseCore 1 53 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout149 layout040
  (layout_for_all_rows 11 layout149 layout_valid149 1 53)
  (layout_for_all_rows 11 layout040 layout_valid040 1 53)
  owner_valid149 owner_valid040 scope280 scope281
  binding3136_0 binding3136_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate280 certificate281 (by decide)

theorem case_closed3137 : CoreExcluded (baseCore 1 53 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout042 layout119
  (layout_for_all_rows 12 layout042 layout_valid042 1 53)
  (layout_for_all_rows 12 layout119 layout_valid119 1 53)
  owner_valid042 owner_valid119 scope282 scope283
  binding3137_0 binding3137_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate282 certificate283 (by decide)

theorem case_closed3138 : CoreExcluded (baseCore 1 53 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 53) owner_valid137
  scope284 binding3138_0 certificate284

theorem case_closed3139 : CoreExcluded (baseCore 1 53 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout139
  (layout_for_all_rows 14 layout139 layout_valid139 1 53) owner_valid139
  scope285 binding3139_0 certificate285

theorem case_closed3140 : CoreExcluded (baseCore 1 53 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout150
  (layout_for_all_rows 15 layout150 layout_valid150 1 53) owner_valid150
  scope286 binding3140_0 certificate286

theorem case_closed3141 : CoreExcluded (baseCore 1 53 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 53) owner_valid180
  scope287 binding3141_0 certificate287

theorem case_closed3142 : CoreExcluded (baseCore 1 53 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 1 53) owner_valid129
  scope288 binding3142_0 certificate288

theorem case_closed3143 : CoreExcluded (baseCore 1 53 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 1 53) owner_valid130
  scope289 binding3143_0 certificate289

theorem case_closed3144 : CoreExcluded (baseCore 1 53 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 53) owner_valid131
  scope290 binding3144_0 certificate290

theorem case_closed3145 : CoreExcluded (baseCore 1 53 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 53) owner_valid070
  scope291 binding3145_0 certificate291

theorem case_closed3146 : CoreExcluded (baseCore 1 53 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 53) owner_valid050
  scope292 binding3146_0 certificate292

theorem case_closed3147 : CoreExcluded (baseCore 1 53 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout072 layout143
  (layout_for_all_rows 22 layout072 layout_valid072 1 53)
  (layout_for_all_rows 22 layout143 layout_valid143 1 53)
  owner_valid072 owner_valid143 scope206 scope205
  binding3147_0 binding3147_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate206 certificate205 (by decide)

theorem case_closed3148 : CoreExcluded (baseCore 1 53 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout073
  (layout_for_all_rows 23 layout073 layout_valid073 1 53) owner_valid073
  scope734 binding3148_0 certificate910

theorem case_closed3149 : CoreExcluded (baseCore 1 53 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 53) owner_valid074
  scope295 binding3149_0 certificate295

theorem case_closed3150 : CoreExcluded (baseCore 1 54 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 54) owner_valid033
  scope503 binding3150_0 certificate590

theorem case_closed3151 : CoreExcluded (baseCore 1 54 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 54) owner_valid002
  scope502 binding3151_0 certificate589

theorem case_closed3152 : CoreExcluded (baseCore 1 54 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 54) owner_valid034
  scope504 binding3152_0 certificate591

theorem case_closed3153 : CoreExcluded (baseCore 1 54 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 54) owner_valid035
  scope594 binding3153_0 certificate737

theorem case_closed3154 : CoreExcluded (baseCore 1 54 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 54) owner_valid036
  scope505 binding3154_0 certificate592

theorem case_closed3155 : CoreExcluded (baseCore 1 54 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 54) owner_valid009
  scope595 binding3155_0 certificate738

theorem case_closed3156 : CoreExcluded (baseCore 1 54 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 54) owner_valid010
  scope596 binding3156_0 certificate739

theorem case_closed3157 : CoreExcluded (baseCore 1 54 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 54) owner_valid059
  scope219 binding3157_0 certificate219

theorem case_closed3158 : CoreExcluded (baseCore 1 54 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 54) owner_valid134
  scope218 binding3158_0 certificate218

theorem case_closed3159 : CoreExcluded (baseCore 1 54 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 54) owner_valid038
  scope254 binding3159_0 certificate254

theorem case_closed3160 : CoreExcluded (baseCore 1 54 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 54) owner_valid039
  scope220 binding3160_0 certificate220

theorem case_closed3161 : CoreExcluded (baseCore 1 54 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 54) owner_valid149
  scope223 binding3161_0 certificate223

theorem case_closed3162 : CoreExcluded (baseCore 1 54 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 54) owner_valid018
  scope255 binding3162_0 certificate255

theorem case_closed3163 : CoreExcluded (baseCore 1 54 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 54) owner_valid137
  scope224 binding3163_0 certificate224

theorem case_closed3164 : CoreExcluded (baseCore 1 54 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 54) owner_valid138
  scope225 binding3164_0 certificate225

theorem case_closed3165 : CoreExcluded (baseCore 1 54 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 54) owner_valid064
  scope226 binding3165_0 certificate226

theorem case_closed3166 : CoreExcluded (baseCore 1 54 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 54) owner_valid022
  scope408 binding3166_0 certificate415

theorem case_closed3167 : CoreExcluded (baseCore 1 54 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 54) owner_valid023
  scope506 binding3167_0 certificate593

theorem case_closed3168 : CoreExcluded (baseCore 1 54 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 1 54) owner_valid130
  scope229 binding3168_0 certificate229

theorem case_closed3169 : CoreExcluded (baseCore 1 54 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 54) owner_valid131
  scope230 binding3169_0 certificate230

theorem case_closed3170 : CoreExcluded (baseCore 1 54 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 54) owner_valid070
  scope231 binding3170_0 certificate231

theorem case_closed3171 : CoreExcluded (baseCore 1 54 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 54) owner_valid050
  scope232 binding3171_0 certificate232

theorem case_closed3172 : CoreExcluded (baseCore 1 54 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 54) owner_valid052
  scope233 binding3172_0 certificate233

theorem case_closed3173 : CoreExcluded (baseCore 1 54 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 54) owner_valid031
  scope597 binding3173_0 certificate740

theorem case_closed3174 : CoreExcluded (baseCore 1 54 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 54) owner_valid032
  scope598 binding3174_0 certificate741

theorem case_closed3175 : CoreExcluded (baseCore 1 55 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 55) owner_valid033
  scope546 binding3175_0 certificate670

theorem case_closed3176 : CoreExcluded (baseCore 1 55 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 55) owner_valid002
  scope545 binding3176_0 certificate669

theorem case_closed3177 : CoreExcluded (baseCore 1 55 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 55) owner_valid034
  scope547 binding3177_0 certificate671

theorem case_closed3178 : CoreExcluded (baseCore 1 55 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 55) owner_valid035
  scope548 binding3178_0 certificate672

theorem case_closed3179 : CoreExcluded (baseCore 1 55 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 55) owner_valid036
  scope621 binding3179_0 certificate766

theorem case_closed3180 : CoreExcluded (baseCore 1 55 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout145
  (layout_for_all_rows 5 layout145 layout_valid145 1 55) owner_valid145
  scope644 binding3180_0 certificate791

theorem case_closed3181 : CoreExcluded (baseCore 1 55 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout177
  (layout_for_all_rows 6 layout177 layout_valid177 1 55) owner_valid177
  scope645 binding3181_0 certificate792

theorem case_closed3182 : CoreExcluded (baseCore 1 55 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 1 55) owner_valid133
  scope519 binding3182_0 certificate622

theorem case_closed3183 : CoreExcluded (baseCore 1 55 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout135
  (layout_for_all_rows 8 layout135 layout_valid135 1 55) owner_valid135
  scope520 binding3183_0 certificate623

theorem case_closed3184 : CoreExcluded (baseCore 1 55 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout116
  (layout_for_all_rows 9 layout116 layout_valid116 1 55) owner_valid116
  scope648 binding3184_0 certificate795

theorem case_closed3185 : CoreExcluded (baseCore 1 55 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout117
  (layout_for_all_rows 10 layout117 layout_valid117 1 55) owner_valid117
  scope649 binding3185_0 certificate796

theorem case_closed3186 : CoreExcluded (baseCore 1 55 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout149 layout040
  (layout_for_all_rows 11 layout149 layout_valid149 1 55)
  (layout_for_all_rows 11 layout040 layout_valid040 1 55)
  owner_valid149 owner_valid040 scope280 scope421
  binding3186_0 binding3186_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate280 certificate602 (by decide)

theorem case_closed3187 : CoreExcluded (baseCore 1 55 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout188
  (layout_for_all_rows 12 layout188 layout_valid188 1 55) owner_valid188
  scope353 binding3187_0 certificate354

theorem case_closed3188 : CoreExcluded (baseCore 1 55 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 55) owner_valid019
  scope549 binding3188_0 certificate673

theorem case_closed3189 : CoreExcluded (baseCore 1 55 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout162 layout163
  (layout_for_all_rows 14 layout162 layout_valid162 1 55)
  (layout_for_all_rows 14 layout163 layout_valid163 1 55)
  owner_valid162 owner_valid163 scope317 scope318
  binding3189_0 binding3189_1
  0 6 6 2 (by decide) (by decide) 3 2 (by decide)
  certificate317 certificate318 (by decide)

theorem case_closed3190 : CoreExcluded (baseCore 1 55 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 55) owner_valid021
  scope624 binding3190_0 certificate770

theorem case_closed3191 : CoreExcluded (baseCore 1 55 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 55) owner_valid022
  scope625 binding3191_0 certificate771

theorem case_closed3192 : CoreExcluded (baseCore 1 55 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 1 55) owner_valid129
  scope288 binding3192_0 certificate288

theorem case_closed3193 : CoreExcluded (baseCore 1 55 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 55) owner_valid024
  scope527 binding3193_0 certificate633

theorem case_closed3194 : CoreExcluded (baseCore 1 55 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 55) owner_valid025
  scope626 binding3194_0 certificate772

theorem case_closed3195 : CoreExcluded (baseCore 1 55 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 55) owner_valid070
  scope291 binding3195_0 certificate291

theorem case_closed3196 : CoreExcluded (baseCore 1 55 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 55) owner_valid087
  scope627 binding3196_0 certificate773

theorem case_closed3197 : CoreExcluded (baseCore 1 55 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 55) owner_valid072
  scope628 binding3197_0 certificate774

theorem case_closed3198 : CoreExcluded (baseCore 1 55 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 55) owner_valid031
  scope629 binding3198_0 certificate775

theorem case_closed3199 : CoreExcluded (baseCore 1 55 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 55) owner_valid074
  scope295 binding3199_0 certificate295

theorem block_closed031 (i : Fin 100) : CoreExcluded (caseCore (blockCase 31 i)) := by
 fin_cases i
 · exact case_closed3100
 · exact case_closed3101
 · exact case_closed3102
 · exact case_closed3103
 · exact case_closed3104
 · exact case_closed3105
 · exact case_closed3106
 · exact case_closed3107
 · exact case_closed3108
 · exact case_closed3109
 · exact case_closed3110
 · exact case_closed3111
 · exact case_closed3112
 · exact case_closed3113
 · exact case_closed3114
 · exact case_closed3115
 · exact case_closed3116
 · exact case_closed3117
 · exact case_closed3118
 · exact case_closed3119
 · exact case_closed3120
 · exact case_closed3121
 · exact case_closed3122
 · exact case_closed3123
 · exact case_closed3124
 · exact case_closed3125
 · exact case_closed3126
 · exact case_closed3127
 · exact case_closed3128
 · exact case_closed3129
 · exact case_closed3130
 · exact case_closed3131
 · exact case_closed3132
 · exact case_closed3133
 · exact case_closed3134
 · exact case_closed3135
 · exact case_closed3136
 · exact case_closed3137
 · exact case_closed3138
 · exact case_closed3139
 · exact case_closed3140
 · exact case_closed3141
 · exact case_closed3142
 · exact case_closed3143
 · exact case_closed3144
 · exact case_closed3145
 · exact case_closed3146
 · exact case_closed3147
 · exact case_closed3148
 · exact case_closed3149
 · exact case_closed3150
 · exact case_closed3151
 · exact case_closed3152
 · exact case_closed3153
 · exact case_closed3154
 · exact case_closed3155
 · exact case_closed3156
 · exact case_closed3157
 · exact case_closed3158
 · exact case_closed3159
 · exact case_closed3160
 · exact case_closed3161
 · exact case_closed3162
 · exact case_closed3163
 · exact case_closed3164
 · exact case_closed3165
 · exact case_closed3166
 · exact case_closed3167
 · exact case_closed3168
 · exact case_closed3169
 · exact case_closed3170
 · exact case_closed3171
 · exact case_closed3172
 · exact case_closed3173
 · exact case_closed3174
 · exact case_closed3175
 · exact case_closed3176
 · exact case_closed3177
 · exact case_closed3178
 · exact case_closed3179
 · exact case_closed3180
 · exact case_closed3181
 · exact case_closed3182
 · exact case_closed3183
 · exact case_closed3184
 · exact case_closed3185
 · exact case_closed3186
 · exact case_closed3187
 · exact case_closed3188
 · exact case_closed3189
 · exact case_closed3190
 · exact case_closed3191
 · exact case_closed3192
 · exact case_closed3193
 · exact case_closed3194
 · exact case_closed3195
 · exact case_closed3196
 · exact case_closed3197
 · exact case_closed3198
 · exact case_closed3199
end PricingC.GIsomorphic