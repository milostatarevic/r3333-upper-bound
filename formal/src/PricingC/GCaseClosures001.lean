import PricingC.GCoreExcluded
import PricingC.GBindings001
import PricingC.GScopeChecks008
import PricingC.GScopeChecks009
import PricingC.GScopeChecks010
import PricingC.GScopeChecks011
import PricingC.GScopeChecks012
import PricingC.GScopeChecks013
import PricingC.GScopeChecks014
import PricingC.GScopeChecks015
import PricingC.GScopeChecks016
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed0100 : CoreExcluded (baseCore 0 4 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout001 layout088
  (layout_for_all_rows 0 layout001 layout_valid001 0 4)
  (layout_for_all_rows 0 layout088 layout_valid088 0 4)
  owner_valid001 owner_valid088 scope128 scope129
  binding0100_0 binding0100_1
  0 9 0 9 (by decide) (by decide) 3 2 (by decide)
  certificate128 certificate129 (by decide)

theorem case_closed0101 : CoreExcluded (baseCore 0 4 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout076 layout089
  (layout_for_all_rows 1 layout076 layout_valid076 0 4)
  (layout_for_all_rows 1 layout089 layout_valid089 0 4)
  owner_valid076 owner_valid089 scope130 scope131
  binding0101_0 binding0101_1
  0 9 0 9 (by decide) (by decide) 2 3 (by decide)
  certificate130 certificate131 (by decide)

theorem case_closed0102 : CoreExcluded (baseCore 0 4 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 4) owner_valid034
  scope132 binding0102_0 certificate132

theorem case_closed0103 : CoreExcluded (baseCore 0 4 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout006
  (layout_for_all_rows 3 layout077 layout_valid077 0 4)
  (layout_for_all_rows 3 layout006 layout_valid006 0 4)
  owner_valid077 owner_valid006 scope133 scope134
  binding0103_0 binding0103_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate133 certificate134 (by decide)

theorem case_closed0104 : CoreExcluded (baseCore 0 4 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout078
  (layout_for_all_rows 4 layout007 layout_valid007 0 4)
  (layout_for_all_rows 4 layout078 layout_valid078 0 4)
  owner_valid007 owner_valid078 scope135 scope136
  binding0104_0 binding0104_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate135 certificate136 (by decide)

theorem case_closed0105 : CoreExcluded (baseCore 0 4 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout090 layout091
  (layout_for_all_rows 5 layout090 layout_valid090 0 4)
  (layout_for_all_rows 5 layout091 layout_valid091 0 4)
  owner_valid090 owner_valid091 scope137 scope138
  binding0105_0 binding0105_1
  0 8 6 3 (by decide) (by decide) 2 3 (by decide)
  certificate137 certificate138 (by decide)

theorem case_closed0106 : CoreExcluded (baseCore 0 4 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout092 layout093
  (layout_for_all_rows 6 layout092 layout_valid092 0 4)
  (layout_for_all_rows 6 layout093 layout_valid093 0 4)
  owner_valid092 owner_valid093 scope139 scope140
  binding0106_0 binding0106_1
  0 9 6 4 (by decide) (by decide) 2 3 (by decide)
  certificate139 certificate140 (by decide)

theorem case_closed0107 : CoreExcluded (baseCore 0 4 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 4) owner_valid011
  scope141 binding0107_0 certificate141

theorem case_closed0108 : CoreExcluded (baseCore 0 4 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 4) owner_valid012
  scope142 binding0108_0 certificate142

theorem case_closed0109 : CoreExcluded (baseCore 0 4 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 4) owner_valid038
  scope143 binding0109_0 certificate143

theorem case_closed0110 : CoreExcluded (baseCore 0 4 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 4) owner_valid079
  scope144 binding0110_0 certificate144

theorem case_closed0111 : CoreExcluded (baseCore 0 4 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 4) owner_valid017
  scope145 binding0111_0 certificate145

theorem case_closed0112 : CoreExcluded (baseCore 0 4 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 4) owner_valid018
  scope146 binding0112_0 certificate146

theorem case_closed0113 : CoreExcluded (baseCore 0 4 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 4) owner_valid019
  scope147 binding0113_0 certificate147

theorem case_closed0114 : CoreExcluded (baseCore 0 4 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 4) owner_valid020
  scope148 binding0114_0 certificate148

theorem case_closed0115 : CoreExcluded (baseCore 0 4 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 4) owner_valid021
  scope149 binding0115_0 certificate149

theorem case_closed0116 : CoreExcluded (baseCore 0 4 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 4) owner_valid022
  scope150 binding0116_0 certificate150

theorem case_closed0117 : CoreExcluded (baseCore 0 4 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 4) owner_valid023
  scope151 binding0117_0 certificate151

theorem case_closed0118 : CoreExcluded (baseCore 0 4 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 4) owner_valid024
  scope152 binding0118_0 certificate152

theorem case_closed0119 : CoreExcluded (baseCore 0 4 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 4) owner_valid025
  scope153 binding0119_0 certificate153

theorem case_closed0120 : CoreExcluded (baseCore 0 4 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 4) owner_valid026
  scope154 binding0120_0 certificate154

theorem case_closed0121 : CoreExcluded (baseCore 0 4 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 4) owner_valid087
  scope155 binding0121_0 certificate155

theorem case_closed0122 : CoreExcluded (baseCore 0 4 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 4) owner_valid072
  scope156 binding0122_0 certificate156

theorem case_closed0123 : CoreExcluded (baseCore 0 4 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout094 layout095
  (layout_for_all_rows 23 layout094 layout_valid094 0 4)
  (layout_for_all_rows 23 layout095 layout_valid095 0 4)
  owner_valid094 owner_valid095 scope157 scope158
  binding0123_0 binding0123_1
  2 6 6 1 (by decide) (by decide) 3 2 (by decide)
  certificate157 certificate158 (by decide)

theorem case_closed0124 : CoreExcluded (baseCore 0 4 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout096 layout097
  (layout_for_all_rows 24 layout096 layout_valid096 0 4)
  (layout_for_all_rows 24 layout097 layout_valid097 0 4)
  owner_valid096 owner_valid097 scope159 scope160
  binding0124_0 binding0124_1
  2 5 6 0 (by decide) (by decide) 3 2 (by decide)
  certificate159 certificate160 (by decide)

theorem case_closed0125 : CoreExcluded (baseCore 0 5 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout098 layout099
  (layout_for_all_rows 0 layout098 layout_valid098 0 5)
  (layout_for_all_rows 0 layout099 layout_valid099 0 5)
  owner_valid098 owner_valid099 scope161 scope162
  binding0125_0 binding0125_1
  0 9 6 4 (by decide) (by decide) 2 3 (by decide)
  certificate161 certificate162 (by decide)

theorem case_closed0126 : CoreExcluded (baseCore 0 5 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout100 layout101
  (layout_for_all_rows 1 layout100 layout_valid100 0 5)
  (layout_for_all_rows 1 layout101 layout_valid101 0 5)
  owner_valid100 owner_valid101 scope163 scope164
  binding0126_0 binding0126_1
  0 8 6 3 (by decide) (by decide) 2 3 (by decide)
  certificate163 certificate164 (by decide)

theorem case_closed0127 : CoreExcluded (baseCore 0 5 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout102 layout103
  (layout_for_all_rows 2 layout102 layout_valid102 0 5)
  (layout_for_all_rows 2 layout103 layout_valid103 0 5)
  owner_valid102 owner_valid103 scope165 scope166
  binding0127_0 binding0127_1
  1 5 6 1 (by decide) (by decide) 3 2 (by decide)
  certificate165 certificate166 (by decide)

theorem case_closed0128 : CoreExcluded (baseCore 0 5 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout104 layout105
  (layout_for_all_rows 3 layout104 layout_valid104 0 5)
  (layout_for_all_rows 3 layout105 layout_valid105 0 5)
  owner_valid104 owner_valid105 scope167 scope168
  binding0128_0 binding0128_1
  2 5 6 0 (by decide) (by decide) 3 2 (by decide)
  certificate167 certificate168 (by decide)

theorem case_closed0129 : CoreExcluded (baseCore 0 5 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout106 layout107
  (layout_for_all_rows 4 layout106 layout_valid106 0 5)
  (layout_for_all_rows 4 layout107 layout_valid107 0 5)
  owner_valid106 owner_valid107 scope169 scope170
  binding0129_0 binding0129_1
  2 6 6 1 (by decide) (by decide) 3 2 (by decide)
  certificate169 certificate170 (by decide)

theorem case_closed0130 : CoreExcluded (baseCore 0 5 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout108 layout109
  (layout_for_all_rows 5 layout108 layout_valid108 0 5)
  (layout_for_all_rows 5 layout109 layout_valid109 0 5)
  owner_valid108 owner_valid109 scope171 scope172
  binding0130_0 binding0130_1
  0 9 0 9 (by decide) (by decide) 2 3 (by decide)
  certificate171 certificate172 (by decide)

theorem case_closed0131 : CoreExcluded (baseCore 0 5 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout110 layout111
  (layout_for_all_rows 6 layout110 layout_valid110 0 5)
  (layout_for_all_rows 6 layout111 layout_valid111 0 5)
  owner_valid110 owner_valid111 scope173 scope174
  binding0131_0 binding0131_1
  0 9 0 9 (by decide) (by decide) 3 2 (by decide)
  certificate173 certificate174 (by decide)

theorem case_closed0132 : CoreExcluded (baseCore 0 5 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout112 layout113
  (layout_for_all_rows 7 layout112 layout_valid112 0 5)
  (layout_for_all_rows 7 layout113 layout_valid113 0 5)
  owner_valid112 owner_valid113 scope175 scope176
  binding0132_0 binding0132_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate175 certificate176 (by decide)

theorem case_closed0133 : CoreExcluded (baseCore 0 5 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout114 layout115
  (layout_for_all_rows 8 layout114 layout_valid114 0 5)
  (layout_for_all_rows 8 layout115 layout_valid115 0 5)
  owner_valid114 owner_valid115 scope177 scope178
  binding0133_0 binding0133_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate177 certificate178 (by decide)

theorem case_closed0134 : CoreExcluded (baseCore 0 5 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 0 5)
  (layout_for_all_rows 9 layout061 layout_valid061 0 5)
  owner_valid116 owner_valid061 scope179 scope180
  binding0134_0 binding0134_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate179 certificate180 (by decide)

theorem case_closed0135 : CoreExcluded (baseCore 0 5 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout117 layout063
  (layout_for_all_rows 10 layout117 layout_valid117 0 5)
  (layout_for_all_rows 10 layout063 layout_valid063 0 5)
  owner_valid117 owner_valid063 scope181 scope182
  binding0135_0 binding0135_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate181 certificate182 (by decide)

theorem case_closed0136 : CoreExcluded (baseCore 0 5 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout040 layout118
  (layout_for_all_rows 11 layout040 layout_valid040 0 5)
  (layout_for_all_rows 11 layout118 layout_valid118 0 5)
  owner_valid040 owner_valid118 scope183 scope184
  binding0136_0 binding0136_1
  0 8 0 8 (by decide) (by decide) 2 3 (by decide)
  certificate183 certificate184 (by decide)

theorem case_closed0137 : CoreExcluded (baseCore 0 5 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout119 layout120
  (layout_for_all_rows 12 layout119 layout_valid119 0 5)
  (layout_for_all_rows 12 layout120 layout_valid120 0 5)
  owner_valid119 owner_valid120 scope185 scope186
  binding0137_0 binding0137_1
  0 8 0 8 (by decide) (by decide) 3 2 (by decide)
  certificate185 certificate186 (by decide)

theorem case_closed0138 : CoreExcluded (baseCore 0 5 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout121 layout122
  (layout_for_all_rows 13 layout121 layout_valid121 0 5)
  (layout_for_all_rows 13 layout122 layout_valid122 0 5)
  owner_valid121 owner_valid122 scope187 scope188
  binding0138_0 binding0138_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate187 certificate188 (by decide)

theorem case_closed0139 : CoreExcluded (baseCore 0 5 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout123 layout124
  (layout_for_all_rows 14 layout123 layout_valid123 0 5)
  (layout_for_all_rows 14 layout124 layout_valid124 0 5)
  owner_valid123 owner_valid124 scope189 scope190
  binding0139_0 binding0139_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate189 certificate190 (by decide)

theorem case_closed0140 : CoreExcluded (baseCore 0 5 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout125 layout126
  (layout_for_all_rows 15 layout125 layout_valid125 0 5)
  (layout_for_all_rows 15 layout126 layout_valid126 0 5)
  owner_valid125 owner_valid126 scope191 scope192
  binding0140_0 binding0140_1
  2 8 1 7 (by decide) (by decide) 3 2 (by decide)
  certificate191 certificate192 (by decide)

theorem case_closed0141 : CoreExcluded (baseCore 0 5 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout127 layout128
  (layout_for_all_rows 16 layout127 layout_valid127 0 5)
  (layout_for_all_rows 16 layout128 layout_valid128 0 5)
  owner_valid127 owner_valid128 scope193 scope194
  binding0141_0 binding0141_1
  2 8 1 7 (by decide) (by decide) 2 3 (by decide)
  certificate193 certificate194 (by decide)

theorem case_closed0142 : CoreExcluded (baseCore 0 5 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 0 5)
  (layout_for_all_rows 17 layout046 layout_valid046 0 5)
  owner_valid129 owner_valid046 scope195 scope196
  binding0142_0 binding0142_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate195 certificate196 (by decide)

theorem case_closed0143 : CoreExcluded (baseCore 0 5 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout130 layout048
  (layout_for_all_rows 18 layout130 layout_valid130 0 5)
  (layout_for_all_rows 18 layout048 layout_valid048 0 5)
  owner_valid130 owner_valid048 scope197 scope198
  binding0143_0 binding0143_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate197 certificate198 (by decide)

theorem case_closed0144 : CoreExcluded (baseCore 0 5 19) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout131 layout069
  (layout_for_all_rows 19 layout131 layout_valid131 0 5)
  (layout_for_all_rows 19 layout069 layout_valid069 0 5)
  owner_valid131 owner_valid069 scope199 scope200
  binding0144_0 binding0144_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate199 certificate200 (by decide)

theorem case_closed0145 : CoreExcluded (baseCore 0 5 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout070 layout071
  (layout_for_all_rows 20 layout070 layout_valid070 0 5)
  (layout_for_all_rows 20 layout071 layout_valid071 0 5)
  owner_valid070 owner_valid071 scope201 scope202
  binding0145_0 binding0145_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate201 certificate202 (by decide)

theorem case_closed0146 : CoreExcluded (baseCore 0 5 21) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout050 layout132
  (layout_for_all_rows 21 layout050 layout_valid050 0 5)
  (layout_for_all_rows 21 layout132 layout_valid132 0 5)
  owner_valid050 owner_valid132 scope203 scope204
  binding0146_0 binding0146_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate203 certificate204 (by decide)

theorem case_closed0147 : CoreExcluded (baseCore 0 5 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout052 layout053
  (layout_for_all_rows 22 layout052 layout_valid052 0 5)
  (layout_for_all_rows 22 layout053 layout_valid053 0 5)
  owner_valid052 owner_valid053 scope205 scope206
  binding0147_0 binding0147_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate205 certificate206 (by decide)

theorem case_closed0148 : CoreExcluded (baseCore 0 5 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 0 5)
  (layout_for_all_rows 23 layout073 layout_valid073 0 5)
  owner_valid054 owner_valid073 scope207 scope208
  binding0148_0 binding0148_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate207 certificate208 (by decide)

theorem case_closed0149 : CoreExcluded (baseCore 0 5 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout074 layout057
  (layout_for_all_rows 24 layout074 layout_valid074 0 5)
  (layout_for_all_rows 24 layout057 layout_valid057 0 5)
  owner_valid074 owner_valid057 scope209 scope210
  binding0149_0 binding0149_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate209 certificate210 (by decide)

theorem case_closed0150 : CoreExcluded (baseCore 0 6 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 6) owner_valid033
  scope211 binding0150_0 certificate211

theorem case_closed0151 : CoreExcluded (baseCore 0 6 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 6) owner_valid002
  scope212 binding0151_0 certificate212

theorem case_closed0152 : CoreExcluded (baseCore 0 6 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 6) owner_valid034
  scope213 binding0152_0 certificate213

theorem case_closed0153 : CoreExcluded (baseCore 0 6 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 6) owner_valid035
  scope214 binding0153_0 certificate214

theorem case_closed0154 : CoreExcluded (baseCore 0 6 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 6) owner_valid036
  scope215 binding0154_0 certificate215

theorem case_closed0155 : CoreExcluded (baseCore 0 6 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 6) owner_valid009
  scope216 binding0155_0 certificate216

theorem case_closed0156 : CoreExcluded (baseCore 0 6 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 6) owner_valid010
  scope217 binding0156_0 certificate217

theorem case_closed0157 : CoreExcluded (baseCore 0 6 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 6) owner_valid011
  scope218 binding0157_0 certificate218

theorem case_closed0158 : CoreExcluded (baseCore 0 6 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 6) owner_valid012
  scope219 binding0158_0 certificate219

theorem case_closed0159 : CoreExcluded (baseCore 0 6 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 6) owner_valid038
  scope220 binding0159_0 certificate220

theorem case_closed0160 : CoreExcluded (baseCore 0 6 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 6) owner_valid079
  scope221 binding0160_0 certificate221

theorem case_closed0161 : CoreExcluded (baseCore 0 6 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 6) owner_valid017
  scope222 binding0161_0 certificate222

theorem case_closed0162 : CoreExcluded (baseCore 0 6 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 6) owner_valid018
  scope223 binding0162_0 certificate223

theorem case_closed0163 : CoreExcluded (baseCore 0 6 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 6) owner_valid019
  scope224 binding0163_0 certificate224

theorem case_closed0164 : CoreExcluded (baseCore 0 6 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 6) owner_valid020
  scope225 binding0164_0 certificate225

theorem case_closed0165 : CoreExcluded (baseCore 0 6 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 6) owner_valid021
  scope226 binding0165_0 certificate226

theorem case_closed0166 : CoreExcluded (baseCore 0 6 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 6) owner_valid022
  scope227 binding0166_0 certificate227

theorem case_closed0167 : CoreExcluded (baseCore 0 6 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 6) owner_valid023
  scope228 binding0167_0 certificate228

theorem case_closed0168 : CoreExcluded (baseCore 0 6 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 6) owner_valid024
  scope229 binding0168_0 certificate229

theorem case_closed0169 : CoreExcluded (baseCore 0 6 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 6) owner_valid025
  scope230 binding0169_0 certificate230

theorem case_closed0170 : CoreExcluded (baseCore 0 6 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 6) owner_valid026
  scope231 binding0170_0 certificate231

theorem case_closed0171 : CoreExcluded (baseCore 0 6 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 6) owner_valid087
  scope232 binding0171_0 certificate232

theorem case_closed0172 : CoreExcluded (baseCore 0 6 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 6) owner_valid072
  scope233 binding0172_0 certificate233

theorem case_closed0173 : CoreExcluded (baseCore 0 6 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 6) owner_valid031
  scope234 binding0173_0 certificate234

theorem case_closed0174 : CoreExcluded (baseCore 0 6 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 6) owner_valid032
  scope235 binding0174_0 certificate235

theorem case_closed0175 : CoreExcluded (baseCore 0 7 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 7) owner_valid033
  scope236 binding0175_0 certificate236

theorem case_closed0176 : CoreExcluded (baseCore 0 7 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 7) owner_valid002
  scope237 binding0176_0 certificate237

theorem case_closed0177 : CoreExcluded (baseCore 0 7 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 7) owner_valid034
  scope238 binding0177_0 certificate238

theorem case_closed0178 : CoreExcluded (baseCore 0 7 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 7) owner_valid035
  scope239 binding0178_0 certificate239

theorem case_closed0179 : CoreExcluded (baseCore 0 7 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 7) owner_valid036
  scope240 binding0179_0 certificate240

theorem case_closed0180 : CoreExcluded (baseCore 0 7 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 7) owner_valid009
  scope241 binding0180_0 certificate241

theorem case_closed0181 : CoreExcluded (baseCore 0 7 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 7) owner_valid010
  scope242 binding0181_0 certificate242

theorem case_closed0182 : CoreExcluded (baseCore 0 7 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout059 layout133
  (layout_for_all_rows 7 layout059 layout_valid059 0 7)
  (layout_for_all_rows 7 layout133 layout_valid133 0 7)
  owner_valid059 owner_valid133 scope243 scope244
  binding0182_0 binding0182_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate243 certificate244 (by decide)

theorem case_closed0183 : CoreExcluded (baseCore 0 7 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout134 layout135
  (layout_for_all_rows 8 layout134 layout_valid134 0 7)
  (layout_for_all_rows 8 layout135 layout_valid135 0 7)
  owner_valid134 owner_valid135 scope245 scope246
  binding0183_0 binding0183_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate245 certificate246 (by decide)

theorem case_closed0184 : CoreExcluded (baseCore 0 7 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 7) owner_valid136
  scope247 binding0184_0 certificate247

theorem case_closed0185 : CoreExcluded (baseCore 0 7 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 7) owner_valid079
  scope247 binding0185_0 certificate247

theorem case_closed0186 : CoreExcluded (baseCore 0 7 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 7) owner_valid017
  scope248 binding0186_0 certificate248

theorem case_closed0187 : CoreExcluded (baseCore 0 7 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 7) owner_valid042
  scope248 binding0187_0 certificate248

theorem case_closed0188 : CoreExcluded (baseCore 0 7 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout137 layout044
  (layout_for_all_rows 13 layout137 layout_valid137 0 7)
  (layout_for_all_rows 13 layout044 layout_valid044 0 7)
  owner_valid137 owner_valid044 scope249 scope250
  binding0188_0 binding0188_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate249 certificate250 (by decide)

theorem case_closed0189 : CoreExcluded (baseCore 0 7 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout138 layout139
  (layout_for_all_rows 14 layout138 layout_valid138 0 7)
  (layout_for_all_rows 14 layout139 layout_valid139 0 7)
  owner_valid138 owner_valid139 scope251 scope252
  binding0189_0 binding0189_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate251 certificate252 (by decide)

theorem case_closed0190 : CoreExcluded (baseCore 0 7 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 7) owner_valid021
  scope253 binding0190_0 certificate253

theorem case_closed0191 : CoreExcluded (baseCore 0 7 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout066
  (layout_for_all_rows 16 layout066 layout_valid066 0 7) owner_valid066
  scope254 binding0191_0 certificate254

theorem case_closed0192 : CoreExcluded (baseCore 0 7 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout140
  (layout_for_all_rows 17 layout140 layout_valid140 0 7) owner_valid140
  scope255 binding0192_0 certificate255

theorem case_closed0193 : CoreExcluded (baseCore 0 7 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 7) owner_valid024
  scope256 binding0193_0 certificate256

theorem case_closed0194 : CoreExcluded (baseCore 0 7 19) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout083 layout049
  (layout_for_all_rows 19 layout083 layout_valid083 0 7)
  (layout_for_all_rows 19 layout049 layout_valid049 0 7)
  owner_valid083 owner_valid049 scope257 scope258
  binding0194_0 binding0194_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate257 certificate258 (by decide)

theorem case_closed0195 : CoreExcluded (baseCore 0 7 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout141 layout142
  (layout_for_all_rows 20 layout141 layout_valid141 0 7)
  (layout_for_all_rows 20 layout142 layout_valid142 0 7)
  owner_valid141 owner_valid142 scope259 scope260
  binding0195_0 binding0195_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate259 certificate260 (by decide)

theorem case_closed0196 : CoreExcluded (baseCore 0 7 21) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout027 layout051
  (layout_for_all_rows 21 layout027 layout_valid027 0 7)
  (layout_for_all_rows 21 layout051 layout_valid051 0 7)
  owner_valid027 owner_valid051 scope261 scope262
  binding0196_0 binding0196_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate261 certificate262 (by decide)

theorem case_closed0197 : CoreExcluded (baseCore 0 7 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout143 layout144
  (layout_for_all_rows 22 layout143 layout_valid143 0 7)
  (layout_for_all_rows 22 layout144 layout_valid144 0 7)
  owner_valid143 owner_valid144 scope263 scope264
  binding0197_0 binding0197_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate263 certificate264 (by decide)

theorem case_closed0198 : CoreExcluded (baseCore 0 7 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 7) owner_valid031
  scope265 binding0198_0 certificate265

theorem case_closed0199 : CoreExcluded (baseCore 0 7 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 7) owner_valid032
  scope266 binding0199_0 certificate266

theorem block_closed001 (i : Fin 100) : CoreExcluded (caseCore (blockCase 1 i)) := by
 fin_cases i
 · exact case_closed0100
 · exact case_closed0101
 · exact case_closed0102
 · exact case_closed0103
 · exact case_closed0104
 · exact case_closed0105
 · exact case_closed0106
 · exact case_closed0107
 · exact case_closed0108
 · exact case_closed0109
 · exact case_closed0110
 · exact case_closed0111
 · exact case_closed0112
 · exact case_closed0113
 · exact case_closed0114
 · exact case_closed0115
 · exact case_closed0116
 · exact case_closed0117
 · exact case_closed0118
 · exact case_closed0119
 · exact case_closed0120
 · exact case_closed0121
 · exact case_closed0122
 · exact case_closed0123
 · exact case_closed0124
 · exact case_closed0125
 · exact case_closed0126
 · exact case_closed0127
 · exact case_closed0128
 · exact case_closed0129
 · exact case_closed0130
 · exact case_closed0131
 · exact case_closed0132
 · exact case_closed0133
 · exact case_closed0134
 · exact case_closed0135
 · exact case_closed0136
 · exact case_closed0137
 · exact case_closed0138
 · exact case_closed0139
 · exact case_closed0140
 · exact case_closed0141
 · exact case_closed0142
 · exact case_closed0143
 · exact case_closed0144
 · exact case_closed0145
 · exact case_closed0146
 · exact case_closed0147
 · exact case_closed0148
 · exact case_closed0149
 · exact case_closed0150
 · exact case_closed0151
 · exact case_closed0152
 · exact case_closed0153
 · exact case_closed0154
 · exact case_closed0155
 · exact case_closed0156
 · exact case_closed0157
 · exact case_closed0158
 · exact case_closed0159
 · exact case_closed0160
 · exact case_closed0161
 · exact case_closed0162
 · exact case_closed0163
 · exact case_closed0164
 · exact case_closed0165
 · exact case_closed0166
 · exact case_closed0167
 · exact case_closed0168
 · exact case_closed0169
 · exact case_closed0170
 · exact case_closed0171
 · exact case_closed0172
 · exact case_closed0173
 · exact case_closed0174
 · exact case_closed0175
 · exact case_closed0176
 · exact case_closed0177
 · exact case_closed0178
 · exact case_closed0179
 · exact case_closed0180
 · exact case_closed0181
 · exact case_closed0182
 · exact case_closed0183
 · exact case_closed0184
 · exact case_closed0185
 · exact case_closed0186
 · exact case_closed0187
 · exact case_closed0188
 · exact case_closed0189
 · exact case_closed0190
 · exact case_closed0191
 · exact case_closed0192
 · exact case_closed0193
 · exact case_closed0194
 · exact case_closed0195
 · exact case_closed0196
 · exact case_closed0197
 · exact case_closed0198
 · exact case_closed0199
end PricingC.GIsomorphic