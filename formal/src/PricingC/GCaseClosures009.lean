import PricingC.GCoreExcluded
import PricingC.GBindings009
import PricingC.GScopeChecks000
import PricingC.GScopeChecks001
import PricingC.GScopeChecks002
import PricingC.GScopeChecks005
import PricingC.GScopeChecks006
import PricingC.GScopeChecks007
import PricingC.GScopeChecks008
import PricingC.GScopeChecks009
import PricingC.GScopeChecks010
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GScopeChecks032
import PricingC.GScopeChecks033
import PricingC.GScopeChecks034
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks006

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed0900 : CoreExcluded (baseCore 0 36 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 36) owner_valid033
  scope361 binding0900_0 certificate362

theorem case_closed0901 : CoreExcluded (baseCore 0 36 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 36) owner_valid002
  scope362 binding0901_0 certificate363

theorem case_closed0902 : CoreExcluded (baseCore 0 36 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 36) owner_valid034
  scope363 binding0902_0 certificate364

theorem case_closed0903 : CoreExcluded (baseCore 0 36 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 36) owner_valid035
  scope364 binding0903_0 certificate365

theorem case_closed0904 : CoreExcluded (baseCore 0 36 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 36) owner_valid036
  scope365 binding0904_0 certificate366

theorem case_closed0905 : CoreExcluded (baseCore 0 36 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout176 layout108
  (layout_for_all_rows 5 layout176 layout_valid176 0 36)
  (layout_for_all_rows 5 layout108 layout_valid108 0 36)
  owner_valid176 owner_valid108 scope366 scope478
  binding0905_0 binding0905_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate367 certificate516 (by decide)

theorem case_closed0906 : CoreExcluded (baseCore 0 36 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout177 layout178
  (layout_for_all_rows 6 layout177 layout_valid177 0 36)
  (layout_for_all_rows 6 layout178 layout_valid178 0 36)
  owner_valid177 owner_valid178 scope479 scope367
  binding0906_0 binding0906_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate517 certificate518 (by decide)

theorem case_closed0907 : CoreExcluded (baseCore 0 36 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 36) owner_valid011
  scope368 binding0907_0 certificate369

theorem case_closed0908 : CoreExcluded (baseCore 0 36 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 0 36) owner_valid134
  scope141 binding0908_0 certificate141

theorem case_closed0909 : CoreExcluded (baseCore 0 36 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 36) owner_valid038
  scope369 binding0909_0 certificate370

theorem case_closed0910 : CoreExcluded (baseCore 0 36 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 36) owner_valid079
  scope370 binding0910_0 certificate371

theorem case_closed0911 : CoreExcluded (baseCore 0 36 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 36) owner_valid149
  scope146 binding0911_0 certificate146

theorem case_closed0912 : CoreExcluded (baseCore 0 36 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 36) owner_valid018
  scope371 binding0912_0 certificate372

theorem case_closed0913 : CoreExcluded (baseCore 0 36 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 0 36) owner_valid137
  scope147 binding0913_0 certificate147

theorem case_closed0914 : CoreExcluded (baseCore 0 36 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 0 36) owner_valid138
  scope148 binding0914_0 certificate148

theorem case_closed0915 : CoreExcluded (baseCore 0 36 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 0 36) owner_valid064
  scope149 binding0915_0 certificate149

theorem case_closed0916 : CoreExcluded (baseCore 0 36 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 0 36) owner_valid180
  scope150 binding0916_0 certificate150

theorem case_closed0917 : CoreExcluded (baseCore 0 36 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 0 36) owner_valid129
  scope151 binding0917_0 certificate151

theorem case_closed0918 : CoreExcluded (baseCore 0 36 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 0 36) owner_valid130
  scope152 binding0918_0 certificate152

theorem case_closed0919 : CoreExcluded (baseCore 0 36 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 36) owner_valid025
  scope384 binding0919_0 certificate385

theorem case_closed0920 : CoreExcluded (baseCore 0 36 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 36) owner_valid070
  scope154 binding0920_0 certificate154

theorem case_closed0921 : CoreExcluded (baseCore 0 36 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 36) owner_valid087
  scope386 binding0921_0 certificate387

theorem case_closed0922 : CoreExcluded (baseCore 0 36 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 36) owner_valid072
  scope387 binding0922_0 certificate388

theorem case_closed0923 : CoreExcluded (baseCore 0 36 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 36) owner_valid031
  scope388 binding0923_0 certificate389

theorem case_closed0924 : CoreExcluded (baseCore 0 36 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout181
  (layout_for_all_rows 24 layout181 layout_valid181 0 36) owner_valid181
  scope389 binding0924_0 certificate390

theorem case_closed0925 : CoreExcluded (baseCore 0 37 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout000 layout001
  (layout_for_all_rows 0 layout000 layout_valid000 0 37)
  (layout_for_all_rows 0 layout001 layout_valid001 0 37)
  owner_valid000 owner_valid001 scope000 scope471
  binding0925_0 binding0925_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate000 certificate519 (by decide)

theorem case_closed0926 : CoreExcluded (baseCore 0 37 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 37) owner_valid002
  scope002 binding0926_0 certificate002

theorem case_closed0927 : CoreExcluded (baseCore 0 37 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout003 layout004
  (layout_for_all_rows 2 layout003 layout_valid003 0 37)
  (layout_for_all_rows 2 layout004 layout_valid004 0 37)
  owner_valid003 owner_valid004 scope438 scope004
  binding0927_0 binding0927_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate520 certificate004 (by decide)

theorem case_closed0928 : CoreExcluded (baseCore 0 37 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout005 layout006
  (layout_for_all_rows 3 layout005 layout_valid005 0 37)
  (layout_for_all_rows 3 layout006 layout_valid006 0 37)
  owner_valid005 owner_valid006 scope005 scope473
  binding0928_0 binding0928_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate005 certificate521 (by decide)

theorem case_closed0929 : CoreExcluded (baseCore 0 37 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout008
  (layout_for_all_rows 4 layout007 layout_valid007 0 37)
  (layout_for_all_rows 4 layout008 layout_valid008 0 37)
  owner_valid007 owner_valid008 scope440 scope008
  binding0929_0 binding0929_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate522 certificate008 (by decide)

theorem case_closed0930 : CoreExcluded (baseCore 0 37 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 37) owner_valid009
  scope009 binding0930_0 certificate009

theorem case_closed0931 : CoreExcluded (baseCore 0 37 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 37) owner_valid010
  scope010 binding0931_0 certificate010

theorem case_closed0932 : CoreExcluded (baseCore 0 37 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 37) owner_valid011
  scope011 binding0932_0 certificate011

theorem case_closed0933 : CoreExcluded (baseCore 0 37 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 37) owner_valid012
  scope012 binding0933_0 certificate012

theorem case_closed0934 : CoreExcluded (baseCore 0 37 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 0 37)
  (layout_for_all_rows 9 layout061 layout_valid061 0 37)
  owner_valid116 owner_valid061 scope410 scope180
  binding0934_0 binding0934_1
  2 5 2 5 (by decide) (by decide) 3 2 (by decide)
  certificate523 certificate524 (by decide)

theorem case_closed0935 : CoreExcluded (baseCore 0 37 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout117 layout063
  (layout_for_all_rows 10 layout117 layout_valid117 0 37)
  (layout_for_all_rows 10 layout063 layout_valid063 0 37)
  owner_valid117 owner_valid063 scope422 scope182
  binding0935_0 binding0935_1
  2 5 2 5 (by decide) (by decide) 2 3 (by decide)
  certificate525 certificate526 (by decide)

theorem case_closed0936 : CoreExcluded (baseCore 0 37 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 37) owner_valid017
  scope017 binding0936_0 certificate017

theorem case_closed0937 : CoreExcluded (baseCore 0 37 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 37) owner_valid018
  scope018 binding0937_0 certificate018

theorem case_closed0938 : CoreExcluded (baseCore 0 37 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 37) owner_valid019
  scope019 binding0938_0 certificate019

theorem case_closed0939 : CoreExcluded (baseCore 0 37 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 37) owner_valid020
  scope020 binding0939_0 certificate020

theorem case_closed0940 : CoreExcluded (baseCore 0 37 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 37) owner_valid021
  scope021 binding0940_0 certificate021

theorem case_closed0941 : CoreExcluded (baseCore 0 37 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 37) owner_valid022
  scope022 binding0941_0 certificate022

theorem case_closed0942 : CoreExcluded (baseCore 0 37 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 37) owner_valid023
  scope023 binding0942_0 certificate023

theorem case_closed0943 : CoreExcluded (baseCore 0 37 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 37) owner_valid024
  scope024 binding0943_0 certificate024

theorem case_closed0944 : CoreExcluded (baseCore 0 37 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 37) owner_valid025
  scope025 binding0944_0 certificate025

theorem case_closed0945 : CoreExcluded (baseCore 0 37 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 37) owner_valid026
  scope026 binding0945_0 certificate026

theorem case_closed0946 : CoreExcluded (baseCore 0 37 21) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout050 layout132
  (layout_for_all_rows 21 layout050 layout_valid050 0 37)
  (layout_for_all_rows 21 layout132 layout_valid132 0 37)
  owner_valid050 owner_valid132 scope203 scope027
  binding0946_0 binding0946_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate527 certificate528 (by decide)

theorem case_closed0947 : CoreExcluded (baseCore 0 37 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout052 layout053
  (layout_for_all_rows 22 layout052 layout_valid052 0 37)
  (layout_for_all_rows 22 layout053 layout_valid053 0 37)
  owner_valid052 owner_valid053 scope205 scope397
  binding0947_0 binding0947_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate529 certificate530 (by decide)

theorem case_closed0948 : CoreExcluded (baseCore 0 37 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 37) owner_valid031
  scope031 binding0948_0 certificate031

theorem case_closed0949 : CoreExcluded (baseCore 0 37 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 37) owner_valid032
  scope032 binding0949_0 certificate032

theorem case_closed0950 : CoreExcluded (baseCore 0 38 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout001 layout088
  (layout_for_all_rows 0 layout001 layout_valid001 0 38)
  (layout_for_all_rows 0 layout088 layout_valid088 0 38)
  owner_valid001 owner_valid088 scope128 scope161
  binding0950_0 binding0950_1
  0 9 0 9 (by decide) (by decide) 3 2 (by decide)
  certificate128 certificate161 (by decide)

theorem case_closed0951 : CoreExcluded (baseCore 0 38 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout076 layout089
  (layout_for_all_rows 1 layout076 layout_valid076 0 38)
  (layout_for_all_rows 1 layout089 layout_valid089 0 38)
  owner_valid076 owner_valid089 scope130 scope480
  binding0951_0 binding0951_1
  0 9 0 9 (by decide) (by decide) 2 3 (by decide)
  certificate130 certificate531 (by decide)

theorem case_closed0952 : CoreExcluded (baseCore 0 38 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 38) owner_valid034
  scope132 binding0952_0 certificate132

theorem case_closed0953 : CoreExcluded (baseCore 0 38 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout006
  (layout_for_all_rows 3 layout077 layout_valid077 0 38)
  (layout_for_all_rows 3 layout006 layout_valid006 0 38)
  owner_valid077 owner_valid006 scope439 scope134
  binding0953_0 binding0953_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate532 certificate134 (by decide)

theorem case_closed0954 : CoreExcluded (baseCore 0 38 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout078
  (layout_for_all_rows 4 layout007 layout_valid007 0 38)
  (layout_for_all_rows 4 layout078 layout_valid078 0 38)
  owner_valid007 owner_valid078 scope440 scope136
  binding0954_0 binding0954_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate533 certificate136 (by decide)

theorem case_closed0955 : CoreExcluded (baseCore 0 38 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout108 layout109
  (layout_for_all_rows 5 layout108 layout_valid108 0 38)
  (layout_for_all_rows 5 layout109 layout_valid109 0 38)
  owner_valid108 owner_valid109 scope478 scope172
  binding0955_0 binding0955_1
  4 5 4 5 (by decide) (by decide) 3 2 (by decide)
  certificate534 certificate535 (by decide)

theorem case_closed0956 : CoreExcluded (baseCore 0 38 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout110 layout111
  (layout_for_all_rows 6 layout110 layout_valid110 0 38)
  (layout_for_all_rows 6 layout111 layout_valid111 0 38)
  owner_valid110 owner_valid111 scope477 scope174
  binding0956_0 binding0956_1
  4 5 4 5 (by decide) (by decide) 2 3 (by decide)
  certificate536 certificate537 (by decide)

theorem case_closed0957 : CoreExcluded (baseCore 0 38 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 38) owner_valid011
  scope141 binding0957_0 certificate141

theorem case_closed0958 : CoreExcluded (baseCore 0 38 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 38) owner_valid012
  scope142 binding0958_0 certificate142

theorem case_closed0959 : CoreExcluded (baseCore 0 38 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 38) owner_valid038
  scope143 binding0959_0 certificate143

theorem case_closed0960 : CoreExcluded (baseCore 0 38 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 38) owner_valid079
  scope144 binding0960_0 certificate144

theorem case_closed0961 : CoreExcluded (baseCore 0 38 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 38) owner_valid017
  scope145 binding0961_0 certificate145

theorem case_closed0962 : CoreExcluded (baseCore 0 38 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 38) owner_valid018
  scope146 binding0962_0 certificate146

theorem case_closed0963 : CoreExcluded (baseCore 0 38 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 38) owner_valid019
  scope147 binding0963_0 certificate147

theorem case_closed0964 : CoreExcluded (baseCore 0 38 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 38) owner_valid020
  scope148 binding0964_0 certificate148

theorem case_closed0965 : CoreExcluded (baseCore 0 38 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 38) owner_valid021
  scope149 binding0965_0 certificate149

theorem case_closed0966 : CoreExcluded (baseCore 0 38 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 38) owner_valid022
  scope150 binding0966_0 certificate150

theorem case_closed0967 : CoreExcluded (baseCore 0 38 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 38) owner_valid023
  scope151 binding0967_0 certificate151

theorem case_closed0968 : CoreExcluded (baseCore 0 38 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 38) owner_valid024
  scope152 binding0968_0 certificate152

theorem case_closed0969 : CoreExcluded (baseCore 0 38 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 38) owner_valid025
  scope153 binding0969_0 certificate153

theorem case_closed0970 : CoreExcluded (baseCore 0 38 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 38) owner_valid026
  scope154 binding0970_0 certificate154

theorem case_closed0971 : CoreExcluded (baseCore 0 38 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 38) owner_valid087
  scope155 binding0971_0 certificate155

theorem case_closed0972 : CoreExcluded (baseCore 0 38 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 38) owner_valid072
  scope156 binding0972_0 certificate156

theorem case_closed0973 : CoreExcluded (baseCore 0 38 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 0 38)
  (layout_for_all_rows 23 layout073 layout_valid073 0 38)
  owner_valid054 owner_valid073 scope207 scope470
  binding0973_0 binding0973_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate538 certificate539 (by decide)

theorem case_closed0974 : CoreExcluded (baseCore 0 38 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout074 layout057
  (layout_for_all_rows 24 layout074 layout_valid074 0 38)
  (layout_for_all_rows 24 layout057 layout_valid057 0 38)
  owner_valid074 owner_valid057 scope209 scope461
  binding0974_0 binding0974_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate540 certificate541 (by decide)

theorem case_closed0975 : CoreExcluded (baseCore 0 39 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 39) owner_valid033
  scope095 binding0975_0 certificate095

theorem case_closed0976 : CoreExcluded (baseCore 0 39 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout075 layout076
  (layout_for_all_rows 1 layout075 layout_valid075 0 39)
  (layout_for_all_rows 1 layout076 layout_valid076 0 39)
  owner_valid075 owner_valid076 scope096 scope472
  binding0976_0 binding0976_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate096 certificate542 (by decide)

theorem case_closed0977 : CoreExcluded (baseCore 0 39 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout003 layout004
  (layout_for_all_rows 2 layout003 layout_valid003 0 39)
  (layout_for_all_rows 2 layout004 layout_valid004 0 39)
  owner_valid003 owner_valid004 scope098 scope404
  binding0977_0 binding0977_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate098 certificate543 (by decide)

theorem case_closed0978 : CoreExcluded (baseCore 0 39 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout005
  (layout_for_all_rows 3 layout077 layout_valid077 0 39)
  (layout_for_all_rows 3 layout005 layout_valid005 0 39)
  owner_valid077 owner_valid005 scope100 scope167
  binding0978_0 binding0978_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate100 certificate544 (by decide)

theorem case_closed0979 : CoreExcluded (baseCore 0 39 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout078
  (layout_for_all_rows 4 layout007 layout_valid007 0 39)
  (layout_for_all_rows 4 layout078 layout_valid078 0 39)
  owner_valid007 owner_valid078 scope102 scope474
  binding0979_0 binding0979_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate102 certificate545 (by decide)

theorem case_closed0980 : CoreExcluded (baseCore 0 39 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 39) owner_valid009
  scope104 binding0980_0 certificate104

theorem case_closed0981 : CoreExcluded (baseCore 0 39 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 39) owner_valid010
  scope105 binding0981_0 certificate105

theorem case_closed0982 : CoreExcluded (baseCore 0 39 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 39) owner_valid011
  scope106 binding0982_0 certificate106

theorem case_closed0983 : CoreExcluded (baseCore 0 39 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 39) owner_valid012
  scope107 binding0983_0 certificate107

theorem case_closed0984 : CoreExcluded (baseCore 0 39 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 39) owner_valid038
  scope108 binding0984_0 certificate108

theorem case_closed0985 : CoreExcluded (baseCore 0 39 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 39) owner_valid079
  scope109 binding0985_0 certificate109

theorem case_closed0986 : CoreExcluded (baseCore 0 39 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 39) owner_valid017
  scope110 binding0986_0 certificate110

theorem case_closed0987 : CoreExcluded (baseCore 0 39 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 39) owner_valid018
  scope111 binding0987_0 certificate111

theorem case_closed0988 : CoreExcluded (baseCore 0 39 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 39) owner_valid019
  scope112 binding0988_0 certificate112

theorem case_closed0989 : CoreExcluded (baseCore 0 39 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 39) owner_valid020
  scope113 binding0989_0 certificate113

theorem case_closed0990 : CoreExcluded (baseCore 0 39 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 39) owner_valid021
  scope114 binding0990_0 certificate114

theorem case_closed0991 : CoreExcluded (baseCore 0 39 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 39) owner_valid022
  scope115 binding0991_0 certificate115

theorem case_closed0992 : CoreExcluded (baseCore 0 39 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 0 39)
  (layout_for_all_rows 17 layout046 layout_valid046 0 39)
  owner_valid129 owner_valid046 scope459 scope196
  binding0992_0 binding0992_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate546 certificate547 (by decide)

theorem case_closed0993 : CoreExcluded (baseCore 0 39 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout130 layout048
  (layout_for_all_rows 18 layout130 layout_valid130 0 39)
  (layout_for_all_rows 18 layout048 layout_valid048 0 39)
  owner_valid130 owner_valid048 scope481 scope198
  binding0993_0 binding0993_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate548 certificate549 (by decide)

theorem case_closed0994 : CoreExcluded (baseCore 0 39 19) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout131 layout069
  (layout_for_all_rows 19 layout131 layout_valid131 0 39)
  (layout_for_all_rows 19 layout069 layout_valid069 0 39)
  owner_valid131 owner_valid069 scope482 scope200
  binding0994_0 binding0994_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate550 certificate551 (by decide)

theorem case_closed0995 : CoreExcluded (baseCore 0 39 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout070 layout071
  (layout_for_all_rows 20 layout070 layout_valid070 0 39)
  (layout_for_all_rows 20 layout071 layout_valid071 0 39)
  owner_valid070 owner_valid071 scope435 scope202
  binding0995_0 binding0995_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate552 certificate553 (by decide)

theorem case_closed0996 : CoreExcluded (baseCore 0 39 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 39) owner_valid087
  scope124 binding0996_0 certificate124

theorem case_closed0997 : CoreExcluded (baseCore 0 39 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 39) owner_valid072
  scope125 binding0997_0 certificate125

theorem case_closed0998 : CoreExcluded (baseCore 0 39 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 39) owner_valid031
  scope126 binding0998_0 certificate126

theorem case_closed0999 : CoreExcluded (baseCore 0 39 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 39) owner_valid032
  scope127 binding0999_0 certificate127

theorem block_closed009 (i : Fin 100) : CoreExcluded (caseCore (blockCase 9 i)) := by
 fin_cases i
 · exact case_closed0900
 · exact case_closed0901
 · exact case_closed0902
 · exact case_closed0903
 · exact case_closed0904
 · exact case_closed0905
 · exact case_closed0906
 · exact case_closed0907
 · exact case_closed0908
 · exact case_closed0909
 · exact case_closed0910
 · exact case_closed0911
 · exact case_closed0912
 · exact case_closed0913
 · exact case_closed0914
 · exact case_closed0915
 · exact case_closed0916
 · exact case_closed0917
 · exact case_closed0918
 · exact case_closed0919
 · exact case_closed0920
 · exact case_closed0921
 · exact case_closed0922
 · exact case_closed0923
 · exact case_closed0924
 · exact case_closed0925
 · exact case_closed0926
 · exact case_closed0927
 · exact case_closed0928
 · exact case_closed0929
 · exact case_closed0930
 · exact case_closed0931
 · exact case_closed0932
 · exact case_closed0933
 · exact case_closed0934
 · exact case_closed0935
 · exact case_closed0936
 · exact case_closed0937
 · exact case_closed0938
 · exact case_closed0939
 · exact case_closed0940
 · exact case_closed0941
 · exact case_closed0942
 · exact case_closed0943
 · exact case_closed0944
 · exact case_closed0945
 · exact case_closed0946
 · exact case_closed0947
 · exact case_closed0948
 · exact case_closed0949
 · exact case_closed0950
 · exact case_closed0951
 · exact case_closed0952
 · exact case_closed0953
 · exact case_closed0954
 · exact case_closed0955
 · exact case_closed0956
 · exact case_closed0957
 · exact case_closed0958
 · exact case_closed0959
 · exact case_closed0960
 · exact case_closed0961
 · exact case_closed0962
 · exact case_closed0963
 · exact case_closed0964
 · exact case_closed0965
 · exact case_closed0966
 · exact case_closed0967
 · exact case_closed0968
 · exact case_closed0969
 · exact case_closed0970
 · exact case_closed0971
 · exact case_closed0972
 · exact case_closed0973
 · exact case_closed0974
 · exact case_closed0975
 · exact case_closed0976
 · exact case_closed0977
 · exact case_closed0978
 · exact case_closed0979
 · exact case_closed0980
 · exact case_closed0981
 · exact case_closed0982
 · exact case_closed0983
 · exact case_closed0984
 · exact case_closed0985
 · exact case_closed0986
 · exact case_closed0987
 · exact case_closed0988
 · exact case_closed0989
 · exact case_closed0990
 · exact case_closed0991
 · exact case_closed0992
 · exact case_closed0993
 · exact case_closed0994
 · exact case_closed0995
 · exact case_closed0996
 · exact case_closed0997
 · exact case_closed0998
 · exact case_closed0999
end PricingC.GIsomorphic