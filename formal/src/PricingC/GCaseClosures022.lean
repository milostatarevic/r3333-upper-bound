import PricingC.GCoreExcluded
import PricingC.GBindings022
import PricingC.GScopeChecks000
import PricingC.GScopeChecks001
import PricingC.GScopeChecks002
import PricingC.GScopeChecks003
import PricingC.GScopeChecks005
import PricingC.GScopeChecks006
import PricingC.GScopeChecks007
import PricingC.GScopeChecks026
import PricingC.GScopeChecks027
import PricingC.GScopeChecks028
import PricingC.GScopeChecks030
import PricingC.GScopeChecks031
import PricingC.GScopeChecks040
import PricingC.GScopeChecks041
import PricingC.GScopeChecks042
import PricingC.GScopeChecks043
import PricingC.GScopeChecks044
import PricingC.GScopeChecks045
import PricingC.GScopeChecks047
import PricingC.GScopeChecks050
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

theorem case_closed2200 : CoreExcluded (baseCore 1 16 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout000 layout001
  (layout_for_all_rows 0 layout000 layout_valid000 1 16)
  (layout_for_all_rows 0 layout001 layout_valid001 1 16)
  owner_valid000 owner_valid001 scope000 scope331
  binding2200_0 binding2200_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate000 certificate804 (by decide)

theorem case_closed2201 : CoreExcluded (baseCore 1 16 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 16) owner_valid075
  scope002 binding2201_0 certificate002

theorem case_closed2202 : CoreExcluded (baseCore 1 16 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout003 layout004
  (layout_for_all_rows 2 layout003 layout_valid003 1 16)
  (layout_for_all_rows 2 layout004 layout_valid004 1 16)
  owner_valid003 owner_valid004 scope003 scope004
  binding2202_0 binding2202_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate003 certificate004 (by decide)

theorem case_closed2203 : CoreExcluded (baseCore 1 16 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout006
  (layout_for_all_rows 3 layout077 layout_valid077 1 16)
  (layout_for_all_rows 3 layout006 layout_valid006 1 16)
  owner_valid077 owner_valid006 scope655 scope335
  binding2203_0 binding2203_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate805 certificate806 (by decide)

theorem case_closed2204 : CoreExcluded (baseCore 1 16 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 16) owner_valid036
  scope612 binding2204_0 certificate755

theorem case_closed2205 : CoreExcluded (baseCore 1 16 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 16) owner_valid009
  scope534 binding2205_0 certificate653

theorem case_closed2206 : CoreExcluded (baseCore 1 16 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 16) owner_valid010
  scope535 binding2206_0 certificate654

theorem case_closed2207 : CoreExcluded (baseCore 1 16 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 16) owner_valid011
  scope537 binding2207_0 certificate656

theorem case_closed2208 : CoreExcluded (baseCore 1 16 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 16) owner_valid012
  scope536 binding2208_0 certificate655

theorem case_closed2209 : CoreExcluded (baseCore 1 16 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 1 16)
  (layout_for_all_rows 9 layout061 layout_valid061 1 16)
  owner_valid116 owner_valid061 scope410 scope351
  binding2209_0 binding2209_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate418 certificate756 (by decide)

theorem case_closed2210 : CoreExcluded (baseCore 1 16 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout039 layout063
  (layout_for_all_rows 10 layout039 layout_valid039 1 16)
  (layout_for_all_rows 10 layout063 layout_valid063 1 16)
  owner_valid039 owner_valid063 scope411 scope489
  binding2210_0 binding2210_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate419 certificate757 (by decide)

theorem case_closed2211 : CoreExcluded (baseCore 1 16 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 16) owner_valid017
  scope541 binding2211_0 certificate661

theorem case_closed2212 : CoreExcluded (baseCore 1 16 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 16) owner_valid018
  scope540 binding2212_0 certificate660

theorem case_closed2213 : CoreExcluded (baseCore 1 16 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 16) owner_valid137
  scope019 binding2213_0 certificate019

theorem case_closed2214 : CoreExcluded (baseCore 1 16 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 16) owner_valid138
  scope020 binding2214_0 certificate020

theorem case_closed2215 : CoreExcluded (baseCore 1 16 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 16) owner_valid021
  scope613 binding2215_0 certificate758

theorem case_closed2216 : CoreExcluded (baseCore 1 16 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 16) owner_valid022
  scope614 binding2216_0 certificate759

theorem case_closed2217 : CoreExcluded (baseCore 1 16 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 16) owner_valid023
  scope615 binding2217_0 certificate760

theorem case_closed2218 : CoreExcluded (baseCore 1 16 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 16) owner_valid024
  scope616 binding2218_0 certificate761

theorem case_closed2219 : CoreExcluded (baseCore 1 16 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 16) owner_valid025
  scope617 binding2219_0 certificate762

theorem case_closed2220 : CoreExcluded (baseCore 1 16 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 16) owner_valid026
  scope542 binding2220_0 certificate662

theorem case_closed2221 : CoreExcluded (baseCore 1 16 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 16) owner_valid087
  scope618 binding2221_0 certificate763

theorem case_closed2222 : CoreExcluded (baseCore 1 16 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 16) owner_valid072
  scope619 binding2222_0 certificate764

theorem case_closed2223 : CoreExcluded (baseCore 1 16 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 16) owner_valid031
  scope620 binding2223_0 certificate765

theorem case_closed2224 : CoreExcluded (baseCore 1 16 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 16) owner_valid032
  scope543 binding2224_0 certificate663

theorem case_closed2225 : CoreExcluded (baseCore 1 17 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 17) owner_valid033
  scope426 binding2225_0 certificate441

theorem case_closed2226 : CoreExcluded (baseCore 1 17 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 17) owner_valid002
  scope425 binding2226_0 certificate440

theorem case_closed2227 : CoreExcluded (baseCore 1 17 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 17) owner_valid034
  scope552 binding2227_0 certificate677

theorem case_closed2228 : CoreExcluded (baseCore 1 17 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 17) owner_valid035
  scope427 binding2228_0 certificate442

theorem case_closed2229 : CoreExcluded (baseCore 1 17 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 17) owner_valid036
  scope428 binding2229_0 certificate443

theorem case_closed2230 : CoreExcluded (baseCore 1 17 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 1 17) owner_valid037
  scope010 binding2230_0 certificate010

theorem case_closed2231 : CoreExcluded (baseCore 1 17 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 17) owner_valid010
  scope429 binding2231_0 certificate444

theorem case_closed2232 : CoreExcluded (baseCore 1 17 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 17) owner_valid011
  scope553 binding2232_0 certificate678

theorem case_closed2233 : CoreExcluded (baseCore 1 17 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 17) owner_valid012
  scope554 binding2233_0 certificate679

theorem case_closed2234 : CoreExcluded (baseCore 1 17 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout116
  (layout_for_all_rows 9 layout116 layout_valid116 1 17) owner_valid116
  scope416 binding2234_0 certificate424

theorem case_closed2235 : CoreExcluded (baseCore 1 17 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout062
  (layout_for_all_rows 10 layout062 layout_valid062 1 17) owner_valid062
  scope114 binding2235_0 certificate114

theorem case_closed2236 : CoreExcluded (baseCore 1 17 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 17) owner_valid017
  scope084 binding2236_0 certificate084

theorem case_closed2237 : CoreExcluded (baseCore 1 17 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 1 17) owner_valid042
  scope017 binding2237_0 certificate017

theorem case_closed2238 : CoreExcluded (baseCore 1 17 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 17) owner_valid137
  scope019 binding2238_0 certificate019

theorem case_closed2239 : CoreExcluded (baseCore 1 17 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 17) owner_valid020
  scope433 binding2239_0 certificate451

theorem case_closed2240 : CoreExcluded (baseCore 1 17 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 17) owner_valid064
  scope021 binding2240_0 certificate021

theorem case_closed2241 : CoreExcluded (baseCore 1 17 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 17) owner_valid180
  scope022 binding2241_0 certificate022

theorem case_closed2242 : CoreExcluded (baseCore 1 17 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 17) owner_valid023
  scope556 binding2242_0 certificate682

theorem case_closed2243 : CoreExcluded (baseCore 1 17 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 17) owner_valid024
  scope557 binding2243_0 certificate683

theorem case_closed2244 : CoreExcluded (baseCore 1 17 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 17) owner_valid131
  scope025 binding2244_0 certificate025

theorem case_closed2245 : CoreExcluded (baseCore 1 17 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 17) owner_valid070
  scope026 binding2245_0 certificate026

theorem case_closed2246 : CoreExcluded (baseCore 1 17 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout027
  (layout_for_all_rows 21 layout027 layout_valid027 1 17) owner_valid027
  scope124 binding2246_0 certificate124

theorem case_closed2247 : CoreExcluded (baseCore 1 17 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 17) owner_valid072
  scope559 binding2247_0 certificate685

theorem case_closed2248 : CoreExcluded (baseCore 1 17 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 1 17) owner_valid054
  scope031 binding2248_0 certificate031

theorem case_closed2249 : CoreExcluded (baseCore 1 17 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 17) owner_valid074
  scope032 binding2249_0 certificate032

theorem case_closed2250 : CoreExcluded (baseCore 1 18 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 18) owner_valid033
  scope572 binding2250_0 certificate699

theorem case_closed2251 : CoreExcluded (baseCore 1 18 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 18) owner_valid002
  scope412 binding2251_0 certificate420

theorem case_closed2252 : CoreExcluded (baseCore 1 18 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 18) owner_valid034
  scope413 binding2252_0 certificate421

theorem case_closed2253 : CoreExcluded (baseCore 1 18 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 18) owner_valid035
  scope414 binding2253_0 certificate422

theorem case_closed2254 : CoreExcluded (baseCore 1 18 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 18) owner_valid036
  scope415 binding2254_0 certificate423

theorem case_closed2255 : CoreExcluded (baseCore 1 18 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 18) owner_valid009
  scope418 binding2255_0 certificate430

theorem case_closed2256 : CoreExcluded (baseCore 1 18 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout110
  (layout_for_all_rows 6 layout110 layout_valid110 1 18) owner_valid110
  scope656 binding2256_0 certificate807

theorem case_closed2257 : CoreExcluded (baseCore 1 18 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 18) owner_valid059
  scope040 binding2257_0 certificate040

theorem case_closed2258 : CoreExcluded (baseCore 1 18 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 18) owner_valid012
  scope046 binding2258_0 certificate046

theorem case_closed2259 : CoreExcluded (baseCore 1 18 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 18) owner_valid038
  scope573 binding2259_0 certificate700

theorem case_closed2260 : CoreExcluded (baseCore 1 18 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 18) owner_valid079
  scope574 binding2260_0 certificate701

theorem case_closed2261 : CoreExcluded (baseCore 1 18 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout040 layout041
  (layout_for_all_rows 11 layout040 layout_valid040 1 18)
  (layout_for_all_rows 11 layout041 layout_valid041 1 18)
  owner_valid040 owner_valid041 scope042 scope560
  binding2261_0 binding2261_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate042 certificate686 (by decide)

theorem case_closed2262 : CoreExcluded (baseCore 1 18 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout042 layout043
  (layout_for_all_rows 12 layout042 layout_valid042 1 18)
  (layout_for_all_rows 12 layout043 layout_valid043 1 18)
  owner_valid042 owner_valid043 scope044 scope561
  binding2262_0 binding2262_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate044 certificate687 (by decide)

theorem case_closed2263 : CoreExcluded (baseCore 1 18 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 18) owner_valid019
  scope575 binding2263_0 certificate702

theorem case_closed2264 : CoreExcluded (baseCore 1 18 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 18) owner_valid020
  scope576 binding2264_0 certificate703

theorem case_closed2265 : CoreExcluded (baseCore 1 18 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 18) owner_valid021
  scope416 binding2265_0 certificate424

theorem case_closed2266 : CoreExcluded (baseCore 1 18 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 18) owner_valid180
  scope049 binding2266_0 certificate049

theorem case_closed2267 : CoreExcluded (baseCore 1 18 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout046
  (layout_for_all_rows 17 layout046 layout_valid046 1 18) owner_valid046
  scope657 binding2267_0 certificate808

theorem case_closed2268 : CoreExcluded (baseCore 1 18 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout048
  (layout_for_all_rows 18 layout048 layout_valid048 1 18) owner_valid048
  scope658 binding2268_0 certificate809

theorem case_closed2269 : CoreExcluded (baseCore 1 18 19) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout083 layout084
  (layout_for_all_rows 19 layout083 layout_valid083 1 18)
  (layout_for_all_rows 19 layout084 layout_valid084 1 18)
  owner_valid083 owner_valid084 scope659 scope121
  binding2269_0 binding2269_1
  2 5 6 0 (by decide) (by decide) 3 2 (by decide)
  certificate810 certificate121 (by decide)

theorem case_closed2270 : CoreExcluded (baseCore 1 18 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 18) owner_valid026
  scope579 binding2270_0 certificate707

theorem case_closed2271 : CoreExcluded (baseCore 1 18 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout051
  (layout_for_all_rows 21 layout051 layout_valid051 1 18) owner_valid051
  scope660 binding2271_0 certificate811

theorem case_closed2272 : CoreExcluded (baseCore 1 18 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout052 layout053
  (layout_for_all_rows 22 layout052 layout_valid052 1 18)
  (layout_for_all_rows 22 layout053 layout_valid053 1 18)
  owner_valid052 owner_valid053 scope058 scope059
  binding2272_0 binding2272_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate058 certificate059 (by decide)

theorem case_closed2273 : CoreExcluded (baseCore 1 18 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout055
  (layout_for_all_rows 23 layout054 layout_valid054 1 18)
  (layout_for_all_rows 23 layout055 layout_valid055 1 18)
  owner_valid054 owner_valid055 scope060 scope061
  binding2273_0 binding2273_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate060 certificate061 (by decide)

theorem case_closed2274 : CoreExcluded (baseCore 1 18 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout057
  (layout_for_all_rows 24 layout057 layout_valid057 1 18) owner_valid057
  scope661 binding2274_0 certificate812

theorem case_closed2275 : CoreExcluded (baseCore 1 19 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 19) owner_valid187
  scope033 binding2275_0 certificate033

theorem case_closed2276 : CoreExcluded (baseCore 1 19 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 19) owner_valid075
  scope034 binding2276_0 certificate034

theorem case_closed2277 : CoreExcluded (baseCore 1 19 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 19) owner_valid003
  scope035 binding2277_0 certificate035

theorem case_closed2278 : CoreExcluded (baseCore 1 19 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 19) owner_valid077
  scope036 binding2278_0 certificate036

theorem case_closed2279 : CoreExcluded (baseCore 1 19 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 19) owner_valid007
  scope037 binding2279_0 certificate037

theorem case_closed2280 : CoreExcluded (baseCore 1 19 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 1 19) owner_valid037
  scope038 binding2280_0 certificate038

theorem case_closed2281 : CoreExcluded (baseCore 1 19 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout147
  (layout_for_all_rows 6 layout147 layout_valid147 1 19) owner_valid147
  scope104 binding2281_0 certificate104

theorem case_closed2282 : CoreExcluded (baseCore 1 19 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 19) owner_valid059
  scope040 binding2282_0 certificate040

theorem case_closed2283 : CoreExcluded (baseCore 1 19 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 19) owner_valid134
  scope039 binding2283_0 certificate039

theorem case_closed2284 : CoreExcluded (baseCore 1 19 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout116
  (layout_for_all_rows 9 layout116 layout_valid116 1 19) owner_valid116
  scope462 binding2284_0 certificate491

theorem case_closed2285 : CoreExcluded (baseCore 1 19 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 19) owner_valid039
  scope041 binding2285_0 certificate041

theorem case_closed2286 : CoreExcluded (baseCore 1 19 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout040
  (layout_for_all_rows 11 layout040 layout_valid040 1 19) owner_valid040
  scope590 binding2286_0 certificate732

theorem case_closed2287 : CoreExcluded (baseCore 1 19 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout119
  (layout_for_all_rows 12 layout119 layout_valid119 1 19) owner_valid119
  scope591 binding2287_0 certificate733

theorem case_closed2288 : CoreExcluded (baseCore 1 19 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout044
  (layout_for_all_rows 13 layout044 layout_valid044 1 19) owner_valid044
  scope586 binding2288_0 certificate728

theorem case_closed2289 : CoreExcluded (baseCore 1 19 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 19) owner_valid138
  scope047 binding2289_0 certificate047

theorem case_closed2290 : CoreExcluded (baseCore 1 19 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 19) owner_valid064
  scope048 binding2290_0 certificate048

theorem case_closed2291 : CoreExcluded (baseCore 1 19 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 19) owner_valid180
  scope049 binding2291_0 certificate049

theorem case_closed2292 : CoreExcluded (baseCore 1 19 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout140
  (layout_for_all_rows 17 layout140 layout_valid140 1 19) owner_valid140
  scope587 binding2292_0 certificate729

theorem case_closed2293 : CoreExcluded (baseCore 1 19 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout068
  (layout_for_all_rows 18 layout068 layout_valid068 1 19) owner_valid068
  scope466 binding2293_0 certificate495

theorem case_closed2294 : CoreExcluded (baseCore 1 19 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout069
  (layout_for_all_rows 19 layout069 layout_valid069 1 19) owner_valid069
  scope467 binding2294_0 certificate496

theorem case_closed2295 : CoreExcluded (baseCore 1 19 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 19) owner_valid070
  scope055 binding2295_0 certificate055

theorem case_closed2296 : CoreExcluded (baseCore 1 19 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout132
  (layout_for_all_rows 21 layout132 layout_valid132 1 19) owner_valid132
  scope469 binding2296_0 certificate498

theorem case_closed2297 : CoreExcluded (baseCore 1 19 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout053
  (layout_for_all_rows 22 layout053 layout_valid053 1 19) owner_valid053
  scope592 binding2297_0 certificate734

theorem case_closed2298 : CoreExcluded (baseCore 1 19 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout055
  (layout_for_all_rows 23 layout054 layout_valid054 1 19)
  (layout_for_all_rows 23 layout055 layout_valid055 1 19)
  owner_valid054 owner_valid055 scope060 scope157
  binding2298_0 binding2298_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate431 certificate432 (by decide)

theorem case_closed2299 : CoreExcluded (baseCore 1 19 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout096
  (layout_for_all_rows 24 layout096 layout_valid096 1 19) owner_valid096
  scope127 binding2299_0 certificate127

theorem block_closed022 (i : Fin 100) : CoreExcluded (caseCore (blockCase 22 i)) := by
 fin_cases i
 · exact case_closed2200
 · exact case_closed2201
 · exact case_closed2202
 · exact case_closed2203
 · exact case_closed2204
 · exact case_closed2205
 · exact case_closed2206
 · exact case_closed2207
 · exact case_closed2208
 · exact case_closed2209
 · exact case_closed2210
 · exact case_closed2211
 · exact case_closed2212
 · exact case_closed2213
 · exact case_closed2214
 · exact case_closed2215
 · exact case_closed2216
 · exact case_closed2217
 · exact case_closed2218
 · exact case_closed2219
 · exact case_closed2220
 · exact case_closed2221
 · exact case_closed2222
 · exact case_closed2223
 · exact case_closed2224
 · exact case_closed2225
 · exact case_closed2226
 · exact case_closed2227
 · exact case_closed2228
 · exact case_closed2229
 · exact case_closed2230
 · exact case_closed2231
 · exact case_closed2232
 · exact case_closed2233
 · exact case_closed2234
 · exact case_closed2235
 · exact case_closed2236
 · exact case_closed2237
 · exact case_closed2238
 · exact case_closed2239
 · exact case_closed2240
 · exact case_closed2241
 · exact case_closed2242
 · exact case_closed2243
 · exact case_closed2244
 · exact case_closed2245
 · exact case_closed2246
 · exact case_closed2247
 · exact case_closed2248
 · exact case_closed2249
 · exact case_closed2250
 · exact case_closed2251
 · exact case_closed2252
 · exact case_closed2253
 · exact case_closed2254
 · exact case_closed2255
 · exact case_closed2256
 · exact case_closed2257
 · exact case_closed2258
 · exact case_closed2259
 · exact case_closed2260
 · exact case_closed2261
 · exact case_closed2262
 · exact case_closed2263
 · exact case_closed2264
 · exact case_closed2265
 · exact case_closed2266
 · exact case_closed2267
 · exact case_closed2268
 · exact case_closed2269
 · exact case_closed2270
 · exact case_closed2271
 · exact case_closed2272
 · exact case_closed2273
 · exact case_closed2274
 · exact case_closed2275
 · exact case_closed2276
 · exact case_closed2277
 · exact case_closed2278
 · exact case_closed2279
 · exact case_closed2280
 · exact case_closed2281
 · exact case_closed2282
 · exact case_closed2283
 · exact case_closed2284
 · exact case_closed2285
 · exact case_closed2286
 · exact case_closed2287
 · exact case_closed2288
 · exact case_closed2289
 · exact case_closed2290
 · exact case_closed2291
 · exact case_closed2292
 · exact case_closed2293
 · exact case_closed2294
 · exact case_closed2295
 · exact case_closed2296
 · exact case_closed2297
 · exact case_closed2298
 · exact case_closed2299
end PricingC.GIsomorphic