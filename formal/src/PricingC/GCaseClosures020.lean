import PricingC.GCoreExcluded
import PricingC.GBindings020
import PricingC.GScopeChecks016
import PricingC.GScopeChecks017
import PricingC.GScopeChecks019
import PricingC.GScopeChecks020
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks038
import PricingC.GScopeChecks039
import PricingC.GScopeChecks040
import PricingC.GScopeChecks041
import PricingC.GScopeChecks042
import PricingC.GScopeChecks047
import PricingC.GScopeChecks048
import PricingC.GScopeChecks049
import PricingC.GScopeChecks050
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks007

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed2000 : CoreExcluded (baseCore 1 8 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 8) owner_valid187
  scope267 binding2000_0 certificate267

theorem case_closed2001 : CoreExcluded (baseCore 1 8 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 8) owner_valid075
  scope268 binding2001_0 certificate268

theorem case_closed2002 : CoreExcluded (baseCore 1 8 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 8) owner_valid003
  scope269 binding2002_0 certificate269

theorem case_closed2003 : CoreExcluded (baseCore 1 8 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 8) owner_valid077
  scope270 binding2003_0 certificate270

theorem case_closed2004 : CoreExcluded (baseCore 1 8 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 8) owner_valid036
  scope612 binding2004_0 certificate755

theorem case_closed2005 : CoreExcluded (baseCore 1 8 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 8) owner_valid009
  scope534 binding2005_0 certificate653

theorem case_closed2006 : CoreExcluded (baseCore 1 8 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 8) owner_valid010
  scope535 binding2006_0 certificate654

theorem case_closed2007 : CoreExcluded (baseCore 1 8 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 8) owner_valid011
  scope537 binding2007_0 certificate656

theorem case_closed2008 : CoreExcluded (baseCore 1 8 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 8) owner_valid012
  scope536 binding2008_0 certificate655

theorem case_closed2009 : CoreExcluded (baseCore 1 8 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout116 layout061
  (layout_for_all_rows 9 layout116 layout_valid116 1 8)
  (layout_for_all_rows 9 layout061 layout_valid061 1 8)
  owner_valid116 owner_valid061 scope276 scope351
  binding2009_0 binding2009_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate276 certificate756 (by decide)

theorem case_closed2010 : CoreExcluded (baseCore 1 8 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout039 layout063
  (layout_for_all_rows 10 layout039 layout_valid039 1 8)
  (layout_for_all_rows 10 layout063 layout_valid063 1 8)
  owner_valid039 owner_valid063 scope278 scope489
  binding2010_0 binding2010_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate278 certificate757 (by decide)

theorem case_closed2011 : CoreExcluded (baseCore 1 8 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 8) owner_valid017
  scope541 binding2011_0 certificate661

theorem case_closed2012 : CoreExcluded (baseCore 1 8 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 8) owner_valid018
  scope540 binding2012_0 certificate660

theorem case_closed2013 : CoreExcluded (baseCore 1 8 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 8) owner_valid137
  scope284 binding2013_0 certificate284

theorem case_closed2014 : CoreExcluded (baseCore 1 8 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout139
  (layout_for_all_rows 14 layout139 layout_valid139 1 8) owner_valid139
  scope285 binding2014_0 certificate285

theorem case_closed2015 : CoreExcluded (baseCore 1 8 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 8) owner_valid021
  scope613 binding2015_0 certificate758

theorem case_closed2016 : CoreExcluded (baseCore 1 8 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 8) owner_valid022
  scope614 binding2016_0 certificate759

theorem case_closed2017 : CoreExcluded (baseCore 1 8 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 8) owner_valid023
  scope615 binding2017_0 certificate760

theorem case_closed2018 : CoreExcluded (baseCore 1 8 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 8) owner_valid024
  scope616 binding2018_0 certificate761

theorem case_closed2019 : CoreExcluded (baseCore 1 8 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 8) owner_valid025
  scope617 binding2019_0 certificate762

theorem case_closed2020 : CoreExcluded (baseCore 1 8 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 8) owner_valid026
  scope542 binding2020_0 certificate662

theorem case_closed2021 : CoreExcluded (baseCore 1 8 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 8) owner_valid087
  scope618 binding2021_0 certificate763

theorem case_closed2022 : CoreExcluded (baseCore 1 8 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 8) owner_valid072
  scope619 binding2022_0 certificate764

theorem case_closed2023 : CoreExcluded (baseCore 1 8 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 8) owner_valid031
  scope620 binding2023_0 certificate765

theorem case_closed2024 : CoreExcluded (baseCore 1 8 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 8) owner_valid032
  scope543 binding2024_0 certificate663

theorem case_closed2025 : CoreExcluded (baseCore 1 9 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 9) owner_valid033
  scope546 binding2025_0 certificate670

theorem case_closed2026 : CoreExcluded (baseCore 1 9 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 9) owner_valid002
  scope545 binding2026_0 certificate669

theorem case_closed2027 : CoreExcluded (baseCore 1 9 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 9) owner_valid034
  scope547 binding2027_0 certificate671

theorem case_closed2028 : CoreExcluded (baseCore 1 9 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 9) owner_valid035
  scope548 binding2028_0 certificate672

theorem case_closed2029 : CoreExcluded (baseCore 1 9 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 9) owner_valid036
  scope621 binding2029_0 certificate766

theorem case_closed2030 : CoreExcluded (baseCore 1 9 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 1 9) owner_valid037
  scope306 binding2030_0 certificate306

theorem case_closed2031 : CoreExcluded (baseCore 1 9 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 1 9) owner_valid058
  scope305 binding2031_0 certificate305

theorem case_closed2032 : CoreExcluded (baseCore 1 9 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 9) owner_valid059
  scope308 binding2032_0 certificate308

theorem case_closed2033 : CoreExcluded (baseCore 1 9 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 9) owner_valid134
  scope307 binding2033_0 certificate307

theorem case_closed2034 : CoreExcluded (baseCore 1 9 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 1 9) owner_valid136
  scope310 binding2034_0 certificate310

theorem case_closed2035 : CoreExcluded (baseCore 1 9 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 9) owner_valid039
  scope309 binding2035_0 certificate309

theorem case_closed2036 : CoreExcluded (baseCore 1 9 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout149 layout041
  (layout_for_all_rows 11 layout149 layout_valid149 1 9)
  (layout_for_all_rows 11 layout041 layout_valid041 1 9)
  owner_valid149 owner_valid041 scope622 scope623
  binding2036_0 binding2036_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate767 certificate768 (by decide)

theorem case_closed2037 : CoreExcluded (baseCore 1 9 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout188 layout189
  (layout_for_all_rows 12 layout188 layout_valid188 1 9)
  (layout_for_all_rows 12 layout189 layout_valid189 1 9)
  owner_valid188 owner_valid189 scope380 scope420
  binding2037_0 binding2037_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate381 certificate769 (by decide)

theorem case_closed2038 : CoreExcluded (baseCore 1 9 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 9) owner_valid019
  scope549 binding2038_0 certificate673

theorem case_closed2039 : CoreExcluded (baseCore 1 9 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout123
  (layout_for_all_rows 14 layout123 layout_valid123 1 9) owner_valid123
  scope368 binding2039_0 certificate369

theorem case_closed2040 : CoreExcluded (baseCore 1 9 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 9) owner_valid021
  scope624 binding2040_0 certificate770

theorem case_closed2041 : CoreExcluded (baseCore 1 9 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 9) owner_valid022
  scope625 binding2041_0 certificate771

theorem case_closed2042 : CoreExcluded (baseCore 1 9 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 1 9) owner_valid129
  scope321 binding2042_0 certificate321

theorem case_closed2043 : CoreExcluded (baseCore 1 9 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 9) owner_valid024
  scope527 binding2043_0 certificate633

theorem case_closed2044 : CoreExcluded (baseCore 1 9 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 9) owner_valid025
  scope626 binding2044_0 certificate772

theorem case_closed2045 : CoreExcluded (baseCore 1 9 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 9) owner_valid070
  scope324 binding2045_0 certificate324

theorem case_closed2046 : CoreExcluded (baseCore 1 9 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 9) owner_valid087
  scope627 binding2046_0 certificate773

theorem case_closed2047 : CoreExcluded (baseCore 1 9 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 9) owner_valid072
  scope628 binding2047_0 certificate774

theorem case_closed2048 : CoreExcluded (baseCore 1 9 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 9) owner_valid031
  scope629 binding2048_0 certificate775

theorem case_closed2049 : CoreExcluded (baseCore 1 9 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 9) owner_valid074
  scope328 binding2049_0 certificate328

theorem case_closed2050 : CoreExcluded (baseCore 1 10 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 10) owner_valid033
  scope630 binding2050_0 certificate776

theorem case_closed2051 : CoreExcluded (baseCore 1 10 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 10) owner_valid002
  scope631 binding2051_0 certificate777

theorem case_closed2052 : CoreExcluded (baseCore 1 10 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 10) owner_valid034
  scope632 binding2052_0 certificate778

theorem case_closed2053 : CoreExcluded (baseCore 1 10 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 10) owner_valid035
  scope633 binding2053_0 certificate779

theorem case_closed2054 : CoreExcluded (baseCore 1 10 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 10) owner_valid036
  scope634 binding2054_0 certificate780

theorem case_closed2055 : CoreExcluded (baseCore 1 10 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 1 10) owner_valid037
  scope339 binding2055_0 certificate339

theorem case_closed2056 : CoreExcluded (baseCore 1 10 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 1 10) owner_valid058
  scope338 binding2056_0 certificate338

theorem case_closed2057 : CoreExcluded (baseCore 1 10 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 10) owner_valid011
  scope285 binding2057_0 certificate285

theorem case_closed2058 : CoreExcluded (baseCore 1 10 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout114
  (layout_for_all_rows 8 layout114 layout_valid114 1 10) owner_valid114
  scope284 binding2058_0 certificate284

theorem case_closed2059 : CoreExcluded (baseCore 1 10 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 1 10) owner_valid136
  scope344 binding2059_0 certificate345

theorem case_closed2060 : CoreExcluded (baseCore 1 10 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 10) owner_valid079
  scope286 binding2060_0 certificate286

theorem case_closed2061 : CoreExcluded (baseCore 1 10 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 10) owner_valid017
  scope635 binding2061_0 certificate781

theorem case_closed2062 : CoreExcluded (baseCore 1 10 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 10) owner_valid018
  scope636 binding2062_0 certificate782

theorem case_closed2063 : CoreExcluded (baseCore 1 10 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 10) owner_valid137
  scope347 binding2063_0 certificate348

theorem case_closed2064 : CoreExcluded (baseCore 1 10 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 10) owner_valid138
  scope348 binding2064_0 certificate349

theorem case_closed2065 : CoreExcluded (baseCore 1 10 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout065
  (layout_for_all_rows 15 layout064 layout_valid064 1 10)
  (layout_for_all_rows 15 layout065 layout_valid065 1 10)
  owner_valid064 owner_valid065 scope528 scope637
  binding2065_0 binding2065_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate783 certificate784 (by decide)

theorem case_closed2066 : CoreExcluded (baseCore 1 10 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout192 layout193
  (layout_for_all_rows 16 layout192 layout_valid192 1 10)
  (layout_for_all_rows 16 layout193 layout_valid193 1 10)
  owner_valid192 owner_valid193 scope278 scope638
  binding2066_0 binding2066_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate278 certificate785 (by decide)

theorem case_closed2067 : CoreExcluded (baseCore 1 10 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 1 10) owner_valid129
  scope353 binding2067_0 certificate354

theorem case_closed2068 : CoreExcluded (baseCore 1 10 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 1 10) owner_valid130
  scope354 binding2068_0 certificate355

theorem case_closed2069 : CoreExcluded (baseCore 1 10 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 10) owner_valid025
  scope639 binding2069_0 certificate786

theorem case_closed2070 : CoreExcluded (baseCore 1 10 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 10) owner_valid026
  scope640 binding2070_0 certificate787

theorem case_closed2071 : CoreExcluded (baseCore 1 10 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 10) owner_valid087
  scope641 binding2071_0 certificate788

theorem case_closed2072 : CoreExcluded (baseCore 1 10 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 10) owner_valid052
  scope358 binding2072_0 certificate359

theorem case_closed2073 : CoreExcluded (baseCore 1 10 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 1 10) owner_valid054
  scope359 binding2073_0 certificate360

theorem case_closed2074 : CoreExcluded (baseCore 1 10 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 10) owner_valid032
  scope642 binding2074_0 certificate789

theorem case_closed2075 : CoreExcluded (baseCore 1 11 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 11) owner_valid187
  scope361 binding2075_0 certificate362

theorem case_closed2076 : CoreExcluded (baseCore 1 11 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 11) owner_valid075
  scope362 binding2076_0 certificate363

theorem case_closed2077 : CoreExcluded (baseCore 1 11 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 11) owner_valid003
  scope363 binding2077_0 certificate364

theorem case_closed2078 : CoreExcluded (baseCore 1 11 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 11) owner_valid035
  scope643 binding2078_0 certificate790

theorem case_closed2079 : CoreExcluded (baseCore 1 11 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 11) owner_valid007
  scope365 binding2079_0 certificate366

theorem case_closed2080 : CoreExcluded (baseCore 1 11 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 11) owner_valid009
  scope644 binding2080_0 certificate791

theorem case_closed2081 : CoreExcluded (baseCore 1 11 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 11) owner_valid010
  scope645 binding2081_0 certificate792

theorem case_closed2082 : CoreExcluded (baseCore 1 11 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 1 11) owner_valid133
  scope549 binding2082_0 certificate673

theorem case_closed2083 : CoreExcluded (baseCore 1 11 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 11) owner_valid134
  scope368 binding2083_0 certificate369

theorem case_closed2084 : CoreExcluded (baseCore 1 11 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 11) owner_valid038
  scope521 binding2084_0 certificate627

theorem case_closed2085 : CoreExcluded (baseCore 1 11 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 11) owner_valid079
  scope646 binding2085_0 certificate793

theorem case_closed2086 : CoreExcluded (baseCore 1 11 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 11) owner_valid017
  scope647 binding2086_0 certificate794

theorem case_closed2087 : CoreExcluded (baseCore 1 11 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 11) owner_valid018
  scope522 binding2087_0 certificate628

theorem case_closed2088 : CoreExcluded (baseCore 1 11 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 11) owner_valid019
  scope519 binding2088_0 certificate622

theorem case_closed2089 : CoreExcluded (baseCore 1 11 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 11) owner_valid020
  scope520 binding2089_0 certificate623

theorem case_closed2090 : CoreExcluded (baseCore 1 11 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 11) owner_valid021
  scope648 binding2090_0 certificate795

theorem case_closed2091 : CoreExcluded (baseCore 1 11 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 11) owner_valid022
  scope649 binding2091_0 certificate796

theorem case_closed2092 : CoreExcluded (baseCore 1 11 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 1 11)
  (layout_for_all_rows 17 layout046 layout_valid046 1 11)
  owner_valid129 owner_valid046 scope380 scope313
  binding2092_0 binding2092_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate381 certificate797 (by decide)

theorem case_closed2093 : CoreExcluded (baseCore 1 11 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout068 layout048
  (layout_for_all_rows 18 layout068 layout_valid068 1 11)
  (layout_for_all_rows 18 layout048 layout_valid048 1 11)
  owner_valid068 owner_valid048 scope382 scope475
  binding2093_0 binding2093_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate383 certificate798 (by decide)

theorem case_closed2094 : CoreExcluded (baseCore 1 11 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 11) owner_valid025
  scope523 binding2094_0 certificate629

theorem case_closed2095 : CoreExcluded (baseCore 1 11 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 11) owner_valid026
  scope524 binding2095_0 certificate630

theorem case_closed2096 : CoreExcluded (baseCore 1 11 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 11) owner_valid087
  scope525 binding2096_0 certificate631

theorem case_closed2097 : CoreExcluded (baseCore 1 11 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 11) owner_valid072
  scope526 binding2097_0 certificate632

theorem case_closed2098 : CoreExcluded (baseCore 1 11 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 11) owner_valid031
  scope650 binding2098_0 certificate799

theorem case_closed2099 : CoreExcluded (baseCore 1 11 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 11) owner_valid032
  scope651 binding2099_0 certificate800

theorem block_closed020 (i : Fin 100) : CoreExcluded (caseCore (blockCase 20 i)) := by
 fin_cases i
 · exact case_closed2000
 · exact case_closed2001
 · exact case_closed2002
 · exact case_closed2003
 · exact case_closed2004
 · exact case_closed2005
 · exact case_closed2006
 · exact case_closed2007
 · exact case_closed2008
 · exact case_closed2009
 · exact case_closed2010
 · exact case_closed2011
 · exact case_closed2012
 · exact case_closed2013
 · exact case_closed2014
 · exact case_closed2015
 · exact case_closed2016
 · exact case_closed2017
 · exact case_closed2018
 · exact case_closed2019
 · exact case_closed2020
 · exact case_closed2021
 · exact case_closed2022
 · exact case_closed2023
 · exact case_closed2024
 · exact case_closed2025
 · exact case_closed2026
 · exact case_closed2027
 · exact case_closed2028
 · exact case_closed2029
 · exact case_closed2030
 · exact case_closed2031
 · exact case_closed2032
 · exact case_closed2033
 · exact case_closed2034
 · exact case_closed2035
 · exact case_closed2036
 · exact case_closed2037
 · exact case_closed2038
 · exact case_closed2039
 · exact case_closed2040
 · exact case_closed2041
 · exact case_closed2042
 · exact case_closed2043
 · exact case_closed2044
 · exact case_closed2045
 · exact case_closed2046
 · exact case_closed2047
 · exact case_closed2048
 · exact case_closed2049
 · exact case_closed2050
 · exact case_closed2051
 · exact case_closed2052
 · exact case_closed2053
 · exact case_closed2054
 · exact case_closed2055
 · exact case_closed2056
 · exact case_closed2057
 · exact case_closed2058
 · exact case_closed2059
 · exact case_closed2060
 · exact case_closed2061
 · exact case_closed2062
 · exact case_closed2063
 · exact case_closed2064
 · exact case_closed2065
 · exact case_closed2066
 · exact case_closed2067
 · exact case_closed2068
 · exact case_closed2069
 · exact case_closed2070
 · exact case_closed2071
 · exact case_closed2072
 · exact case_closed2073
 · exact case_closed2074
 · exact case_closed2075
 · exact case_closed2076
 · exact case_closed2077
 · exact case_closed2078
 · exact case_closed2079
 · exact case_closed2080
 · exact case_closed2081
 · exact case_closed2082
 · exact case_closed2083
 · exact case_closed2084
 · exact case_closed2085
 · exact case_closed2086
 · exact case_closed2087
 · exact case_closed2088
 · exact case_closed2089
 · exact case_closed2090
 · exact case_closed2091
 · exact case_closed2092
 · exact case_closed2093
 · exact case_closed2094
 · exact case_closed2095
 · exact case_closed2096
 · exact case_closed2097
 · exact case_closed2098
 · exact case_closed2099
end PricingC.GIsomorphic