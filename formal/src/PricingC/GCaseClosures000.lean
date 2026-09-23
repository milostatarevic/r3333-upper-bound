import PricingC.GCoreExcluded
import PricingC.GBindings000
import PricingC.GScopeChecks000
import PricingC.GScopeChecks001
import PricingC.GScopeChecks002
import PricingC.GScopeChecks003
import PricingC.GScopeChecks004
import PricingC.GScopeChecks005
import PricingC.GScopeChecks006
import PricingC.GScopeChecks007
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed0000 : CoreExcluded (baseCore 0 0 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout000 layout001
  (layout_for_all_rows 0 layout000 layout_valid000 0 0)
  (layout_for_all_rows 0 layout001 layout_valid001 0 0)
  owner_valid000 owner_valid001 scope000 scope001
  binding0000_0 binding0000_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate000 certificate001 (by decide)

theorem case_closed0001 : CoreExcluded (baseCore 0 0 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 0) owner_valid002
  scope002 binding0001_0 certificate002

theorem case_closed0002 : CoreExcluded (baseCore 0 0 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout003 layout004
  (layout_for_all_rows 2 layout003 layout_valid003 0 0)
  (layout_for_all_rows 2 layout004 layout_valid004 0 0)
  owner_valid003 owner_valid004 scope003 scope004
  binding0002_0 binding0002_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate003 certificate004 (by decide)

theorem case_closed0003 : CoreExcluded (baseCore 0 0 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout005 layout006
  (layout_for_all_rows 3 layout005 layout_valid005 0 0)
  (layout_for_all_rows 3 layout006 layout_valid006 0 0)
  owner_valid005 owner_valid006 scope005 scope006
  binding0003_0 binding0003_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate005 certificate006 (by decide)

theorem case_closed0004 : CoreExcluded (baseCore 0 0 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout008
  (layout_for_all_rows 4 layout007 layout_valid007 0 0)
  (layout_for_all_rows 4 layout008 layout_valid008 0 0)
  owner_valid007 owner_valid008 scope007 scope008
  binding0004_0 binding0004_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate007 certificate008 (by decide)

theorem case_closed0005 : CoreExcluded (baseCore 0 0 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 0) owner_valid009
  scope009 binding0005_0 certificate009

theorem case_closed0006 : CoreExcluded (baseCore 0 0 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 0) owner_valid010
  scope010 binding0006_0 certificate010

theorem case_closed0007 : CoreExcluded (baseCore 0 0 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 0) owner_valid011
  scope011 binding0007_0 certificate011

theorem case_closed0008 : CoreExcluded (baseCore 0 0 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 0) owner_valid012
  scope012 binding0008_0 certificate012

theorem case_closed0009 : CoreExcluded (baseCore 0 0 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout013 layout014
  (layout_for_all_rows 9 layout013 layout_valid013 0 0)
  (layout_for_all_rows 9 layout014 layout_valid014 0 0)
  owner_valid013 owner_valid014 scope013 scope014
  binding0009_0 binding0009_1
  2 9 7 4 (by decide) (by decide) 3 2 (by decide)
  certificate013 certificate014 (by decide)

theorem case_closed0010 : CoreExcluded (baseCore 0 0 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout015 layout016
  (layout_for_all_rows 10 layout015 layout_valid015 0 0)
  (layout_for_all_rows 10 layout016 layout_valid016 0 0)
  owner_valid015 owner_valid016 scope015 scope016
  binding0010_0 binding0010_1
  0 6 6 2 (by decide) (by decide) 2 3 (by decide)
  certificate015 certificate016 (by decide)

theorem case_closed0011 : CoreExcluded (baseCore 0 0 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 0) owner_valid017
  scope017 binding0011_0 certificate017

theorem case_closed0012 : CoreExcluded (baseCore 0 0 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 0) owner_valid018
  scope018 binding0012_0 certificate018

theorem case_closed0013 : CoreExcluded (baseCore 0 0 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 0) owner_valid019
  scope019 binding0013_0 certificate019

theorem case_closed0014 : CoreExcluded (baseCore 0 0 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 0) owner_valid020
  scope020 binding0014_0 certificate020

theorem case_closed0015 : CoreExcluded (baseCore 0 0 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 0) owner_valid021
  scope021 binding0015_0 certificate021

theorem case_closed0016 : CoreExcluded (baseCore 0 0 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 0) owner_valid022
  scope022 binding0016_0 certificate022

theorem case_closed0017 : CoreExcluded (baseCore 0 0 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 0) owner_valid023
  scope023 binding0017_0 certificate023

theorem case_closed0018 : CoreExcluded (baseCore 0 0 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 0) owner_valid024
  scope024 binding0018_0 certificate024

theorem case_closed0019 : CoreExcluded (baseCore 0 0 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 0) owner_valid025
  scope025 binding0019_0 certificate025

theorem case_closed0020 : CoreExcluded (baseCore 0 0 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 0) owner_valid026
  scope026 binding0020_0 certificate026

theorem case_closed0021 : CoreExcluded (baseCore 0 0 21) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout027 layout028
  (layout_for_all_rows 21 layout027 layout_valid027 0 0)
  (layout_for_all_rows 21 layout028 layout_valid028 0 0)
  owner_valid027 owner_valid028 scope027 scope028
  binding0021_0 binding0021_1
  2 6 6 1 (by decide) (by decide) 3 2 (by decide)
  certificate027 certificate028 (by decide)

theorem case_closed0022 : CoreExcluded (baseCore 0 0 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout029 layout030
  (layout_for_all_rows 22 layout029 layout_valid029 0 0)
  (layout_for_all_rows 22 layout030 layout_valid030 0 0)
  owner_valid029 owner_valid030 scope029 scope030
  binding0022_0 binding0022_1
  1 5 6 1 (by decide) (by decide) 3 2 (by decide)
  certificate029 certificate030 (by decide)

theorem case_closed0023 : CoreExcluded (baseCore 0 0 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 0) owner_valid031
  scope031 binding0023_0 certificate031

theorem case_closed0024 : CoreExcluded (baseCore 0 0 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 0) owner_valid032
  scope032 binding0024_0 certificate032

theorem case_closed0025 : CoreExcluded (baseCore 0 1 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 1) owner_valid033
  scope033 binding0025_0 certificate033

theorem case_closed0026 : CoreExcluded (baseCore 0 1 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 1) owner_valid002
  scope034 binding0026_0 certificate034

theorem case_closed0027 : CoreExcluded (baseCore 0 1 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 1) owner_valid034
  scope035 binding0027_0 certificate035

theorem case_closed0028 : CoreExcluded (baseCore 0 1 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 1) owner_valid035
  scope036 binding0028_0 certificate036

theorem case_closed0029 : CoreExcluded (baseCore 0 1 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 1) owner_valid036
  scope037 binding0029_0 certificate037

theorem case_closed0030 : CoreExcluded (baseCore 0 1 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 1) owner_valid037
  scope038 binding0030_0 certificate038

theorem case_closed0031 : CoreExcluded (baseCore 0 1 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 1) owner_valid010
  scope038 binding0031_0 certificate038

theorem case_closed0032 : CoreExcluded (baseCore 0 1 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 1) owner_valid011
  scope039 binding0032_0 certificate039

theorem case_closed0033 : CoreExcluded (baseCore 0 1 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 1) owner_valid012
  scope040 binding0033_0 certificate040

theorem case_closed0034 : CoreExcluded (baseCore 0 1 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 1) owner_valid038
  scope041 binding0034_0 certificate041

theorem case_closed0035 : CoreExcluded (baseCore 0 1 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 0 1) owner_valid039
  scope041 binding0035_0 certificate041

theorem case_closed0036 : CoreExcluded (baseCore 0 1 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout040 layout041
  (layout_for_all_rows 11 layout040 layout_valid040 0 1)
  (layout_for_all_rows 11 layout041 layout_valid041 0 1)
  owner_valid040 owner_valid041 scope042 scope043
  binding0036_0 binding0036_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate042 certificate043 (by decide)

theorem case_closed0037 : CoreExcluded (baseCore 0 1 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout042 layout043
  (layout_for_all_rows 12 layout042 layout_valid042 0 1)
  (layout_for_all_rows 12 layout043 layout_valid043 0 1)
  owner_valid042 owner_valid043 scope044 scope045
  binding0037_0 binding0037_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate044 certificate045 (by decide)

theorem case_closed0038 : CoreExcluded (baseCore 0 1 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout044
  (layout_for_all_rows 13 layout044 layout_valid044 0 1) owner_valid044
  scope046 binding0038_0 certificate046

theorem case_closed0039 : CoreExcluded (baseCore 0 1 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 1) owner_valid020
  scope047 binding0039_0 certificate047

theorem case_closed0040 : CoreExcluded (baseCore 0 1 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 1) owner_valid021
  scope048 binding0040_0 certificate048

theorem case_closed0041 : CoreExcluded (baseCore 0 1 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 1) owner_valid022
  scope049 binding0041_0 certificate049

theorem case_closed0042 : CoreExcluded (baseCore 0 1 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout045 layout046
  (layout_for_all_rows 17 layout045 layout_valid045 0 1)
  (layout_for_all_rows 17 layout046 layout_valid046 0 1)
  owner_valid045 owner_valid046 scope050 scope051
  binding0042_0 binding0042_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate050 certificate051 (by decide)

theorem case_closed0043 : CoreExcluded (baseCore 0 1 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout047 layout048
  (layout_for_all_rows 18 layout047 layout_valid047 0 1)
  (layout_for_all_rows 18 layout048 layout_valid048 0 1)
  owner_valid047 owner_valid048 scope052 scope053
  binding0043_0 binding0043_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate052 certificate053 (by decide)

theorem case_closed0044 : CoreExcluded (baseCore 0 1 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout049
  (layout_for_all_rows 19 layout049 layout_valid049 0 1) owner_valid049
  scope054 binding0044_0 certificate054

theorem case_closed0045 : CoreExcluded (baseCore 0 1 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 1) owner_valid026
  scope055 binding0045_0 certificate055

theorem case_closed0046 : CoreExcluded (baseCore 0 1 21) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout050 layout051
  (layout_for_all_rows 21 layout050 layout_valid050 0 1)
  (layout_for_all_rows 21 layout051 layout_valid051 0 1)
  owner_valid050 owner_valid051 scope056 scope057
  binding0046_0 binding0046_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate056 certificate057 (by decide)

theorem case_closed0047 : CoreExcluded (baseCore 0 1 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout052 layout053
  (layout_for_all_rows 22 layout052 layout_valid052 0 1)
  (layout_for_all_rows 22 layout053 layout_valid053 0 1)
  owner_valid052 owner_valid053 scope058 scope059
  binding0047_0 binding0047_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate058 certificate059 (by decide)

theorem case_closed0048 : CoreExcluded (baseCore 0 1 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout055
  (layout_for_all_rows 23 layout054 layout_valid054 0 1)
  (layout_for_all_rows 23 layout055 layout_valid055 0 1)
  owner_valid054 owner_valid055 scope060 scope061
  binding0048_0 binding0048_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate060 certificate061 (by decide)

theorem case_closed0049 : CoreExcluded (baseCore 0 1 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout056 layout057
  (layout_for_all_rows 24 layout056 layout_valid056 0 1)
  (layout_for_all_rows 24 layout057 layout_valid057 0 1)
  owner_valid056 owner_valid057 scope062 scope063
  binding0049_0 binding0049_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate062 certificate063 (by decide)

theorem case_closed0050 : CoreExcluded (baseCore 0 2 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 2) owner_valid033
  scope064 binding0050_0 certificate064

theorem case_closed0051 : CoreExcluded (baseCore 0 2 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 2) owner_valid002
  scope065 binding0051_0 certificate065

theorem case_closed0052 : CoreExcluded (baseCore 0 2 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 2) owner_valid034
  scope066 binding0052_0 certificate066

theorem case_closed0053 : CoreExcluded (baseCore 0 2 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 2) owner_valid035
  scope067 binding0053_0 certificate067

theorem case_closed0054 : CoreExcluded (baseCore 0 2 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 2) owner_valid036
  scope068 binding0054_0 certificate068

theorem case_closed0055 : CoreExcluded (baseCore 0 2 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 2) owner_valid009
  scope069 binding0055_0 certificate069

theorem case_closed0056 : CoreExcluded (baseCore 0 2 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 2) owner_valid058
  scope069 binding0056_0 certificate069

theorem case_closed0057 : CoreExcluded (baseCore 0 2 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 0 2) owner_valid059
  scope070 binding0057_0 certificate070

theorem case_closed0058 : CoreExcluded (baseCore 0 2 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 2) owner_valid012
  scope070 binding0058_0 certificate070

theorem case_closed0059 : CoreExcluded (baseCore 0 2 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout060 layout061
  (layout_for_all_rows 9 layout060 layout_valid060 0 2)
  (layout_for_all_rows 9 layout061 layout_valid061 0 2)
  owner_valid060 owner_valid061 scope071 scope072
  binding0059_0 binding0059_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate071 certificate072 (by decide)

theorem case_closed0060 : CoreExcluded (baseCore 0 2 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout062 layout063
  (layout_for_all_rows 10 layout062 layout_valid062 0 2)
  (layout_for_all_rows 10 layout063 layout_valid063 0 2)
  owner_valid062 owner_valid063 scope073 scope074
  binding0060_0 binding0060_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate073 certificate074 (by decide)

theorem case_closed0061 : CoreExcluded (baseCore 0 2 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 2) owner_valid017
  scope075 binding0061_0 certificate075

theorem case_closed0062 : CoreExcluded (baseCore 0 2 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 2) owner_valid018
  scope076 binding0062_0 certificate076

theorem case_closed0063 : CoreExcluded (baseCore 0 2 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 2) owner_valid019
  scope077 binding0063_0 certificate077

theorem case_closed0064 : CoreExcluded (baseCore 0 2 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 2) owner_valid020
  scope078 binding0064_0 certificate078

theorem case_closed0065 : CoreExcluded (baseCore 0 2 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout065
  (layout_for_all_rows 15 layout064 layout_valid064 0 2)
  (layout_for_all_rows 15 layout065 layout_valid065 0 2)
  owner_valid064 owner_valid065 scope079 scope080
  binding0065_0 binding0065_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate079 certificate080 (by decide)

theorem case_closed0066 : CoreExcluded (baseCore 0 2 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout066 layout067
  (layout_for_all_rows 16 layout066 layout_valid066 0 2)
  (layout_for_all_rows 16 layout067 layout_valid067 0 2)
  owner_valid066 owner_valid067 scope081 scope082
  binding0066_0 binding0066_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate081 certificate082 (by decide)

theorem case_closed0067 : CoreExcluded (baseCore 0 2 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 2) owner_valid023
  scope083 binding0067_0 certificate083

theorem case_closed0068 : CoreExcluded (baseCore 0 2 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout068
  (layout_for_all_rows 18 layout068 layout_valid068 0 2) owner_valid068
  scope084 binding0068_0 certificate084

theorem case_closed0069 : CoreExcluded (baseCore 0 2 19) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout069 layout049
  (layout_for_all_rows 19 layout069 layout_valid069 0 2)
  (layout_for_all_rows 19 layout049 layout_valid049 0 2)
  owner_valid069 owner_valid049 scope085 scope086
  binding0069_0 binding0069_1
  2 5 2 5 (by decide) (by decide) 3 2 (by decide)
  certificate085 certificate086 (by decide)

theorem case_closed0070 : CoreExcluded (baseCore 0 2 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout070 layout071
  (layout_for_all_rows 20 layout070 layout_valid070 0 2)
  (layout_for_all_rows 20 layout071 layout_valid071 0 2)
  owner_valid070 owner_valid071 scope087 scope088
  binding0070_0 binding0070_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate087 certificate088 (by decide)

theorem case_closed0071 : CoreExcluded (baseCore 0 2 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout051
  (layout_for_all_rows 21 layout051 layout_valid051 0 2) owner_valid051
  scope089 binding0071_0 certificate089

theorem case_closed0072 : CoreExcluded (baseCore 0 2 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 2) owner_valid072
  scope090 binding0072_0 certificate090

theorem case_closed0073 : CoreExcluded (baseCore 0 2 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 0 2)
  (layout_for_all_rows 23 layout073 layout_valid073 0 2)
  owner_valid054 owner_valid073 scope091 scope092
  binding0073_0 binding0073_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate091 certificate092 (by decide)

theorem case_closed0074 : CoreExcluded (baseCore 0 2 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout074 layout056
  (layout_for_all_rows 24 layout074 layout_valid074 0 2)
  (layout_for_all_rows 24 layout056 layout_valid056 0 2)
  owner_valid074 owner_valid056 scope093 scope094
  binding0074_0 binding0074_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate093 certificate094 (by decide)

theorem case_closed0075 : CoreExcluded (baseCore 0 3 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 3) owner_valid033
  scope095 binding0075_0 certificate095

theorem case_closed0076 : CoreExcluded (baseCore 0 3 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout075 layout076
  (layout_for_all_rows 1 layout075 layout_valid075 0 3)
  (layout_for_all_rows 1 layout076 layout_valid076 0 3)
  owner_valid075 owner_valid076 scope096 scope097
  binding0076_0 binding0076_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate096 certificate097 (by decide)

theorem case_closed0077 : CoreExcluded (baseCore 0 3 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout003 layout004
  (layout_for_all_rows 2 layout003 layout_valid003 0 3)
  (layout_for_all_rows 2 layout004 layout_valid004 0 3)
  owner_valid003 owner_valid004 scope098 scope099
  binding0077_0 binding0077_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate098 certificate099 (by decide)

theorem case_closed0078 : CoreExcluded (baseCore 0 3 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout005
  (layout_for_all_rows 3 layout077 layout_valid077 0 3)
  (layout_for_all_rows 3 layout005 layout_valid005 0 3)
  owner_valid077 owner_valid005 scope100 scope101
  binding0078_0 binding0078_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate100 certificate101 (by decide)

theorem case_closed0079 : CoreExcluded (baseCore 0 3 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout078
  (layout_for_all_rows 4 layout007 layout_valid007 0 3)
  (layout_for_all_rows 4 layout078 layout_valid078 0 3)
  owner_valid007 owner_valid078 scope102 scope103
  binding0079_0 binding0079_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate102 certificate103 (by decide)

theorem case_closed0080 : CoreExcluded (baseCore 0 3 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 3) owner_valid009
  scope104 binding0080_0 certificate104

theorem case_closed0081 : CoreExcluded (baseCore 0 3 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 3) owner_valid010
  scope105 binding0081_0 certificate105

theorem case_closed0082 : CoreExcluded (baseCore 0 3 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 3) owner_valid011
  scope106 binding0082_0 certificate106

theorem case_closed0083 : CoreExcluded (baseCore 0 3 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 3) owner_valid012
  scope107 binding0083_0 certificate107

theorem case_closed0084 : CoreExcluded (baseCore 0 3 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 3) owner_valid038
  scope108 binding0084_0 certificate108

theorem case_closed0085 : CoreExcluded (baseCore 0 3 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 3) owner_valid079
  scope109 binding0085_0 certificate109

theorem case_closed0086 : CoreExcluded (baseCore 0 3 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 3) owner_valid017
  scope110 binding0086_0 certificate110

theorem case_closed0087 : CoreExcluded (baseCore 0 3 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 3) owner_valid018
  scope111 binding0087_0 certificate111

theorem case_closed0088 : CoreExcluded (baseCore 0 3 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 3) owner_valid019
  scope112 binding0088_0 certificate112

theorem case_closed0089 : CoreExcluded (baseCore 0 3 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 3) owner_valid020
  scope113 binding0089_0 certificate113

theorem case_closed0090 : CoreExcluded (baseCore 0 3 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 3) owner_valid021
  scope114 binding0090_0 certificate114

theorem case_closed0091 : CoreExcluded (baseCore 0 3 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 3) owner_valid022
  scope115 binding0091_0 certificate115

theorem case_closed0092 : CoreExcluded (baseCore 0 3 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout045 layout080
  (layout_for_all_rows 17 layout045 layout_valid045 0 3)
  (layout_for_all_rows 17 layout080 layout_valid080 0 3)
  owner_valid045 owner_valid080 scope116 scope117
  binding0092_0 binding0092_1
  3 5 7 0 (by decide) (by decide) 2 3 (by decide)
  certificate116 certificate117 (by decide)

theorem case_closed0093 : CoreExcluded (baseCore 0 3 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout081 layout082
  (layout_for_all_rows 18 layout081 layout_valid081 0 3)
  (layout_for_all_rows 18 layout082 layout_valid082 0 3)
  owner_valid081 owner_valid082 scope118 scope119
  binding0093_0 binding0093_1
  0 6 6 2 (by decide) (by decide) 2 3 (by decide)
  certificate118 certificate119 (by decide)

theorem case_closed0094 : CoreExcluded (baseCore 0 3 19) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout083 layout084
  (layout_for_all_rows 19 layout083 layout_valid083 0 3)
  (layout_for_all_rows 19 layout084 layout_valid084 0 3)
  owner_valid083 owner_valid084 scope120 scope121
  binding0094_0 binding0094_1
  2 5 6 0 (by decide) (by decide) 3 2 (by decide)
  certificate120 certificate121 (by decide)

theorem case_closed0095 : CoreExcluded (baseCore 0 3 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout085 layout086
  (layout_for_all_rows 20 layout085 layout_valid085 0 3)
  (layout_for_all_rows 20 layout086 layout_valid086 0 3)
  owner_valid085 owner_valid086 scope122 scope123
  binding0095_0 binding0095_1
  1 9 6 4 (by decide) (by decide) 3 2 (by decide)
  certificate122 certificate123 (by decide)

theorem case_closed0096 : CoreExcluded (baseCore 0 3 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 3) owner_valid087
  scope124 binding0096_0 certificate124

theorem case_closed0097 : CoreExcluded (baseCore 0 3 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 3) owner_valid072
  scope125 binding0097_0 certificate125

theorem case_closed0098 : CoreExcluded (baseCore 0 3 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 3) owner_valid031
  scope126 binding0098_0 certificate126

theorem case_closed0099 : CoreExcluded (baseCore 0 3 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 3) owner_valid032
  scope127 binding0099_0 certificate127

theorem block_closed000 (i : Fin 100) : CoreExcluded (caseCore (blockCase 0 i)) := by
 fin_cases i
 · exact case_closed0000
 · exact case_closed0001
 · exact case_closed0002
 · exact case_closed0003
 · exact case_closed0004
 · exact case_closed0005
 · exact case_closed0006
 · exact case_closed0007
 · exact case_closed0008
 · exact case_closed0009
 · exact case_closed0010
 · exact case_closed0011
 · exact case_closed0012
 · exact case_closed0013
 · exact case_closed0014
 · exact case_closed0015
 · exact case_closed0016
 · exact case_closed0017
 · exact case_closed0018
 · exact case_closed0019
 · exact case_closed0020
 · exact case_closed0021
 · exact case_closed0022
 · exact case_closed0023
 · exact case_closed0024
 · exact case_closed0025
 · exact case_closed0026
 · exact case_closed0027
 · exact case_closed0028
 · exact case_closed0029
 · exact case_closed0030
 · exact case_closed0031
 · exact case_closed0032
 · exact case_closed0033
 · exact case_closed0034
 · exact case_closed0035
 · exact case_closed0036
 · exact case_closed0037
 · exact case_closed0038
 · exact case_closed0039
 · exact case_closed0040
 · exact case_closed0041
 · exact case_closed0042
 · exact case_closed0043
 · exact case_closed0044
 · exact case_closed0045
 · exact case_closed0046
 · exact case_closed0047
 · exact case_closed0048
 · exact case_closed0049
 · exact case_closed0050
 · exact case_closed0051
 · exact case_closed0052
 · exact case_closed0053
 · exact case_closed0054
 · exact case_closed0055
 · exact case_closed0056
 · exact case_closed0057
 · exact case_closed0058
 · exact case_closed0059
 · exact case_closed0060
 · exact case_closed0061
 · exact case_closed0062
 · exact case_closed0063
 · exact case_closed0064
 · exact case_closed0065
 · exact case_closed0066
 · exact case_closed0067
 · exact case_closed0068
 · exact case_closed0069
 · exact case_closed0070
 · exact case_closed0071
 · exact case_closed0072
 · exact case_closed0073
 · exact case_closed0074
 · exact case_closed0075
 · exact case_closed0076
 · exact case_closed0077
 · exact case_closed0078
 · exact case_closed0079
 · exact case_closed0080
 · exact case_closed0081
 · exact case_closed0082
 · exact case_closed0083
 · exact case_closed0084
 · exact case_closed0085
 · exact case_closed0086
 · exact case_closed0087
 · exact case_closed0088
 · exact case_closed0089
 · exact case_closed0090
 · exact case_closed0091
 · exact case_closed0092
 · exact case_closed0093
 · exact case_closed0094
 · exact case_closed0095
 · exact case_closed0096
 · exact case_closed0097
 · exact case_closed0098
 · exact case_closed0099
end PricingC.GIsomorphic