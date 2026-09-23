import PricingC.GCoreExcluded
import PricingC.GBindings019
import PricingC.GScopeChecks008
import PricingC.GScopeChecks009
import PricingC.GScopeChecks010
import PricingC.GScopeChecks012
import PricingC.GScopeChecks013
import PricingC.GScopeChecks014
import PricingC.GScopeChecks015
import PricingC.GScopeChecks025
import PricingC.GScopeChecks027
import PricingC.GScopeChecks028
import PricingC.GScopeChecks030
import PricingC.GScopeChecks031
import PricingC.GScopeChecks036
import PricingC.GScopeChecks037
import PricingC.GScopeChecks044
import PricingC.GScopeChecks045
import PricingC.GScopeChecks046
import PricingC.GScopeChecks047
import PricingC.GLayoutChecks000
import PricingC.GLayoutChecks001
import PricingC.GLayoutChecks002
import PricingC.GLayoutChecks003
import PricingC.GLayoutChecks004
import PricingC.GLayoutChecks005
import PricingC.GLayoutChecks006

namespace PricingC.GIsomorphic
open PricingIntegration.GCoreConsumer

theorem case_closed1900 : CoreExcluded (baseCore 1 4 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout001 layout088
  (layout_for_all_rows 0 layout001 layout_valid001 1 4)
  (layout_for_all_rows 0 layout088 layout_valid088 1 4)
  owner_valid001 owner_valid088 scope163 scope129
  binding1900_0 binding1900_1
  0 9 0 9 (by decide) (by decide) 3 2 (by decide)
  certificate708 certificate129 (by decide)

theorem case_closed1901 : CoreExcluded (baseCore 1 4 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout076 layout089
  (layout_for_all_rows 1 layout076 layout_valid076 1 4)
  (layout_for_all_rows 1 layout089 layout_valid089 1 4)
  owner_valid076 owner_valid089 scope161 scope131
  binding1901_0 binding1901_1
  0 9 0 9 (by decide) (by decide) 2 3 (by decide)
  certificate161 certificate131 (by decide)

theorem case_closed1902 : CoreExcluded (baseCore 1 4 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 4) owner_valid003
  scope132 binding1902_0 certificate132

theorem case_closed1903 : CoreExcluded (baseCore 1 4 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout006
  (layout_for_all_rows 3 layout077 layout_valid077 1 4)
  (layout_for_all_rows 3 layout006 layout_valid006 1 4)
  owner_valid077 owner_valid006 scope133 scope529
  binding1903_0 binding1903_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate133 certificate709 (by decide)

theorem case_closed1904 : CoreExcluded (baseCore 1 4 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout078
  (layout_for_all_rows 4 layout007 layout_valid007 1 4)
  (layout_for_all_rows 4 layout078 layout_valid078 1 4)
  owner_valid007 owner_valid078 scope135 scope480
  binding1904_0 binding1904_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate135 certificate710 (by decide)

theorem case_closed1905 : CoreExcluded (baseCore 1 4 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout108 layout109
  (layout_for_all_rows 5 layout108 layout_valid108 1 4)
  (layout_for_all_rows 5 layout109 layout_valid109 1 4)
  owner_valid108 owner_valid109 scope186 scope313
  binding1905_0 binding1905_1
  4 5 4 5 (by decide) (by decide) 2 3 (by decide)
  certificate711 certificate712 (by decide)

theorem case_closed1906 : CoreExcluded (baseCore 1 4 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout110 layout111
  (layout_for_all_rows 6 layout110 layout_valid110 1 4)
  (layout_for_all_rows 6 layout111 layout_valid111 1 4)
  owner_valid110 owner_valid111 scope184 scope475
  binding1906_0 binding1906_1
  4 5 4 5 (by decide) (by decide) 3 2 (by decide)
  certificate713 certificate714 (by decide)

theorem case_closed1907 : CoreExcluded (baseCore 1 4 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 4) owner_valid059
  scope142 binding1907_0 certificate142

theorem case_closed1908 : CoreExcluded (baseCore 1 4 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 4) owner_valid134
  scope141 binding1908_0 certificate141

theorem case_closed1909 : CoreExcluded (baseCore 1 4 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 1 4) owner_valid136
  scope144 binding1909_0 certificate144

theorem case_closed1910 : CoreExcluded (baseCore 1 4 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 4) owner_valid039
  scope143 binding1910_0 certificate143

theorem case_closed1911 : CoreExcluded (baseCore 1 4 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 4) owner_valid149
  scope146 binding1911_0 certificate146

theorem case_closed1912 : CoreExcluded (baseCore 1 4 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 1 4) owner_valid042
  scope145 binding1912_0 certificate145

theorem case_closed1913 : CoreExcluded (baseCore 1 4 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 4) owner_valid137
  scope147 binding1913_0 certificate147

theorem case_closed1914 : CoreExcluded (baseCore 1 4 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 4) owner_valid138
  scope148 binding1914_0 certificate148

theorem case_closed1915 : CoreExcluded (baseCore 1 4 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 4) owner_valid064
  scope149 binding1915_0 certificate149

theorem case_closed1916 : CoreExcluded (baseCore 1 4 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 4) owner_valid180
  scope150 binding1916_0 certificate150

theorem case_closed1917 : CoreExcluded (baseCore 1 4 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 1 4) owner_valid129
  scope151 binding1917_0 certificate151

theorem case_closed1918 : CoreExcluded (baseCore 1 4 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 1 4) owner_valid130
  scope152 binding1918_0 certificate152

theorem case_closed1919 : CoreExcluded (baseCore 1 4 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 4) owner_valid131
  scope153 binding1919_0 certificate153

theorem case_closed1920 : CoreExcluded (baseCore 1 4 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 4) owner_valid070
  scope154 binding1920_0 certificate154

theorem case_closed1921 : CoreExcluded (baseCore 1 4 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 4) owner_valid050
  scope155 binding1921_0 certificate155

theorem case_closed1922 : CoreExcluded (baseCore 1 4 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 4) owner_valid052
  scope156 binding1922_0 certificate156

theorem case_closed1923 : CoreExcluded (baseCore 1 4 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 1 4)
  (layout_for_all_rows 23 layout073 layout_valid073 1 4)
  owner_valid054 owner_valid073 scope430 scope580
  binding1923_0 binding1923_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate445 certificate715 (by decide)

theorem case_closed1924 : CoreExcluded (baseCore 1 4 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout074 layout057
  (layout_for_all_rows 24 layout074 layout_valid074 1 4)
  (layout_for_all_rows 24 layout057 layout_valid057 1 4)
  owner_valid074 owner_valid057 scope431 scope581
  binding1924_0 binding1924_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate716 certificate717 (by decide)

theorem case_closed1925 : CoreExcluded (baseCore 1 5 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout001 layout088
  (layout_for_all_rows 0 layout001 layout_valid001 1 5)
  (layout_for_all_rows 0 layout088 layout_valid088 1 5)
  owner_valid001 owner_valid088 scope304 scope161
  binding1925_0 binding1925_1
  4 5 4 5 (by decide) (by decide) 3 2 (by decide)
  certificate718 certificate719 (by decide)

theorem case_closed1926 : CoreExcluded (baseCore 1 5 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout076 layout089
  (layout_for_all_rows 1 layout076 layout_valid076 1 5)
  (layout_for_all_rows 1 layout089 layout_valid089 1 5)
  owner_valid076 owner_valid089 scope297 scope480
  binding1926_0 binding1926_1
  4 5 4 5 (by decide) (by decide) 2 3 (by decide)
  certificate720 certificate721 (by decide)

theorem case_closed1927 : CoreExcluded (baseCore 1 5 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 5) owner_valid034
  scope582 binding1927_0 certificate722

theorem case_closed1928 : CoreExcluded (baseCore 1 5 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout077 layout006
  (layout_for_all_rows 3 layout077 layout_valid077 1 5)
  (layout_for_all_rows 3 layout006 layout_valid006 1 5)
  owner_valid077 owner_valid006 scope439 scope583
  binding1928_0 binding1928_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate723 certificate724 (by decide)

theorem case_closed1929 : CoreExcluded (baseCore 1 5 4) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout007 layout078
  (layout_for_all_rows 4 layout007 layout_valid007 1 5)
  (layout_for_all_rows 4 layout078 layout_valid078 1 5)
  owner_valid007 owner_valid078 scope440 scope584
  binding1929_0 binding1929_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate463 certificate725 (by decide)

theorem case_closed1930 : CoreExcluded (baseCore 1 5 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout108 layout109
  (layout_for_all_rows 5 layout108 layout_valid108 1 5)
  (layout_for_all_rows 5 layout109 layout_valid109 1 5)
  owner_valid108 owner_valid109 scope139 scope172
  binding1930_0 binding1930_1
  0 9 0 9 (by decide) (by decide) 2 3 (by decide)
  certificate139 certificate172 (by decide)

theorem case_closed1931 : CoreExcluded (baseCore 1 5 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout110 layout111
  (layout_for_all_rows 6 layout110 layout_valid110 1 5)
  (layout_for_all_rows 6 layout111 layout_valid111 1 5)
  owner_valid110 owner_valid111 scope137 scope174
  binding1931_0 binding1931_1
  0 9 0 9 (by decide) (by decide) 3 2 (by decide)
  certificate726 certificate174 (by decide)

theorem case_closed1932 : CoreExcluded (baseCore 1 5 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 5) owner_valid011
  scope585 binding1932_0 certificate727

theorem case_closed1933 : CoreExcluded (baseCore 1 5 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 5) owner_valid012
  scope586 binding1933_0 certificate728

theorem case_closed1934 : CoreExcluded (baseCore 1 5 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 5) owner_valid038
  scope465 binding1934_0 certificate494

theorem case_closed1935 : CoreExcluded (baseCore 1 5 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 5) owner_valid079
  scope464 binding1935_0 certificate493

theorem case_closed1936 : CoreExcluded (baseCore 1 5 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 5) owner_valid017
  scope466 binding1936_0 certificate495

theorem case_closed1937 : CoreExcluded (baseCore 1 5 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 5) owner_valid018
  scope587 binding1937_0 certificate729

theorem case_closed1938 : CoreExcluded (baseCore 1 5 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 5) owner_valid019
  scope588 binding1938_0 certificate730

theorem case_closed1939 : CoreExcluded (baseCore 1 5 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 5) owner_valid020
  scope589 binding1939_0 certificate731

theorem case_closed1940 : CoreExcluded (baseCore 1 5 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 5) owner_valid021
  scope462 binding1940_0 certificate491

theorem case_closed1941 : CoreExcluded (baseCore 1 5 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 5) owner_valid022
  scope463 binding1941_0 certificate492

theorem case_closed1942 : CoreExcluded (baseCore 1 5 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 5) owner_valid023
  scope590 binding1942_0 certificate732

theorem case_closed1943 : CoreExcluded (baseCore 1 5 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 5) owner_valid024
  scope591 binding1943_0 certificate733

theorem case_closed1944 : CoreExcluded (baseCore 1 5 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 5) owner_valid025
  scope467 binding1944_0 certificate496

theorem case_closed1945 : CoreExcluded (baseCore 1 5 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 5) owner_valid026
  scope468 binding1945_0 certificate497

theorem case_closed1946 : CoreExcluded (baseCore 1 5 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 5) owner_valid087
  scope469 binding1946_0 certificate498

theorem case_closed1947 : CoreExcluded (baseCore 1 5 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 5) owner_valid072
  scope592 binding1947_0 certificate734

theorem case_closed1948 : CoreExcluded (baseCore 1 5 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 1 5)
  (layout_for_all_rows 23 layout073 layout_valid073 1 5)
  owner_valid054 owner_valid073 scope207 scope593
  binding1948_0 binding1948_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate207 certificate735 (by decide)

theorem case_closed1949 : CoreExcluded (baseCore 1 5 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout074 layout057
  (layout_for_all_rows 24 layout074 layout_valid074 1 5)
  (layout_for_all_rows 24 layout057 layout_valid057 1 5)
  owner_valid074 owner_valid057 scope209 scope315
  binding1949_0 binding1949_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate209 certificate736 (by decide)

theorem case_closed1950 : CoreExcluded (baseCore 1 6 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 6) owner_valid033
  scope503 binding1950_0 certificate590

theorem case_closed1951 : CoreExcluded (baseCore 1 6 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 6) owner_valid002
  scope502 binding1951_0 certificate589

theorem case_closed1952 : CoreExcluded (baseCore 1 6 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 6) owner_valid034
  scope504 binding1952_0 certificate591

theorem case_closed1953 : CoreExcluded (baseCore 1 6 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 6) owner_valid035
  scope594 binding1953_0 certificate737

theorem case_closed1954 : CoreExcluded (baseCore 1 6 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 6) owner_valid036
  scope505 binding1954_0 certificate592

theorem case_closed1955 : CoreExcluded (baseCore 1 6 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 6) owner_valid009
  scope595 binding1955_0 certificate738

theorem case_closed1956 : CoreExcluded (baseCore 1 6 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 6) owner_valid010
  scope596 binding1956_0 certificate739

theorem case_closed1957 : CoreExcluded (baseCore 1 6 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 6) owner_valid059
  scope219 binding1957_0 certificate219

theorem case_closed1958 : CoreExcluded (baseCore 1 6 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 6) owner_valid134
  scope218 binding1958_0 certificate218

theorem case_closed1959 : CoreExcluded (baseCore 1 6 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 6) owner_valid038
  scope254 binding1959_0 certificate254

theorem case_closed1960 : CoreExcluded (baseCore 1 6 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 6) owner_valid039
  scope220 binding1960_0 certificate220

theorem case_closed1961 : CoreExcluded (baseCore 1 6 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 6) owner_valid149
  scope223 binding1961_0 certificate223

theorem case_closed1962 : CoreExcluded (baseCore 1 6 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 6) owner_valid018
  scope255 binding1962_0 certificate255

theorem case_closed1963 : CoreExcluded (baseCore 1 6 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 6) owner_valid137
  scope224 binding1963_0 certificate224

theorem case_closed1964 : CoreExcluded (baseCore 1 6 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 6) owner_valid138
  scope225 binding1964_0 certificate225

theorem case_closed1965 : CoreExcluded (baseCore 1 6 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 6) owner_valid064
  scope226 binding1965_0 certificate226

theorem case_closed1966 : CoreExcluded (baseCore 1 6 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 6) owner_valid022
  scope408 binding1966_0 certificate415

theorem case_closed1967 : CoreExcluded (baseCore 1 6 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 6) owner_valid023
  scope506 binding1967_0 certificate593

theorem case_closed1968 : CoreExcluded (baseCore 1 6 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 1 6) owner_valid130
  scope229 binding1968_0 certificate229

theorem case_closed1969 : CoreExcluded (baseCore 1 6 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 6) owner_valid131
  scope230 binding1969_0 certificate230

theorem case_closed1970 : CoreExcluded (baseCore 1 6 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 6) owner_valid070
  scope231 binding1970_0 certificate231

theorem case_closed1971 : CoreExcluded (baseCore 1 6 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 6) owner_valid050
  scope232 binding1971_0 certificate232

theorem case_closed1972 : CoreExcluded (baseCore 1 6 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 6) owner_valid052
  scope233 binding1972_0 certificate233

theorem case_closed1973 : CoreExcluded (baseCore 1 6 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 6) owner_valid031
  scope597 binding1973_0 certificate740

theorem case_closed1974 : CoreExcluded (baseCore 1 6 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 6) owner_valid032
  scope598 binding1974_0 certificate741

theorem case_closed1975 : CoreExcluded (baseCore 1 7 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 7) owner_valid033
  scope599 binding1975_0 certificate742

theorem case_closed1976 : CoreExcluded (baseCore 1 7 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 7) owner_valid002
  scope600 binding1976_0 certificate743

theorem case_closed1977 : CoreExcluded (baseCore 1 7 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 7) owner_valid034
  scope601 binding1977_0 certificate744

theorem case_closed1978 : CoreExcluded (baseCore 1 7 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 7) owner_valid035
  scope602 binding1978_0 certificate745

theorem case_closed1979 : CoreExcluded (baseCore 1 7 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 7) owner_valid036
  scope603 binding1979_0 certificate746

theorem case_closed1980 : CoreExcluded (baseCore 1 7 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 7) owner_valid009
  scope490 binding1980_0 certificate577

theorem case_closed1981 : CoreExcluded (baseCore 1 7 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 7) owner_valid010
  scope491 binding1981_0 certificate578

theorem case_closed1982 : CoreExcluded (baseCore 1 7 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 7) owner_valid011
  scope498 binding1982_0 certificate585

theorem case_closed1983 : CoreExcluded (baseCore 1 7 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 7) owner_valid012
  scope604 binding1983_0 certificate747

theorem case_closed1984 : CoreExcluded (baseCore 1 7 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 7) owner_valid038
  scope605 binding1984_0 certificate748

theorem case_closed1985 : CoreExcluded (baseCore 1 7 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 7) owner_valid079
  scope499 binding1985_0 certificate586

theorem case_closed1986 : CoreExcluded (baseCore 1 7 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 7) owner_valid017
  scope606 binding1986_0 certificate749

theorem case_closed1987 : CoreExcluded (baseCore 1 7 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 7) owner_valid018
  scope607 binding1987_0 certificate750

theorem case_closed1988 : CoreExcluded (baseCore 1 7 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 7) owner_valid019
  scope492 binding1988_0 certificate579

theorem case_closed1989 : CoreExcluded (baseCore 1 7 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 7) owner_valid020
  scope493 binding1989_0 certificate580

theorem case_closed1990 : CoreExcluded (baseCore 1 7 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 7) owner_valid021
  scope494 binding1990_0 certificate581

theorem case_closed1991 : CoreExcluded (baseCore 1 7 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 7) owner_valid022
  scope495 binding1991_0 certificate582

theorem case_closed1992 : CoreExcluded (baseCore 1 7 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 7) owner_valid023
  scope496 binding1992_0 certificate583

theorem case_closed1993 : CoreExcluded (baseCore 1 7 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 7) owner_valid024
  scope497 binding1993_0 certificate584

theorem case_closed1994 : CoreExcluded (baseCore 1 7 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 7) owner_valid025
  scope608 binding1994_0 certificate751

theorem case_closed1995 : CoreExcluded (baseCore 1 7 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 7) owner_valid026
  scope609 binding1995_0 certificate752

theorem case_closed1996 : CoreExcluded (baseCore 1 7 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 7) owner_valid087
  scope610 binding1996_0 certificate753

theorem case_closed1997 : CoreExcluded (baseCore 1 7 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 7) owner_valid072
  scope500 binding1997_0 certificate587

theorem case_closed1998 : CoreExcluded (baseCore 1 7 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 7) owner_valid031
  scope501 binding1998_0 certificate588

theorem case_closed1999 : CoreExcluded (baseCore 1 7 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 7) owner_valid032
  scope611 binding1999_0 certificate754

theorem block_closed019 (i : Fin 100) : CoreExcluded (caseCore (blockCase 19 i)) := by
 fin_cases i
 · exact case_closed1900
 · exact case_closed1901
 · exact case_closed1902
 · exact case_closed1903
 · exact case_closed1904
 · exact case_closed1905
 · exact case_closed1906
 · exact case_closed1907
 · exact case_closed1908
 · exact case_closed1909
 · exact case_closed1910
 · exact case_closed1911
 · exact case_closed1912
 · exact case_closed1913
 · exact case_closed1914
 · exact case_closed1915
 · exact case_closed1916
 · exact case_closed1917
 · exact case_closed1918
 · exact case_closed1919
 · exact case_closed1920
 · exact case_closed1921
 · exact case_closed1922
 · exact case_closed1923
 · exact case_closed1924
 · exact case_closed1925
 · exact case_closed1926
 · exact case_closed1927
 · exact case_closed1928
 · exact case_closed1929
 · exact case_closed1930
 · exact case_closed1931
 · exact case_closed1932
 · exact case_closed1933
 · exact case_closed1934
 · exact case_closed1935
 · exact case_closed1936
 · exact case_closed1937
 · exact case_closed1938
 · exact case_closed1939
 · exact case_closed1940
 · exact case_closed1941
 · exact case_closed1942
 · exact case_closed1943
 · exact case_closed1944
 · exact case_closed1945
 · exact case_closed1946
 · exact case_closed1947
 · exact case_closed1948
 · exact case_closed1949
 · exact case_closed1950
 · exact case_closed1951
 · exact case_closed1952
 · exact case_closed1953
 · exact case_closed1954
 · exact case_closed1955
 · exact case_closed1956
 · exact case_closed1957
 · exact case_closed1958
 · exact case_closed1959
 · exact case_closed1960
 · exact case_closed1961
 · exact case_closed1962
 · exact case_closed1963
 · exact case_closed1964
 · exact case_closed1965
 · exact case_closed1966
 · exact case_closed1967
 · exact case_closed1968
 · exact case_closed1969
 · exact case_closed1970
 · exact case_closed1971
 · exact case_closed1972
 · exact case_closed1973
 · exact case_closed1974
 · exact case_closed1975
 · exact case_closed1976
 · exact case_closed1977
 · exact case_closed1978
 · exact case_closed1979
 · exact case_closed1980
 · exact case_closed1981
 · exact case_closed1982
 · exact case_closed1983
 · exact case_closed1984
 · exact case_closed1985
 · exact case_closed1986
 · exact case_closed1987
 · exact case_closed1988
 · exact case_closed1989
 · exact case_closed1990
 · exact case_closed1991
 · exact case_closed1992
 · exact case_closed1993
 · exact case_closed1994
 · exact case_closed1995
 · exact case_closed1996
 · exact case_closed1997
 · exact case_closed1998
 · exact case_closed1999
end PricingC.GIsomorphic