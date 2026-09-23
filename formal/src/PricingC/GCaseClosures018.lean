import PricingC.GCoreExcluded
import PricingC.GBindings018
import PricingC.GScopeChecks000
import PricingC.GScopeChecks001
import PricingC.GScopeChecks002
import PricingC.GScopeChecks003
import PricingC.GScopeChecks004
import PricingC.GScopeChecks005
import PricingC.GScopeChecks006
import PricingC.GScopeChecks007
import PricingC.GScopeChecks024
import PricingC.GScopeChecks025
import PricingC.GScopeChecks026
import PricingC.GScopeChecks027
import PricingC.GScopeChecks028
import PricingC.GScopeChecks029
import PricingC.GScopeChecks030
import PricingC.GScopeChecks034
import PricingC.GScopeChecks042
import PricingC.GScopeChecks043
import PricingC.GScopeChecks044
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

theorem case_closed1800 : CoreExcluded (baseCore 1 0 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 0) owner_valid033
  scope426 binding1800_0 certificate441

theorem case_closed1801 : CoreExcluded (baseCore 1 0 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 0) owner_valid002
  scope425 binding1801_0 certificate440

theorem case_closed1802 : CoreExcluded (baseCore 1 0 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 0) owner_valid034
  scope552 binding1802_0 certificate677

theorem case_closed1803 : CoreExcluded (baseCore 1 0 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 0) owner_valid035
  scope427 binding1803_0 certificate442

theorem case_closed1804 : CoreExcluded (baseCore 1 0 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 0) owner_valid036
  scope428 binding1804_0 certificate443

theorem case_closed1805 : CoreExcluded (baseCore 1 0 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 1 0) owner_valid037
  scope010 binding1805_0 certificate010

theorem case_closed1806 : CoreExcluded (baseCore 1 0 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 0) owner_valid010
  scope429 binding1806_0 certificate444

theorem case_closed1807 : CoreExcluded (baseCore 1 0 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 0) owner_valid011
  scope553 binding1807_0 certificate678

theorem case_closed1808 : CoreExcluded (baseCore 1 0 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 0) owner_valid012
  scope554 binding1808_0 certificate679

theorem case_closed1809 : CoreExcluded (baseCore 1 0 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout136 layout061
  (layout_for_all_rows 9 layout136 layout_valid136 1 0)
  (layout_for_all_rows 9 layout061 layout_valid061 1 0)
  owner_valid136 owner_valid061 scope400 scope555
  binding1809_0 binding1809_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate680 certificate681 (by decide)

theorem case_closed1810 : CoreExcluded (baseCore 1 0 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout062 layout198
  (layout_for_all_rows 10 layout062 layout_valid062 1 0)
  (layout_for_all_rows 10 layout198 layout_valid198 1 0)
  owner_valid062 owner_valid198 scope079 scope405
  binding1810_0 binding1810_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate079 certificate411 (by decide)

theorem case_closed1811 : CoreExcluded (baseCore 1 0 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 0) owner_valid017
  scope084 binding1811_0 certificate084

theorem case_closed1812 : CoreExcluded (baseCore 1 0 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 1 0) owner_valid042
  scope017 binding1812_0 certificate017

theorem case_closed1813 : CoreExcluded (baseCore 1 0 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 0) owner_valid137
  scope019 binding1813_0 certificate019

theorem case_closed1814 : CoreExcluded (baseCore 1 0 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 0) owner_valid020
  scope433 binding1814_0 certificate451

theorem case_closed1815 : CoreExcluded (baseCore 1 0 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 0) owner_valid064
  scope021 binding1815_0 certificate021

theorem case_closed1816 : CoreExcluded (baseCore 1 0 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 0) owner_valid180
  scope022 binding1816_0 certificate022

theorem case_closed1817 : CoreExcluded (baseCore 1 0 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 0) owner_valid023
  scope556 binding1817_0 certificate682

theorem case_closed1818 : CoreExcluded (baseCore 1 0 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 0) owner_valid024
  scope557 binding1818_0 certificate683

theorem case_closed1819 : CoreExcluded (baseCore 1 0 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 0) owner_valid131
  scope025 binding1819_0 certificate025

theorem case_closed1820 : CoreExcluded (baseCore 1 0 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 0) owner_valid070
  scope026 binding1820_0 certificate026

theorem case_closed1821 : CoreExcluded (baseCore 1 0 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout051
  (layout_for_all_rows 21 layout051 layout_valid051 1 0) owner_valid051
  scope558 binding1821_0 certificate684

theorem case_closed1822 : CoreExcluded (baseCore 1 0 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 0) owner_valid072
  scope559 binding1822_0 certificate685

theorem case_closed1823 : CoreExcluded (baseCore 1 0 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 1 0) owner_valid054
  scope031 binding1823_0 certificate031

theorem case_closed1824 : CoreExcluded (baseCore 1 0 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 0) owner_valid074
  scope032 binding1824_0 certificate032

theorem case_closed1825 : CoreExcluded (baseCore 1 1 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 1) owner_valid187
  scope033 binding1825_0 certificate033

theorem case_closed1826 : CoreExcluded (baseCore 1 1 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 1) owner_valid002
  scope436 binding1826_0 certificate456

theorem case_closed1827 : CoreExcluded (baseCore 1 1 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 1) owner_valid003
  scope035 binding1827_0 certificate035

theorem case_closed1828 : CoreExcluded (baseCore 1 1 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 1) owner_valid077
  scope036 binding1828_0 certificate036

theorem case_closed1829 : CoreExcluded (baseCore 1 1 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 1) owner_valid007
  scope037 binding1829_0 certificate037

theorem case_closed1830 : CoreExcluded (baseCore 1 1 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 1) owner_valid009
  scope441 binding1830_0 certificate465

theorem case_closed1831 : CoreExcluded (baseCore 1 1 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 1) owner_valid010
  scope442 binding1831_0 certificate466

theorem case_closed1832 : CoreExcluded (baseCore 1 1 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 1) owner_valid011
  scope450 binding1832_0 certificate474

theorem case_closed1833 : CoreExcluded (baseCore 1 1 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 1) owner_valid012
  scope449 binding1833_0 certificate473

theorem case_closed1834 : CoreExcluded (baseCore 1 1 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 1) owner_valid038
  scope452 binding1834_0 certificate476

theorem case_closed1835 : CoreExcluded (baseCore 1 1 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 1) owner_valid079
  scope451 binding1835_0 certificate475

theorem case_closed1836 : CoreExcluded (baseCore 1 1 11) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout040 layout041
  (layout_for_all_rows 11 layout040 layout_valid040 1 1)
  (layout_for_all_rows 11 layout041 layout_valid041 1 1)
  owner_valid040 owner_valid041 scope042 scope560
  binding1836_0 binding1836_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate042 certificate686 (by decide)

theorem case_closed1837 : CoreExcluded (baseCore 1 1 12) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout042 layout043
  (layout_for_all_rows 12 layout042 layout_valid042 1 1)
  (layout_for_all_rows 12 layout043 layout_valid043 1 1)
  owner_valid042 owner_valid043 scope044 scope561
  binding1837_0 binding1837_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate044 certificate687 (by decide)

theorem case_closed1838 : CoreExcluded (baseCore 1 1 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 1) owner_valid019
  scope443 binding1838_0 certificate467

theorem case_closed1839 : CoreExcluded (baseCore 1 1 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 1) owner_valid020
  scope444 binding1839_0 certificate468

theorem case_closed1840 : CoreExcluded (baseCore 1 1 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 1) owner_valid021
  scope445 binding1840_0 certificate469

theorem case_closed1841 : CoreExcluded (baseCore 1 1 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 1) owner_valid022
  scope446 binding1841_0 certificate470

theorem case_closed1842 : CoreExcluded (baseCore 1 1 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 1) owner_valid023
  scope447 binding1842_0 certificate471

theorem case_closed1843 : CoreExcluded (baseCore 1 1 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 1) owner_valid024
  scope448 binding1843_0 certificate472

theorem case_closed1844 : CoreExcluded (baseCore 1 1 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout195
  (layout_for_all_rows 19 layout195 layout_valid195 1 1) owner_valid195
  scope054 binding1844_0 certificate054

theorem case_closed1845 : CoreExcluded (baseCore 1 1 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 1) owner_valid070
  scope055 binding1845_0 certificate055

theorem case_closed1846 : CoreExcluded (baseCore 1 1 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 1) owner_valid087
  scope454 binding1846_0 certificate481

theorem case_closed1847 : CoreExcluded (baseCore 1 1 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 1) owner_valid072
  scope455 binding1847_0 certificate482

theorem case_closed1848 : CoreExcluded (baseCore 1 1 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 1) owner_valid031
  scope456 binding1848_0 certificate483

theorem case_closed1849 : CoreExcluded (baseCore 1 1 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 1) owner_valid032
  scope457 binding1849_0 certificate484

theorem case_closed1850 : CoreExcluded (baseCore 1 2 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 2) owner_valid033
  scope562 binding1850_0 certificate688

theorem case_closed1851 : CoreExcluded (baseCore 1 2 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 2) owner_valid075
  scope065 binding1851_0 certificate065

theorem case_closed1852 : CoreExcluded (baseCore 1 2 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 2) owner_valid003
  scope066 binding1852_0 certificate066

theorem case_closed1853 : CoreExcluded (baseCore 1 2 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 2) owner_valid077
  scope067 binding1853_0 certificate067

theorem case_closed1854 : CoreExcluded (baseCore 1 2 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 2) owner_valid007
  scope068 binding1854_0 certificate068

theorem case_closed1855 : CoreExcluded (baseCore 1 2 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 2) owner_valid009
  scope563 binding1855_0 certificate689

theorem case_closed1856 : CoreExcluded (baseCore 1 2 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 2) owner_valid010
  scope564 binding1856_0 certificate690

theorem case_closed1857 : CoreExcluded (baseCore 1 2 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 2) owner_valid011
  scope565 binding1857_0 certificate691

theorem case_closed1858 : CoreExcluded (baseCore 1 2 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 2) owner_valid012
  scope392 binding1858_0 certificate393

theorem case_closed1859 : CoreExcluded (baseCore 1 2 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 2) owner_valid038
  scope566 binding1859_0 certificate692

theorem case_closed1860 : CoreExcluded (baseCore 1 2 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 2) owner_valid079
  scope567 binding1860_0 certificate693

theorem case_closed1861 : CoreExcluded (baseCore 1 2 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 2) owner_valid017
  scope394 binding1861_0 certificate395

theorem case_closed1862 : CoreExcluded (baseCore 1 2 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 2) owner_valid018
  scope393 binding1862_0 certificate394

theorem case_closed1863 : CoreExcluded (baseCore 1 2 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 2) owner_valid019
  scope568 binding1863_0 certificate694

theorem case_closed1864 : CoreExcluded (baseCore 1 2 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 2) owner_valid020
  scope569 binding1864_0 certificate695

theorem case_closed1865 : CoreExcluded (baseCore 1 2 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout065
  (layout_for_all_rows 15 layout064 layout_valid064 1 2)
  (layout_for_all_rows 15 layout065 layout_valid065 1 2)
  owner_valid064 owner_valid065 scope079 scope570
  binding1865_0 binding1865_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate079 certificate696 (by decide)

theorem case_closed1866 : CoreExcluded (baseCore 1 2 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout066 layout067
  (layout_for_all_rows 16 layout066 layout_valid066 1 2)
  (layout_for_all_rows 16 layout067 layout_valid067 1 2)
  owner_valid066 owner_valid067 scope081 scope424
  binding1866_0 binding1866_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate081 certificate697 (by decide)

theorem case_closed1867 : CoreExcluded (baseCore 1 2 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 2) owner_valid023
  scope390 binding1867_0 certificate391

theorem case_closed1868 : CoreExcluded (baseCore 1 2 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 2) owner_valid024
  scope391 binding1868_0 certificate392

theorem case_closed1869 : CoreExcluded (baseCore 1 2 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 2) owner_valid025
  scope395 binding1869_0 certificate396

theorem case_closed1870 : CoreExcluded (baseCore 1 2 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 2) owner_valid026
  scope571 binding1870_0 certificate698

theorem case_closed1871 : CoreExcluded (baseCore 1 2 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout184
  (layout_for_all_rows 21 layout184 layout_valid184 1 2) owner_valid184
  scope089 binding1871_0 certificate089

theorem case_closed1872 : CoreExcluded (baseCore 1 2 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 2) owner_valid052
  scope090 binding1872_0 certificate090

theorem case_closed1873 : CoreExcluded (baseCore 1 2 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 2) owner_valid031
  scope398 binding1873_0 certificate399

theorem case_closed1874 : CoreExcluded (baseCore 1 2 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 2) owner_valid032
  scope399 binding1874_0 certificate400

theorem case_closed1875 : CoreExcluded (baseCore 1 3 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 3) owner_valid033
  scope572 binding1875_0 certificate699

theorem case_closed1876 : CoreExcluded (baseCore 1 3 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 3) owner_valid002
  scope412 binding1876_0 certificate420

theorem case_closed1877 : CoreExcluded (baseCore 1 3 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 3) owner_valid034
  scope413 binding1877_0 certificate421

theorem case_closed1878 : CoreExcluded (baseCore 1 3 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 3) owner_valid035
  scope414 binding1878_0 certificate422

theorem case_closed1879 : CoreExcluded (baseCore 1 3 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 3) owner_valid036
  scope415 binding1879_0 certificate423

theorem case_closed1880 : CoreExcluded (baseCore 1 3 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 3) owner_valid009
  scope418 binding1880_0 certificate430

theorem case_closed1881 : CoreExcluded (baseCore 1 3 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 1 3) owner_valid058
  scope104 binding1881_0 certificate104

theorem case_closed1882 : CoreExcluded (baseCore 1 3 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout059
  (layout_for_all_rows 7 layout059 layout_valid059 1 3) owner_valid059
  scope107 binding1882_0 certificate107

theorem case_closed1883 : CoreExcluded (baseCore 1 3 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 3) owner_valid012
  scope046 binding1883_0 certificate046

theorem case_closed1884 : CoreExcluded (baseCore 1 3 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 3) owner_valid038
  scope573 binding1884_0 certificate700

theorem case_closed1885 : CoreExcluded (baseCore 1 3 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 3) owner_valid079
  scope574 binding1885_0 certificate701

theorem case_closed1886 : CoreExcluded (baseCore 1 3 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 3) owner_valid149
  scope111 binding1886_0 certificate111

theorem case_closed1887 : CoreExcluded (baseCore 1 3 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 1 3) owner_valid042
  scope110 binding1887_0 certificate110

theorem case_closed1888 : CoreExcluded (baseCore 1 3 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 3) owner_valid019
  scope575 binding1888_0 certificate702

theorem case_closed1889 : CoreExcluded (baseCore 1 3 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 3) owner_valid020
  scope576 binding1889_0 certificate703

theorem case_closed1890 : CoreExcluded (baseCore 1 3 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 3) owner_valid021
  scope416 binding1890_0 certificate424

theorem case_closed1891 : CoreExcluded (baseCore 1 3 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 3) owner_valid180
  scope115 binding1891_0 certificate115

theorem case_closed1892 : CoreExcluded (baseCore 1 3 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 1 3)
  (layout_for_all_rows 17 layout046 layout_valid046 1 3)
  owner_valid129 owner_valid046 scope459 scope577
  binding1892_0 binding1892_1
  2 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate546 certificate704 (by decide)

theorem case_closed1893 : CoreExcluded (baseCore 1 3 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout047 layout186
  (layout_for_all_rows 18 layout047 layout_valid047 1 3)
  (layout_for_all_rows 18 layout186 layout_valid186 1 3)
  owner_valid047 owner_valid186 scope044 scope417
  binding1893_0 binding1893_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate044 certificate705 (by decide)

theorem case_closed1894 : CoreExcluded (baseCore 1 3 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout049
  (layout_for_all_rows 19 layout049 layout_valid049 1 3) owner_valid049
  scope578 binding1894_0 certificate706

theorem case_closed1895 : CoreExcluded (baseCore 1 3 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 3) owner_valid026
  scope579 binding1895_0 certificate707

theorem case_closed1896 : CoreExcluded (baseCore 1 3 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 3) owner_valid050
  scope124 binding1896_0 certificate124

theorem case_closed1897 : CoreExcluded (baseCore 1 3 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 3) owner_valid052
  scope125 binding1897_0 certificate125

theorem case_closed1898 : CoreExcluded (baseCore 1 3 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 1 3) owner_valid054
  scope126 binding1898_0 certificate126

theorem case_closed1899 : CoreExcluded (baseCore 1 3 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 1 3) owner_valid074
  scope127 binding1899_0 certificate127

theorem block_closed018 (i : Fin 100) : CoreExcluded (caseCore (blockCase 18 i)) := by
 fin_cases i
 · exact case_closed1800
 · exact case_closed1801
 · exact case_closed1802
 · exact case_closed1803
 · exact case_closed1804
 · exact case_closed1805
 · exact case_closed1806
 · exact case_closed1807
 · exact case_closed1808
 · exact case_closed1809
 · exact case_closed1810
 · exact case_closed1811
 · exact case_closed1812
 · exact case_closed1813
 · exact case_closed1814
 · exact case_closed1815
 · exact case_closed1816
 · exact case_closed1817
 · exact case_closed1818
 · exact case_closed1819
 · exact case_closed1820
 · exact case_closed1821
 · exact case_closed1822
 · exact case_closed1823
 · exact case_closed1824
 · exact case_closed1825
 · exact case_closed1826
 · exact case_closed1827
 · exact case_closed1828
 · exact case_closed1829
 · exact case_closed1830
 · exact case_closed1831
 · exact case_closed1832
 · exact case_closed1833
 · exact case_closed1834
 · exact case_closed1835
 · exact case_closed1836
 · exact case_closed1837
 · exact case_closed1838
 · exact case_closed1839
 · exact case_closed1840
 · exact case_closed1841
 · exact case_closed1842
 · exact case_closed1843
 · exact case_closed1844
 · exact case_closed1845
 · exact case_closed1846
 · exact case_closed1847
 · exact case_closed1848
 · exact case_closed1849
 · exact case_closed1850
 · exact case_closed1851
 · exact case_closed1852
 · exact case_closed1853
 · exact case_closed1854
 · exact case_closed1855
 · exact case_closed1856
 · exact case_closed1857
 · exact case_closed1858
 · exact case_closed1859
 · exact case_closed1860
 · exact case_closed1861
 · exact case_closed1862
 · exact case_closed1863
 · exact case_closed1864
 · exact case_closed1865
 · exact case_closed1866
 · exact case_closed1867
 · exact case_closed1868
 · exact case_closed1869
 · exact case_closed1870
 · exact case_closed1871
 · exact case_closed1872
 · exact case_closed1873
 · exact case_closed1874
 · exact case_closed1875
 · exact case_closed1876
 · exact case_closed1877
 · exact case_closed1878
 · exact case_closed1879
 · exact case_closed1880
 · exact case_closed1881
 · exact case_closed1882
 · exact case_closed1883
 · exact case_closed1884
 · exact case_closed1885
 · exact case_closed1886
 · exact case_closed1887
 · exact case_closed1888
 · exact case_closed1889
 · exact case_closed1890
 · exact case_closed1891
 · exact case_closed1892
 · exact case_closed1893
 · exact case_closed1894
 · exact case_closed1895
 · exact case_closed1896
 · exact case_closed1897
 · exact case_closed1898
 · exact case_closed1899
end PricingC.GIsomorphic