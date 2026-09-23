import PricingC.GCoreExcluded
import PricingC.GBindings028
import PricingC.GScopeChecks012
import PricingC.GScopeChecks013
import PricingC.GScopeChecks014
import PricingC.GScopeChecks017
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GScopeChecks025
import PricingC.GScopeChecks028
import PricingC.GScopeChecks029
import PricingC.GScopeChecks030
import PricingC.GScopeChecks039
import PricingC.GScopeChecks041
import PricingC.GScopeChecks042
import PricingC.GScopeChecks043
import PricingC.GScopeChecks045
import PricingC.GScopeChecks046
import PricingC.GScopeChecks047
import PricingC.GScopeChecks048
import PricingC.GScopeChecks049
import PricingC.GScopeChecks054
import PricingC.GScopeChecks055
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

theorem case_closed2800 : CoreExcluded (baseCore 1 40 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 40) owner_valid033
  scope546 binding2800_0 certificate670

theorem case_closed2801 : CoreExcluded (baseCore 1 40 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 40) owner_valid002
  scope545 binding2801_0 certificate669

theorem case_closed2802 : CoreExcluded (baseCore 1 40 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 40) owner_valid034
  scope547 binding2802_0 certificate671

theorem case_closed2803 : CoreExcluded (baseCore 1 40 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 40) owner_valid035
  scope548 binding2803_0 certificate672

theorem case_closed2804 : CoreExcluded (baseCore 1 40 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 40) owner_valid036
  scope621 binding2804_0 certificate766

theorem case_closed2805 : CoreExcluded (baseCore 1 40 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout146
  (layout_for_all_rows 5 layout146 layout_valid146 1 40) owner_valid146
  scope705 binding2805_0 certificate876

theorem case_closed2806 : CoreExcluded (baseCore 1 40 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout147 layout110
  (layout_for_all_rows 6 layout147 layout_valid147 1 40)
  (layout_for_all_rows 6 layout110 layout_valid110 1 40)
  owner_valid147 owner_valid110 scope706 scope137
  binding2806_0 binding2806_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate877 certificate878 (by decide)

theorem case_closed2807 : CoreExcluded (baseCore 1 40 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout113
  (layout_for_all_rows 7 layout113 layout_valid113 1 40) owner_valid113
  scope707 binding2807_0 certificate879

theorem case_closed2808 : CoreExcluded (baseCore 1 40 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout115
  (layout_for_all_rows 8 layout115 layout_valid115 1 40) owner_valid115
  scope708 binding2808_0 certificate880

theorem case_closed2809 : CoreExcluded (baseCore 1 40 9) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout038 layout060
  (layout_for_all_rows 9 layout038 layout_valid038 1 40)
  (layout_for_all_rows 9 layout060 layout_valid060 1 40)
  owner_valid038 owner_valid060 scope379 scope378
  binding2809_0 binding2809_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate380 certificate379 (by decide)

theorem case_closed2810 : CoreExcluded (baseCore 1 40 10) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout079 layout062
  (layout_for_all_rows 10 layout079 layout_valid079 1 40)
  (layout_for_all_rows 10 layout062 layout_valid062 1 40)
  owner_valid079 owner_valid062 scope377 scope376
  binding2810_0 binding2810_1
  1 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate378 certificate377 (by decide)

theorem case_closed2811 : CoreExcluded (baseCore 1 40 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout041
  (layout_for_all_rows 11 layout041 layout_valid041 1 40) owner_valid041
  scope709 binding2811_0 certificate881

theorem case_closed2812 : CoreExcluded (baseCore 1 40 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout043
  (layout_for_all_rows 12 layout043 layout_valid043 1 40) owner_valid043
  scope710 binding2812_0 certificate882

theorem case_closed2813 : CoreExcluded (baseCore 1 40 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 40) owner_valid019
  scope549 binding2813_0 certificate673

theorem case_closed2814 : CoreExcluded (baseCore 1 40 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout123
  (layout_for_all_rows 14 layout123 layout_valid123 1 40) owner_valid123
  scope368 binding2814_0 certificate369

theorem case_closed2815 : CoreExcluded (baseCore 1 40 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 40) owner_valid021
  scope624 binding2815_0 certificate770

theorem case_closed2816 : CoreExcluded (baseCore 1 40 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 40) owner_valid022
  scope625 binding2816_0 certificate771

theorem case_closed2817 : CoreExcluded (baseCore 1 40 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout045
  (layout_for_all_rows 17 layout045 layout_valid045 1 40) owner_valid045
  scope371 binding2817_0 certificate372

theorem case_closed2818 : CoreExcluded (baseCore 1 40 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 40) owner_valid024
  scope527 binding2818_0 certificate633

theorem case_closed2819 : CoreExcluded (baseCore 1 40 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 40) owner_valid025
  scope626 binding2819_0 certificate772

theorem case_closed2820 : CoreExcluded (baseCore 1 40 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout070 layout071
  (layout_for_all_rows 20 layout070 layout_valid070 1 40)
  (layout_for_all_rows 20 layout071 layout_valid071 1 40)
  owner_valid070 owner_valid071 scope201 scope202
  binding2820_0 binding2820_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate201 certificate202 (by decide)

theorem case_closed2821 : CoreExcluded (baseCore 1 40 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 40) owner_valid087
  scope627 binding2821_0 certificate773

theorem case_closed2822 : CoreExcluded (baseCore 1 40 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 40) owner_valid072
  scope628 binding2822_0 certificate774

theorem case_closed2823 : CoreExcluded (baseCore 1 40 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 40) owner_valid031
  scope629 binding2823_0 certificate775

theorem case_closed2824 : CoreExcluded (baseCore 1 40 24) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout074 layout057
  (layout_for_all_rows 24 layout074 layout_valid074 1 40)
  (layout_for_all_rows 24 layout057 layout_valid057 1 40)
  owner_valid074 owner_valid057 scope209 scope315
  binding2824_0 binding2824_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate209 certificate736 (by decide)

theorem case_closed2825 : CoreExcluded (baseCore 1 41 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 41) owner_valid033
  scope630 binding2825_0 certificate776

theorem case_closed2826 : CoreExcluded (baseCore 1 41 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 41) owner_valid002
  scope631 binding2826_0 certificate777

theorem case_closed2827 : CoreExcluded (baseCore 1 41 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 41) owner_valid034
  scope632 binding2827_0 certificate778

theorem case_closed2828 : CoreExcluded (baseCore 1 41 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 41) owner_valid035
  scope633 binding2828_0 certificate779

theorem case_closed2829 : CoreExcluded (baseCore 1 41 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 41) owner_valid036
  scope634 binding2829_0 certificate780

theorem case_closed2830 : CoreExcluded (baseCore 1 41 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout176 layout108
  (layout_for_all_rows 5 layout176 layout_valid176 1 41)
  (layout_for_all_rows 5 layout108 layout_valid108 1 41)
  owner_valid176 owner_valid108 scope711 scope139
  binding2830_0 binding2830_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate883 certificate884 (by decide)

theorem case_closed2831 : CoreExcluded (baseCore 1 41 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout178
  (layout_for_all_rows 6 layout178 layout_valid178 1 41) owner_valid178
  scope712 binding2831_0 certificate885

theorem case_closed2832 : CoreExcluded (baseCore 1 41 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 41) owner_valid011
  scope285 binding2832_0 certificate285

theorem case_closed2833 : CoreExcluded (baseCore 1 41 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout114
  (layout_for_all_rows 8 layout114 layout_valid114 1 41) owner_valid114
  scope284 binding2833_0 certificate284

theorem case_closed2834 : CoreExcluded (baseCore 1 41 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout060
  (layout_for_all_rows 9 layout060 layout_valid060 1 41) owner_valid060
  scope287 binding2834_0 certificate287

theorem case_closed2835 : CoreExcluded (baseCore 1 41 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 41) owner_valid079
  scope286 binding2835_0 certificate286

theorem case_closed2836 : CoreExcluded (baseCore 1 41 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 41) owner_valid017
  scope635 binding2836_0 certificate781

theorem case_closed2837 : CoreExcluded (baseCore 1 41 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 41) owner_valid018
  scope636 binding2837_0 certificate782

theorem case_closed2838 : CoreExcluded (baseCore 1 41 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout122
  (layout_for_all_rows 13 layout122 layout_valid122 1 41) owner_valid122
  scope713 binding2838_0 certificate886

theorem case_closed2839 : CoreExcluded (baseCore 1 41 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout124
  (layout_for_all_rows 14 layout124 layout_valid124 1 41) owner_valid124
  scope714 binding2839_0 certificate887

theorem case_closed2840 : CoreExcluded (baseCore 1 41 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout065
  (layout_for_all_rows 15 layout065 layout_valid065 1 41) owner_valid065
  scope715 binding2840_0 certificate888

theorem case_closed2841 : CoreExcluded (baseCore 1 41 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout067
  (layout_for_all_rows 16 layout067 layout_valid067 1 41) owner_valid067
  scope716 binding2841_0 certificate889

theorem case_closed2842 : CoreExcluded (baseCore 1 41 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout023 layout045
  (layout_for_all_rows 17 layout023 layout_valid023 1 41)
  (layout_for_all_rows 17 layout045 layout_valid045 1 41)
  owner_valid023 owner_valid045 scope281 scope280
  binding2842_0 binding2842_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate281 certificate280 (by decide)

theorem case_closed2843 : CoreExcluded (baseCore 1 41 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout024 layout047
  (layout_for_all_rows 18 layout024 layout_valid024 1 41)
  (layout_for_all_rows 18 layout047 layout_valid047 1 41)
  owner_valid024 owner_valid047 scope283 scope282
  binding2843_0 binding2843_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate283 certificate282 (by decide)

theorem case_closed2844 : CoreExcluded (baseCore 1 41 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 41) owner_valid025
  scope639 binding2844_0 certificate786

theorem case_closed2845 : CoreExcluded (baseCore 1 41 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 41) owner_valid026
  scope640 binding2845_0 certificate787

theorem case_closed2846 : CoreExcluded (baseCore 1 41 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 41) owner_valid087
  scope641 binding2846_0 certificate788

theorem case_closed2847 : CoreExcluded (baseCore 1 41 22) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout052 layout053
  (layout_for_all_rows 22 layout052 layout_valid052 1 41)
  (layout_for_all_rows 22 layout053 layout_valid053 1 41)
  owner_valid052 owner_valid053 scope205 scope206
  binding2847_0 binding2847_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate205 certificate206 (by decide)

theorem case_closed2848 : CoreExcluded (baseCore 1 41 23) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout054 layout073
  (layout_for_all_rows 23 layout054 layout_valid054 1 41)
  (layout_for_all_rows 23 layout073 layout_valid073 1 41)
  owner_valid054 owner_valid073 scope207 scope593
  binding2848_0 binding2848_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate207 certificate735 (by decide)

theorem case_closed2849 : CoreExcluded (baseCore 1 41 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 41) owner_valid032
  scope642 binding2849_0 certificate789

theorem case_closed2850 : CoreExcluded (baseCore 1 42 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 42) owner_valid187
  scope211 binding2850_0 certificate211

theorem case_closed2851 : CoreExcluded (baseCore 1 42 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 42) owner_valid002
  scope436 binding2851_0 certificate456

theorem case_closed2852 : CoreExcluded (baseCore 1 42 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 42) owner_valid003
  scope213 binding2852_0 certificate213

theorem case_closed2853 : CoreExcluded (baseCore 1 42 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 42) owner_valid077
  scope214 binding2853_0 certificate214

theorem case_closed2854 : CoreExcluded (baseCore 1 42 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 42) owner_valid007
  scope215 binding2854_0 certificate215

theorem case_closed2855 : CoreExcluded (baseCore 1 42 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 42) owner_valid009
  scope441 binding2855_0 certificate465

theorem case_closed2856 : CoreExcluded (baseCore 1 42 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 42) owner_valid010
  scope442 binding2856_0 certificate466

theorem case_closed2857 : CoreExcluded (baseCore 1 42 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 42) owner_valid011
  scope450 binding2857_0 certificate474

theorem case_closed2858 : CoreExcluded (baseCore 1 42 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 42) owner_valid012
  scope449 binding2858_0 certificate473

theorem case_closed2859 : CoreExcluded (baseCore 1 42 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 42) owner_valid038
  scope452 binding2859_0 certificate476

theorem case_closed2860 : CoreExcluded (baseCore 1 42 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 42) owner_valid079
  scope451 binding2860_0 certificate475

theorem case_closed2861 : CoreExcluded (baseCore 1 42 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 42) owner_valid149
  scope223 binding2861_0 certificate223

theorem case_closed2862 : CoreExcluded (baseCore 1 42 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 1 42) owner_valid042
  scope222 binding2862_0 certificate222

theorem case_closed2863 : CoreExcluded (baseCore 1 42 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 42) owner_valid019
  scope443 binding2863_0 certificate467

theorem case_closed2864 : CoreExcluded (baseCore 1 42 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 42) owner_valid020
  scope444 binding2864_0 certificate468

theorem case_closed2865 : CoreExcluded (baseCore 1 42 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 42) owner_valid021
  scope445 binding2865_0 certificate469

theorem case_closed2866 : CoreExcluded (baseCore 1 42 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 42) owner_valid022
  scope446 binding2866_0 certificate470

theorem case_closed2867 : CoreExcluded (baseCore 1 42 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 42) owner_valid023
  scope447 binding2867_0 certificate471

theorem case_closed2868 : CoreExcluded (baseCore 1 42 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 42) owner_valid024
  scope448 binding2868_0 certificate472

theorem case_closed2869 : CoreExcluded (baseCore 1 42 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 42) owner_valid131
  scope230 binding2869_0 certificate230

theorem case_closed2870 : CoreExcluded (baseCore 1 42 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 1 42) owner_valid070
  scope231 binding2870_0 certificate231

theorem case_closed2871 : CoreExcluded (baseCore 1 42 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 42) owner_valid087
  scope454 binding2871_0 certificate481

theorem case_closed2872 : CoreExcluded (baseCore 1 42 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 42) owner_valid072
  scope455 binding2872_0 certificate482

theorem case_closed2873 : CoreExcluded (baseCore 1 42 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 42) owner_valid031
  scope456 binding2873_0 certificate483

theorem case_closed2874 : CoreExcluded (baseCore 1 42 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 42) owner_valid032
  scope457 binding2874_0 certificate484

theorem case_closed2875 : CoreExcluded (baseCore 1 43 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 43) owner_valid033
  scope562 binding2875_0 certificate688

theorem case_closed2876 : CoreExcluded (baseCore 1 43 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 43) owner_valid075
  scope212 binding2876_0 certificate212

theorem case_closed2877 : CoreExcluded (baseCore 1 43 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 43) owner_valid003
  scope213 binding2877_0 certificate213

theorem case_closed2878 : CoreExcluded (baseCore 1 43 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 43) owner_valid077
  scope214 binding2878_0 certificate214

theorem case_closed2879 : CoreExcluded (baseCore 1 43 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 43) owner_valid007
  scope215 binding2879_0 certificate215

theorem case_closed2880 : CoreExcluded (baseCore 1 43 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 43) owner_valid009
  scope563 binding2880_0 certificate689

theorem case_closed2881 : CoreExcluded (baseCore 1 43 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 43) owner_valid010
  scope564 binding2881_0 certificate690

theorem case_closed2882 : CoreExcluded (baseCore 1 43 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 43) owner_valid011
  scope565 binding2882_0 certificate691

theorem case_closed2883 : CoreExcluded (baseCore 1 43 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 1 43) owner_valid012
  scope392 binding2883_0 certificate393

theorem case_closed2884 : CoreExcluded (baseCore 1 43 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 43) owner_valid038
  scope566 binding2884_0 certificate692

theorem case_closed2885 : CoreExcluded (baseCore 1 43 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 43) owner_valid079
  scope567 binding2885_0 certificate693

theorem case_closed2886 : CoreExcluded (baseCore 1 43 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 43) owner_valid017
  scope394 binding2886_0 certificate395

theorem case_closed2887 : CoreExcluded (baseCore 1 43 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 43) owner_valid018
  scope393 binding2887_0 certificate394

theorem case_closed2888 : CoreExcluded (baseCore 1 43 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 43) owner_valid019
  scope568 binding2888_0 certificate694

theorem case_closed2889 : CoreExcluded (baseCore 1 43 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 1 43) owner_valid020
  scope569 binding2889_0 certificate695

theorem case_closed2890 : CoreExcluded (baseCore 1 43 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 1 43) owner_valid064
  scope226 binding2890_0 certificate226

theorem case_closed2891 : CoreExcluded (baseCore 1 43 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 1 43) owner_valid180
  scope227 binding2891_0 certificate227

theorem case_closed2892 : CoreExcluded (baseCore 1 43 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 43) owner_valid023
  scope390 binding2892_0 certificate391

theorem case_closed2893 : CoreExcluded (baseCore 1 43 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 43) owner_valid024
  scope391 binding2893_0 certificate392

theorem case_closed2894 : CoreExcluded (baseCore 1 43 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 43) owner_valid025
  scope395 binding2894_0 certificate396

theorem case_closed2895 : CoreExcluded (baseCore 1 43 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 43) owner_valid026
  scope571 binding2895_0 certificate698

theorem case_closed2896 : CoreExcluded (baseCore 1 43 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 43) owner_valid050
  scope232 binding2896_0 certificate232

theorem case_closed2897 : CoreExcluded (baseCore 1 43 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 43) owner_valid052
  scope233 binding2897_0 certificate233

theorem case_closed2898 : CoreExcluded (baseCore 1 43 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 43) owner_valid031
  scope398 binding2898_0 certificate399

theorem case_closed2899 : CoreExcluded (baseCore 1 43 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 43) owner_valid032
  scope399 binding2899_0 certificate400

theorem block_closed028 (i : Fin 100) : CoreExcluded (caseCore (blockCase 28 i)) := by
 fin_cases i
 · exact case_closed2800
 · exact case_closed2801
 · exact case_closed2802
 · exact case_closed2803
 · exact case_closed2804
 · exact case_closed2805
 · exact case_closed2806
 · exact case_closed2807
 · exact case_closed2808
 · exact case_closed2809
 · exact case_closed2810
 · exact case_closed2811
 · exact case_closed2812
 · exact case_closed2813
 · exact case_closed2814
 · exact case_closed2815
 · exact case_closed2816
 · exact case_closed2817
 · exact case_closed2818
 · exact case_closed2819
 · exact case_closed2820
 · exact case_closed2821
 · exact case_closed2822
 · exact case_closed2823
 · exact case_closed2824
 · exact case_closed2825
 · exact case_closed2826
 · exact case_closed2827
 · exact case_closed2828
 · exact case_closed2829
 · exact case_closed2830
 · exact case_closed2831
 · exact case_closed2832
 · exact case_closed2833
 · exact case_closed2834
 · exact case_closed2835
 · exact case_closed2836
 · exact case_closed2837
 · exact case_closed2838
 · exact case_closed2839
 · exact case_closed2840
 · exact case_closed2841
 · exact case_closed2842
 · exact case_closed2843
 · exact case_closed2844
 · exact case_closed2845
 · exact case_closed2846
 · exact case_closed2847
 · exact case_closed2848
 · exact case_closed2849
 · exact case_closed2850
 · exact case_closed2851
 · exact case_closed2852
 · exact case_closed2853
 · exact case_closed2854
 · exact case_closed2855
 · exact case_closed2856
 · exact case_closed2857
 · exact case_closed2858
 · exact case_closed2859
 · exact case_closed2860
 · exact case_closed2861
 · exact case_closed2862
 · exact case_closed2863
 · exact case_closed2864
 · exact case_closed2865
 · exact case_closed2866
 · exact case_closed2867
 · exact case_closed2868
 · exact case_closed2869
 · exact case_closed2870
 · exact case_closed2871
 · exact case_closed2872
 · exact case_closed2873
 · exact case_closed2874
 · exact case_closed2875
 · exact case_closed2876
 · exact case_closed2877
 · exact case_closed2878
 · exact case_closed2879
 · exact case_closed2880
 · exact case_closed2881
 · exact case_closed2882
 · exact case_closed2883
 · exact case_closed2884
 · exact case_closed2885
 · exact case_closed2886
 · exact case_closed2887
 · exact case_closed2888
 · exact case_closed2889
 · exact case_closed2890
 · exact case_closed2891
 · exact case_closed2892
 · exact case_closed2893
 · exact case_closed2894
 · exact case_closed2895
 · exact case_closed2896
 · exact case_closed2897
 · exact case_closed2898
 · exact case_closed2899
end PricingC.GIsomorphic