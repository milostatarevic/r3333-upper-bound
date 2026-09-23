import PricingC.GCoreExcluded
import PricingC.GBindings017
import PricingC.GScopeChecks008
import PricingC.GScopeChecks009
import PricingC.GScopeChecks013
import PricingC.GScopeChecks014
import PricingC.GScopeChecks018
import PricingC.GScopeChecks019
import PricingC.GScopeChecks020
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GScopeChecks032
import PricingC.GScopeChecks039
import PricingC.GScopeChecks041
import PricingC.GScopeChecks042
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

theorem case_closed1700 : CoreExcluded (baseCore 0 68 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 0 68) owner_valid187
  scope361 binding1700_0 certificate362

theorem case_closed1701 : CoreExcluded (baseCore 0 68 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 0 68) owner_valid075
  scope362 binding1701_0 certificate363

theorem case_closed1702 : CoreExcluded (baseCore 0 68 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 68) owner_valid034
  scope132 binding1702_0 certificate132

theorem case_closed1703 : CoreExcluded (baseCore 0 68 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 0 68) owner_valid077
  scope364 binding1703_0 certificate365

theorem case_closed1704 : CoreExcluded (baseCore 0 68 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 0 68) owner_valid007
  scope365 binding1704_0 certificate366

theorem case_closed1705 : CoreExcluded (baseCore 0 68 5) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout176 layout108
  (layout_for_all_rows 5 layout176 layout_valid176 0 68)
  (layout_for_all_rows 5 layout108 layout_valid108 0 68)
  owner_valid176 owner_valid108 scope479 scope367
  binding1705_0 binding1705_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate517 certificate518 (by decide)

theorem case_closed1706 : CoreExcluded (baseCore 0 68 6) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout177 layout178
  (layout_for_all_rows 6 layout177 layout_valid177 0 68)
  (layout_for_all_rows 6 layout178 layout_valid178 0 68)
  owner_valid177 owner_valid178 scope366 scope478
  binding1706_0 binding1706_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate367 certificate516 (by decide)

theorem case_closed1707 : CoreExcluded (baseCore 0 68 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 68) owner_valid011
  scope141 binding1707_0 certificate141

theorem case_closed1708 : CoreExcluded (baseCore 0 68 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 68) owner_valid012
  scope142 binding1708_0 certificate142

theorem case_closed1709 : CoreExcluded (baseCore 0 68 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 68) owner_valid038
  scope143 binding1709_0 certificate143

theorem case_closed1710 : CoreExcluded (baseCore 0 68 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 68) owner_valid079
  scope144 binding1710_0 certificate144

theorem case_closed1711 : CoreExcluded (baseCore 0 68 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 68) owner_valid017
  scope145 binding1711_0 certificate145

theorem case_closed1712 : CoreExcluded (baseCore 0 68 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 68) owner_valid018
  scope146 binding1712_0 certificate146

theorem case_closed1713 : CoreExcluded (baseCore 0 68 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 68) owner_valid019
  scope147 binding1713_0 certificate147

theorem case_closed1714 : CoreExcluded (baseCore 0 68 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 68) owner_valid020
  scope148 binding1714_0 certificate148

theorem case_closed1715 : CoreExcluded (baseCore 0 68 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 68) owner_valid021
  scope149 binding1715_0 certificate149

theorem case_closed1716 : CoreExcluded (baseCore 0 68 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 68) owner_valid022
  scope150 binding1716_0 certificate150

theorem case_closed1717 : CoreExcluded (baseCore 0 68 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 68) owner_valid023
  scope151 binding1717_0 certificate151

theorem case_closed1718 : CoreExcluded (baseCore 0 68 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 68) owner_valid024
  scope152 binding1718_0 certificate152

theorem case_closed1719 : CoreExcluded (baseCore 0 68 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 68) owner_valid025
  scope153 binding1719_0 certificate153

theorem case_closed1720 : CoreExcluded (baseCore 0 68 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 68) owner_valid026
  scope154 binding1720_0 certificate154

theorem case_closed1721 : CoreExcluded (baseCore 0 68 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 68) owner_valid087
  scope155 binding1721_0 certificate155

theorem case_closed1722 : CoreExcluded (baseCore 0 68 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 68) owner_valid072
  scope156 binding1722_0 certificate156

theorem case_closed1723 : CoreExcluded (baseCore 0 68 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 68) owner_valid054
  scope388 binding1723_0 certificate389

theorem case_closed1724 : CoreExcluded (baseCore 0 68 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout201
  (layout_for_all_rows 24 layout201 layout_valid201 0 68) owner_valid201
  scope389 binding1724_0 certificate390

theorem case_closed1725 : CoreExcluded (baseCore 0 69 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 69) owner_valid033
  scope211 binding1725_0 certificate211

theorem case_closed1726 : CoreExcluded (baseCore 0 69 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 69) owner_valid002
  scope212 binding1726_0 certificate212

theorem case_closed1727 : CoreExcluded (baseCore 0 69 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 69) owner_valid034
  scope213 binding1727_0 certificate213

theorem case_closed1728 : CoreExcluded (baseCore 0 69 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 69) owner_valid035
  scope214 binding1728_0 certificate214

theorem case_closed1729 : CoreExcluded (baseCore 0 69 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 69) owner_valid036
  scope215 binding1729_0 certificate215

theorem case_closed1730 : CoreExcluded (baseCore 0 69 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 69) owner_valid009
  scope216 binding1730_0 certificate216

theorem case_closed1731 : CoreExcluded (baseCore 0 69 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 69) owner_valid010
  scope217 binding1731_0 certificate217

theorem case_closed1732 : CoreExcluded (baseCore 0 69 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 69) owner_valid011
  scope218 binding1732_0 certificate218

theorem case_closed1733 : CoreExcluded (baseCore 0 69 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 69) owner_valid012
  scope219 binding1733_0 certificate219

theorem case_closed1734 : CoreExcluded (baseCore 0 69 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 69) owner_valid038
  scope220 binding1734_0 certificate220

theorem case_closed1735 : CoreExcluded (baseCore 0 69 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 69) owner_valid079
  scope221 binding1735_0 certificate221

theorem case_closed1736 : CoreExcluded (baseCore 0 69 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 69) owner_valid017
  scope222 binding1736_0 certificate222

theorem case_closed1737 : CoreExcluded (baseCore 0 69 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 69) owner_valid018
  scope223 binding1737_0 certificate223

theorem case_closed1738 : CoreExcluded (baseCore 0 69 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 69) owner_valid019
  scope224 binding1738_0 certificate224

theorem case_closed1739 : CoreExcluded (baseCore 0 69 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 69) owner_valid020
  scope225 binding1739_0 certificate225

theorem case_closed1740 : CoreExcluded (baseCore 0 69 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 69) owner_valid021
  scope226 binding1740_0 certificate226

theorem case_closed1741 : CoreExcluded (baseCore 0 69 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 69) owner_valid022
  scope227 binding1741_0 certificate227

theorem case_closed1742 : CoreExcluded (baseCore 0 69 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 69) owner_valid023
  scope228 binding1742_0 certificate228

theorem case_closed1743 : CoreExcluded (baseCore 0 69 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 69) owner_valid024
  scope229 binding1743_0 certificate229

theorem case_closed1744 : CoreExcluded (baseCore 0 69 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 69) owner_valid025
  scope230 binding1744_0 certificate230

theorem case_closed1745 : CoreExcluded (baseCore 0 69 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 69) owner_valid026
  scope231 binding1745_0 certificate231

theorem case_closed1746 : CoreExcluded (baseCore 0 69 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 69) owner_valid087
  scope232 binding1746_0 certificate232

theorem case_closed1747 : CoreExcluded (baseCore 0 69 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 69) owner_valid072
  scope233 binding1747_0 certificate233

theorem case_closed1748 : CoreExcluded (baseCore 0 69 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 69) owner_valid031
  scope234 binding1748_0 certificate234

theorem case_closed1749 : CoreExcluded (baseCore 0 69 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 69) owner_valid032
  scope235 binding1749_0 certificate235

theorem case_closed1750 : CoreExcluded (baseCore 0 70 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 0 70) owner_valid187
  scope361 binding1750_0 certificate362

theorem case_closed1751 : CoreExcluded (baseCore 0 70 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 0 70) owner_valid075
  scope362 binding1751_0 certificate363

theorem case_closed1752 : CoreExcluded (baseCore 0 70 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 0 70) owner_valid003
  scope363 binding1752_0 certificate364

theorem case_closed1753 : CoreExcluded (baseCore 0 70 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 70) owner_valid035
  scope302 binding1753_0 certificate302

theorem case_closed1754 : CoreExcluded (baseCore 0 70 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 0 70) owner_valid007
  scope365 binding1754_0 certificate366

theorem case_closed1755 : CoreExcluded (baseCore 0 70 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 70) owner_valid009
  scope305 binding1755_0 certificate305

theorem case_closed1756 : CoreExcluded (baseCore 0 70 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 70) owner_valid010
  scope306 binding1756_0 certificate306

theorem case_closed1757 : CoreExcluded (baseCore 0 70 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 70) owner_valid011
  scope307 binding1757_0 certificate307

theorem case_closed1758 : CoreExcluded (baseCore 0 70 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 70) owner_valid012
  scope308 binding1758_0 certificate308

theorem case_closed1759 : CoreExcluded (baseCore 0 70 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 70) owner_valid038
  scope309 binding1759_0 certificate309

theorem case_closed1760 : CoreExcluded (baseCore 0 70 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 70) owner_valid079
  scope310 binding1760_0 certificate310

theorem case_closed1761 : CoreExcluded (baseCore 0 70 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 70) owner_valid149
  scope371 binding1761_0 certificate372

theorem case_closed1762 : CoreExcluded (baseCore 0 70 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout119
  (layout_for_all_rows 12 layout119 layout_valid119 0 70) owner_valid119
  scope527 binding1762_0 certificate633

theorem case_closed1763 : CoreExcluded (baseCore 0 70 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout137 layout179
  (layout_for_all_rows 13 layout137 layout_valid137 0 70)
  (layout_for_all_rows 13 layout179 layout_valid179 0 70)
  owner_valid137 owner_valid179 scope372 scope544
  binding1763_0 binding1763_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate666 certificate667 (by decide)

theorem case_closed1764 : CoreExcluded (baseCore 0 70 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout123 layout124
  (layout_for_all_rows 14 layout123 layout_valid123 0 70)
  (layout_for_all_rows 14 layout124 layout_valid124 0 70)
  owner_valid123 owner_valid124 scope485 scope375
  binding1764_0 binding1764_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate668 certificate376 (by decide)

theorem case_closed1765 : CoreExcluded (baseCore 0 70 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 70) owner_valid021
  scope319 binding1765_0 certificate319

theorem case_closed1766 : CoreExcluded (baseCore 0 70 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 70) owner_valid022
  scope320 binding1766_0 certificate320

theorem case_closed1767 : CoreExcluded (baseCore 0 70 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 70) owner_valid023
  scope321 binding1767_0 certificate321

theorem case_closed1768 : CoreExcluded (baseCore 0 70 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 70) owner_valid024
  scope322 binding1768_0 certificate322

theorem case_closed1769 : CoreExcluded (baseCore 0 70 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 70) owner_valid025
  scope323 binding1769_0 certificate323

theorem case_closed1770 : CoreExcluded (baseCore 0 70 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 70) owner_valid026
  scope324 binding1770_0 certificate324

theorem case_closed1771 : CoreExcluded (baseCore 0 70 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 70) owner_valid087
  scope325 binding1771_0 certificate325

theorem case_closed1772 : CoreExcluded (baseCore 0 70 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 70) owner_valid072
  scope326 binding1772_0 certificate326

theorem case_closed1773 : CoreExcluded (baseCore 0 70 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 70) owner_valid031
  scope327 binding1773_0 certificate327

theorem case_closed1774 : CoreExcluded (baseCore 0 70 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 70) owner_valid032
  scope328 binding1774_0 certificate328

theorem case_closed1775 : CoreExcluded (baseCore 0 71 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout000
  (layout_for_all_rows 0 layout000 layout_valid000 0 71) owner_valid000
  scope545 binding1775_0 certificate669

theorem case_closed1776 : CoreExcluded (baseCore 0 71 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout191
  (layout_for_all_rows 1 layout191 layout_valid191 0 71) owner_valid191
  scope546 binding1776_0 certificate670

theorem case_closed1777 : CoreExcluded (baseCore 0 71 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout004
  (layout_for_all_rows 2 layout004 layout_valid004 0 71) owner_valid004
  scope547 binding1777_0 certificate671

theorem case_closed1778 : CoreExcluded (baseCore 0 71 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout005
  (layout_for_all_rows 3 layout005 layout_valid005 0 71) owner_valid005
  scope548 binding1778_0 certificate672

theorem case_closed1779 : CoreExcluded (baseCore 0 71 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 71) owner_valid036
  scope337 binding1779_0 certificate337

theorem case_closed1780 : CoreExcluded (baseCore 0 71 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 71) owner_valid009
  scope338 binding1780_0 certificate338

theorem case_closed1781 : CoreExcluded (baseCore 0 71 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 71) owner_valid010
  scope339 binding1781_0 certificate339

theorem case_closed1782 : CoreExcluded (baseCore 0 71 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 0 71) owner_valid133
  scope549 binding1782_0 certificate673

theorem case_closed1783 : CoreExcluded (baseCore 0 71 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout114
  (layout_for_all_rows 8 layout114 layout_valid114 0 71) owner_valid114
  scope549 binding1783_0 certificate673

theorem case_closed1784 : CoreExcluded (baseCore 0 71 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 71) owner_valid038
  scope343 binding1784_0 certificate344

theorem case_closed1785 : CoreExcluded (baseCore 0 71 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 71) owner_valid079
  scope344 binding1785_0 certificate345

theorem case_closed1786 : CoreExcluded (baseCore 0 71 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 71) owner_valid017
  scope345 binding1786_0 certificate346

theorem case_closed1787 : CoreExcluded (baseCore 0 71 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 71) owner_valid018
  scope346 binding1787_0 certificate347

theorem case_closed1788 : CoreExcluded (baseCore 0 71 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 71) owner_valid019
  scope347 binding1788_0 certificate348

theorem case_closed1789 : CoreExcluded (baseCore 0 71 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 71) owner_valid020
  scope348 binding1789_0 certificate349

theorem case_closed1790 : CoreExcluded (baseCore 0 71 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout150
  (layout_for_all_rows 15 layout064 layout_valid064 0 71)
  (layout_for_all_rows 15 layout150 layout_valid150 0 71)
  owner_valid064 owner_valid150 scope528 scope377
  binding1790_0 binding1790_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate674 certificate378 (by decide)

theorem case_closed1791 : CoreExcluded (baseCore 0 71 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout180 layout067
  (layout_for_all_rows 16 layout180 layout_valid180 0 71)
  (layout_for_all_rows 16 layout067 layout_valid067 0 71)
  owner_valid180 owner_valid067 scope550 scope551
  binding1791_0 binding1791_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate675 certificate676 (by decide)

theorem case_closed1792 : CoreExcluded (baseCore 0 71 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 71) owner_valid023
  scope353 binding1792_0 certificate354

theorem case_closed1793 : CoreExcluded (baseCore 0 71 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 71) owner_valid024
  scope354 binding1793_0 certificate355

theorem case_closed1794 : CoreExcluded (baseCore 0 71 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 71) owner_valid025
  scope355 binding1794_0 certificate356

theorem case_closed1795 : CoreExcluded (baseCore 0 71 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 71) owner_valid026
  scope356 binding1795_0 certificate357

theorem case_closed1796 : CoreExcluded (baseCore 0 71 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 71) owner_valid087
  scope357 binding1796_0 certificate358

theorem case_closed1797 : CoreExcluded (baseCore 0 71 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 71) owner_valid072
  scope358 binding1797_0 certificate359

theorem case_closed1798 : CoreExcluded (baseCore 0 71 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 71) owner_valid031
  scope359 binding1798_0 certificate360

theorem case_closed1799 : CoreExcluded (baseCore 0 71 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 71) owner_valid032
  scope360 binding1799_0 certificate361

theorem block_closed017 (i : Fin 100) : CoreExcluded (caseCore (blockCase 17 i)) := by
 fin_cases i
 · exact case_closed1700
 · exact case_closed1701
 · exact case_closed1702
 · exact case_closed1703
 · exact case_closed1704
 · exact case_closed1705
 · exact case_closed1706
 · exact case_closed1707
 · exact case_closed1708
 · exact case_closed1709
 · exact case_closed1710
 · exact case_closed1711
 · exact case_closed1712
 · exact case_closed1713
 · exact case_closed1714
 · exact case_closed1715
 · exact case_closed1716
 · exact case_closed1717
 · exact case_closed1718
 · exact case_closed1719
 · exact case_closed1720
 · exact case_closed1721
 · exact case_closed1722
 · exact case_closed1723
 · exact case_closed1724
 · exact case_closed1725
 · exact case_closed1726
 · exact case_closed1727
 · exact case_closed1728
 · exact case_closed1729
 · exact case_closed1730
 · exact case_closed1731
 · exact case_closed1732
 · exact case_closed1733
 · exact case_closed1734
 · exact case_closed1735
 · exact case_closed1736
 · exact case_closed1737
 · exact case_closed1738
 · exact case_closed1739
 · exact case_closed1740
 · exact case_closed1741
 · exact case_closed1742
 · exact case_closed1743
 · exact case_closed1744
 · exact case_closed1745
 · exact case_closed1746
 · exact case_closed1747
 · exact case_closed1748
 · exact case_closed1749
 · exact case_closed1750
 · exact case_closed1751
 · exact case_closed1752
 · exact case_closed1753
 · exact case_closed1754
 · exact case_closed1755
 · exact case_closed1756
 · exact case_closed1757
 · exact case_closed1758
 · exact case_closed1759
 · exact case_closed1760
 · exact case_closed1761
 · exact case_closed1762
 · exact case_closed1763
 · exact case_closed1764
 · exact case_closed1765
 · exact case_closed1766
 · exact case_closed1767
 · exact case_closed1768
 · exact case_closed1769
 · exact case_closed1770
 · exact case_closed1771
 · exact case_closed1772
 · exact case_closed1773
 · exact case_closed1774
 · exact case_closed1775
 · exact case_closed1776
 · exact case_closed1777
 · exact case_closed1778
 · exact case_closed1779
 · exact case_closed1780
 · exact case_closed1781
 · exact case_closed1782
 · exact case_closed1783
 · exact case_closed1784
 · exact case_closed1785
 · exact case_closed1786
 · exact case_closed1787
 · exact case_closed1788
 · exact case_closed1789
 · exact case_closed1790
 · exact case_closed1791
 · exact case_closed1792
 · exact case_closed1793
 · exact case_closed1794
 · exact case_closed1795
 · exact case_closed1796
 · exact case_closed1797
 · exact case_closed1798
 · exact case_closed1799
end PricingC.GIsomorphic