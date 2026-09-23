import PricingC.GCoreExcluded
import PricingC.GBindings016
import PricingC.GScopeChecks005
import PricingC.GScopeChecks006
import PricingC.GScopeChecks007
import PricingC.GScopeChecks014
import PricingC.GScopeChecks015
import PricingC.GScopeChecks016
import PricingC.GScopeChecks017
import PricingC.GScopeChecks018
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GScopeChecks030
import PricingC.GScopeChecks037
import PricingC.GScopeChecks040
import PricingC.GScopeChecks041
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

theorem case_closed1600 : CoreExcluded (baseCore 0 64 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 64) owner_valid033
  scope236 binding1600_0 certificate236

theorem case_closed1601 : CoreExcluded (baseCore 0 64 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 64) owner_valid002
  scope237 binding1601_0 certificate237

theorem case_closed1602 : CoreExcluded (baseCore 0 64 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 64) owner_valid034
  scope238 binding1602_0 certificate238

theorem case_closed1603 : CoreExcluded (baseCore 0 64 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 64) owner_valid035
  scope239 binding1603_0 certificate239

theorem case_closed1604 : CoreExcluded (baseCore 0 64 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 64) owner_valid036
  scope240 binding1604_0 certificate240

theorem case_closed1605 : CoreExcluded (baseCore 0 64 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 64) owner_valid009
  scope241 binding1605_0 certificate241

theorem case_closed1606 : CoreExcluded (baseCore 0 64 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 64) owner_valid010
  scope242 binding1606_0 certificate242

theorem case_closed1607 : CoreExcluded (baseCore 0 64 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout133 layout113
  (layout_for_all_rows 7 layout133 layout_valid133 0 64)
  (layout_for_all_rows 7 layout113 layout_valid113 0 64)
  owner_valid133 owner_valid113 scope244 scope530
  binding1607_0 binding1607_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate650 certificate651 (by decide)

theorem case_closed1608 : CoreExcluded (baseCore 0 64 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout134 layout135
  (layout_for_all_rows 8 layout134 layout_valid134 0 64)
  (layout_for_all_rows 8 layout135 layout_valid135 0 64)
  owner_valid134 owner_valid135 scope533 scope246
  binding1608_0 binding1608_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate652 certificate246 (by decide)

theorem case_closed1609 : CoreExcluded (baseCore 0 64 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 64) owner_valid136
  scope344 binding1609_0 certificate345

theorem case_closed1610 : CoreExcluded (baseCore 0 64 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 64) owner_valid079
  scope247 binding1610_0 certificate247

theorem case_closed1611 : CoreExcluded (baseCore 0 64 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 64) owner_valid017
  scope248 binding1611_0 certificate248

theorem case_closed1612 : CoreExcluded (baseCore 0 64 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 64) owner_valid042
  scope345 binding1612_0 certificate346

theorem case_closed1613 : CoreExcluded (baseCore 0 64 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 0 64) owner_valid137
  scope347 binding1613_0 certificate348

theorem case_closed1614 : CoreExcluded (baseCore 0 64 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 0 64) owner_valid138
  scope348 binding1614_0 certificate349

theorem case_closed1615 : CoreExcluded (baseCore 0 64 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 64) owner_valid021
  scope253 binding1615_0 certificate253

theorem case_closed1616 : CoreExcluded (baseCore 0 64 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout066
  (layout_for_all_rows 16 layout066 layout_valid066 0 64) owner_valid066
  scope254 binding1616_0 certificate254

theorem case_closed1617 : CoreExcluded (baseCore 0 64 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 0 64) owner_valid129
  scope353 binding1617_0 certificate354

theorem case_closed1618 : CoreExcluded (baseCore 0 64 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 64) owner_valid024
  scope256 binding1618_0 certificate256

theorem case_closed1619 : CoreExcluded (baseCore 0 64 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 0 64) owner_valid131
  scope355 binding1619_0 certificate356

theorem case_closed1620 : CoreExcluded (baseCore 0 64 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 64) owner_valid070
  scope356 binding1620_0 certificate357

theorem case_closed1621 : CoreExcluded (baseCore 0 64 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 0 64) owner_valid050
  scope357 binding1621_0 certificate358

theorem case_closed1622 : CoreExcluded (baseCore 0 64 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 0 64) owner_valid052
  scope358 binding1622_0 certificate359

theorem case_closed1623 : CoreExcluded (baseCore 0 64 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 64) owner_valid031
  scope265 binding1623_0 certificate265

theorem case_closed1624 : CoreExcluded (baseCore 0 64 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 64) owner_valid032
  scope266 binding1624_0 certificate266

theorem case_closed1625 : CoreExcluded (baseCore 0 65 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 65) owner_valid033
  scope267 binding1625_0 certificate267

theorem case_closed1626 : CoreExcluded (baseCore 0 65 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 65) owner_valid002
  scope268 binding1626_0 certificate268

theorem case_closed1627 : CoreExcluded (baseCore 0 65 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 65) owner_valid034
  scope269 binding1627_0 certificate269

theorem case_closed1628 : CoreExcluded (baseCore 0 65 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 65) owner_valid035
  scope270 binding1628_0 certificate270

theorem case_closed1629 : CoreExcluded (baseCore 0 65 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 65) owner_valid036
  scope271 binding1629_0 certificate271

theorem case_closed1630 : CoreExcluded (baseCore 0 65 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 65) owner_valid037
  scope339 binding1630_0 certificate339

theorem case_closed1631 : CoreExcluded (baseCore 0 65 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 65) owner_valid058
  scope338 binding1631_0 certificate338

theorem case_closed1632 : CoreExcluded (baseCore 0 65 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout133 layout148
  (layout_for_all_rows 7 layout133 layout_valid133 0 65)
  (layout_for_all_rows 7 layout148 layout_valid148 0 65)
  owner_valid133 owner_valid148 scope488 scope275
  binding1632_0 binding1632_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate606 certificate607 (by decide)

theorem case_closed1633 : CoreExcluded (baseCore 0 65 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout114 layout115
  (layout_for_all_rows 8 layout114 layout_valid114 0 65)
  (layout_for_all_rows 8 layout115 layout_valid115 0 65)
  owner_valid114 owner_valid115 scope274 scope514
  binding1633_0 binding1633_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate274 certificate605 (by decide)

theorem case_closed1634 : CoreExcluded (baseCore 0 65 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 65) owner_valid136
  scope344 binding1634_0 certificate345

theorem case_closed1635 : CoreExcluded (baseCore 0 65 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 0 65) owner_valid039
  scope343 binding1635_0 certificate344

theorem case_closed1636 : CoreExcluded (baseCore 0 65 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 65) owner_valid149
  scope346 binding1636_0 certificate347

theorem case_closed1637 : CoreExcluded (baseCore 0 65 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 65) owner_valid042
  scope345 binding1637_0 certificate346

theorem case_closed1638 : CoreExcluded (baseCore 0 65 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 65) owner_valid019
  scope284 binding1638_0 certificate284

theorem case_closed1639 : CoreExcluded (baseCore 0 65 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 0 65) owner_valid138
  scope348 binding1639_0 certificate349

theorem case_closed1640 : CoreExcluded (baseCore 0 65 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout200
  (layout_for_all_rows 15 layout200 layout_valid200 0 65) owner_valid200
  scope286 binding1640_0 certificate286

theorem case_closed1641 : CoreExcluded (baseCore 0 65 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 65) owner_valid022
  scope287 binding1641_0 certificate287

theorem case_closed1642 : CoreExcluded (baseCore 0 65 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 65) owner_valid023
  scope288 binding1642_0 certificate288

theorem case_closed1643 : CoreExcluded (baseCore 0 65 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 65) owner_valid024
  scope289 binding1643_0 certificate289

theorem case_closed1644 : CoreExcluded (baseCore 0 65 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 65) owner_valid025
  scope290 binding1644_0 certificate290

theorem case_closed1645 : CoreExcluded (baseCore 0 65 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 0 65) owner_valid026
  scope291 binding1645_0 certificate291

theorem case_closed1646 : CoreExcluded (baseCore 0 65 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 65) owner_valid087
  scope292 binding1646_0 certificate292

theorem case_closed1647 : CoreExcluded (baseCore 0 65 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 0 65) owner_valid052
  scope358 binding1647_0 certificate359

theorem case_closed1648 : CoreExcluded (baseCore 0 65 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 65) owner_valid054
  scope359 binding1648_0 certificate360

theorem case_closed1649 : CoreExcluded (baseCore 0 65 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 65) owner_valid032
  scope295 binding1649_0 certificate295

theorem case_closed1650 : CoreExcluded (baseCore 0 66 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 66) owner_valid033
  scope361 binding1650_0 certificate362

theorem case_closed1651 : CoreExcluded (baseCore 0 66 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 66) owner_valid002
  scope362 binding1651_0 certificate363

theorem case_closed1652 : CoreExcluded (baseCore 0 66 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 66) owner_valid034
  scope363 binding1652_0 certificate364

theorem case_closed1653 : CoreExcluded (baseCore 0 66 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 66) owner_valid035
  scope364 binding1653_0 certificate365

theorem case_closed1654 : CoreExcluded (baseCore 0 66 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 66) owner_valid036
  scope365 binding1654_0 certificate366

theorem case_closed1655 : CoreExcluded (baseCore 0 66 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout145
  (layout_for_all_rows 5 layout145 layout_valid145 0 66) owner_valid145
  scope534 binding1655_0 certificate653

theorem case_closed1656 : CoreExcluded (baseCore 0 66 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout177
  (layout_for_all_rows 6 layout177 layout_valid177 0 66) owner_valid177
  scope535 binding1656_0 certificate654

theorem case_closed1657 : CoreExcluded (baseCore 0 66 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 66) owner_valid011
  scope368 binding1657_0 certificate369

theorem case_closed1658 : CoreExcluded (baseCore 0 66 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 0 66) owner_valid134
  scope368 binding1658_0 certificate369

theorem case_closed1659 : CoreExcluded (baseCore 0 66 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 66) owner_valid038
  scope369 binding1659_0 certificate370

theorem case_closed1660 : CoreExcluded (baseCore 0 66 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 66) owner_valid079
  scope370 binding1660_0 certificate371

theorem case_closed1661 : CoreExcluded (baseCore 0 66 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 66) owner_valid149
  scope371 binding1661_0 certificate372

theorem case_closed1662 : CoreExcluded (baseCore 0 66 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 66) owner_valid018
  scope371 binding1662_0 certificate372

theorem case_closed1663 : CoreExcluded (baseCore 0 66 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout044
  (layout_for_all_rows 13 layout044 layout_valid044 0 66) owner_valid044
  scope536 binding1663_0 certificate655

theorem case_closed1664 : CoreExcluded (baseCore 0 66 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout139
  (layout_for_all_rows 14 layout139 layout_valid139 0 66) owner_valid139
  scope537 binding1664_0 certificate656

theorem case_closed1665 : CoreExcluded (baseCore 0 66 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout200 layout125
  (layout_for_all_rows 15 layout200 layout_valid200 0 66)
  (layout_for_all_rows 15 layout125 layout_valid125 0 66)
  owner_valid200 owner_valid125 scope538 scope539
  binding1665_0 binding1665_1
  2 6 2 5 (by decide) (by decide) 2 3 (by decide)
  certificate657 certificate658 (by decide)

theorem case_closed1666 : CoreExcluded (baseCore 0 66 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout180 layout066
  (layout_for_all_rows 16 layout180 layout_valid180 0 66)
  (layout_for_all_rows 16 layout066 layout_valid066 0 66)
  owner_valid180 owner_valid066 scope378 scope434
  binding1666_0 binding1666_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate379 certificate659 (by decide)

theorem case_closed1667 : CoreExcluded (baseCore 0 66 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout140
  (layout_for_all_rows 17 layout140 layout_valid140 0 66) owner_valid140
  scope540 binding1667_0 certificate660

theorem case_closed1668 : CoreExcluded (baseCore 0 66 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout068
  (layout_for_all_rows 18 layout068 layout_valid068 0 66) owner_valid068
  scope541 binding1668_0 certificate661

theorem case_closed1669 : CoreExcluded (baseCore 0 66 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 66) owner_valid025
  scope384 binding1669_0 certificate385

theorem case_closed1670 : CoreExcluded (baseCore 0 66 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout071
  (layout_for_all_rows 20 layout071 layout_valid071 0 66) owner_valid071
  scope542 binding1670_0 certificate662

theorem case_closed1671 : CoreExcluded (baseCore 0 66 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 66) owner_valid087
  scope386 binding1671_0 certificate387

theorem case_closed1672 : CoreExcluded (baseCore 0 66 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 66) owner_valid072
  scope387 binding1672_0 certificate388

theorem case_closed1673 : CoreExcluded (baseCore 0 66 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 66) owner_valid031
  scope388 binding1673_0 certificate389

theorem case_closed1674 : CoreExcluded (baseCore 0 66 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout056
  (layout_for_all_rows 24 layout056 layout_valid056 0 66) owner_valid056
  scope543 binding1674_0 certificate663

theorem case_closed1675 : CoreExcluded (baseCore 0 67 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 67) owner_valid033
  scope095 binding1675_0 certificate095

theorem case_closed1676 : CoreExcluded (baseCore 0 67 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 0 67) owner_valid075
  scope362 binding1676_0 certificate363

theorem case_closed1677 : CoreExcluded (baseCore 0 67 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 0 67) owner_valid003
  scope363 binding1677_0 certificate364

theorem case_closed1678 : CoreExcluded (baseCore 0 67 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 0 67) owner_valid077
  scope364 binding1678_0 certificate365

theorem case_closed1679 : CoreExcluded (baseCore 0 67 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 0 67) owner_valid007
  scope365 binding1679_0 certificate366

theorem case_closed1680 : CoreExcluded (baseCore 0 67 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 67) owner_valid009
  scope104 binding1680_0 certificate104

theorem case_closed1681 : CoreExcluded (baseCore 0 67 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 67) owner_valid010
  scope105 binding1681_0 certificate105

theorem case_closed1682 : CoreExcluded (baseCore 0 67 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 67) owner_valid011
  scope106 binding1682_0 certificate106

theorem case_closed1683 : CoreExcluded (baseCore 0 67 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 67) owner_valid012
  scope107 binding1683_0 certificate107

theorem case_closed1684 : CoreExcluded (baseCore 0 67 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 67) owner_valid038
  scope108 binding1684_0 certificate108

theorem case_closed1685 : CoreExcluded (baseCore 0 67 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 67) owner_valid079
  scope109 binding1685_0 certificate109

theorem case_closed1686 : CoreExcluded (baseCore 0 67 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 67) owner_valid017
  scope110 binding1686_0 certificate110

theorem case_closed1687 : CoreExcluded (baseCore 0 67 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 67) owner_valid018
  scope111 binding1687_0 certificate111

theorem case_closed1688 : CoreExcluded (baseCore 0 67 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 67) owner_valid019
  scope112 binding1688_0 certificate112

theorem case_closed1689 : CoreExcluded (baseCore 0 67 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 67) owner_valid020
  scope113 binding1689_0 certificate113

theorem case_closed1690 : CoreExcluded (baseCore 0 67 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 67) owner_valid021
  scope114 binding1690_0 certificate114

theorem case_closed1691 : CoreExcluded (baseCore 0 67 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 0 67) owner_valid022
  scope115 binding1691_0 certificate115

theorem case_closed1692 : CoreExcluded (baseCore 0 67 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 0 67)
  (layout_for_all_rows 17 layout046 layout_valid046 0 67)
  owner_valid129 owner_valid046 scope380 scope453
  binding1692_0 binding1692_1
  2 5 1 5 (by decide) (by decide) 2 3 (by decide)
  certificate664 certificate665 (by decide)

theorem case_closed1693 : CoreExcluded (baseCore 0 67 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout047 layout186
  (layout_for_all_rows 18 layout047 layout_valid047 0 67)
  (layout_for_all_rows 18 layout186 layout_valid186 0 67)
  owner_valid047 owner_valid186 scope460 scope383
  binding1693_0 binding1693_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate488 certificate384 (by decide)

theorem case_closed1694 : CoreExcluded (baseCore 0 67 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 0 67) owner_valid131
  scope384 binding1694_0 certificate385

theorem case_closed1695 : CoreExcluded (baseCore 0 67 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout196
  (layout_for_all_rows 20 layout196 layout_valid196 0 67) owner_valid196
  scope385 binding1695_0 certificate386

theorem case_closed1696 : CoreExcluded (baseCore 0 67 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 67) owner_valid087
  scope124 binding1696_0 certificate124

theorem case_closed1697 : CoreExcluded (baseCore 0 67 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 67) owner_valid072
  scope125 binding1697_0 certificate125

theorem case_closed1698 : CoreExcluded (baseCore 0 67 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 67) owner_valid031
  scope126 binding1698_0 certificate126

theorem case_closed1699 : CoreExcluded (baseCore 0 67 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 67) owner_valid032
  scope127 binding1699_0 certificate127

theorem block_closed016 (i : Fin 100) : CoreExcluded (caseCore (blockCase 16 i)) := by
 fin_cases i
 · exact case_closed1600
 · exact case_closed1601
 · exact case_closed1602
 · exact case_closed1603
 · exact case_closed1604
 · exact case_closed1605
 · exact case_closed1606
 · exact case_closed1607
 · exact case_closed1608
 · exact case_closed1609
 · exact case_closed1610
 · exact case_closed1611
 · exact case_closed1612
 · exact case_closed1613
 · exact case_closed1614
 · exact case_closed1615
 · exact case_closed1616
 · exact case_closed1617
 · exact case_closed1618
 · exact case_closed1619
 · exact case_closed1620
 · exact case_closed1621
 · exact case_closed1622
 · exact case_closed1623
 · exact case_closed1624
 · exact case_closed1625
 · exact case_closed1626
 · exact case_closed1627
 · exact case_closed1628
 · exact case_closed1629
 · exact case_closed1630
 · exact case_closed1631
 · exact case_closed1632
 · exact case_closed1633
 · exact case_closed1634
 · exact case_closed1635
 · exact case_closed1636
 · exact case_closed1637
 · exact case_closed1638
 · exact case_closed1639
 · exact case_closed1640
 · exact case_closed1641
 · exact case_closed1642
 · exact case_closed1643
 · exact case_closed1644
 · exact case_closed1645
 · exact case_closed1646
 · exact case_closed1647
 · exact case_closed1648
 · exact case_closed1649
 · exact case_closed1650
 · exact case_closed1651
 · exact case_closed1652
 · exact case_closed1653
 · exact case_closed1654
 · exact case_closed1655
 · exact case_closed1656
 · exact case_closed1657
 · exact case_closed1658
 · exact case_closed1659
 · exact case_closed1660
 · exact case_closed1661
 · exact case_closed1662
 · exact case_closed1663
 · exact case_closed1664
 · exact case_closed1665
 · exact case_closed1666
 · exact case_closed1667
 · exact case_closed1668
 · exact case_closed1669
 · exact case_closed1670
 · exact case_closed1671
 · exact case_closed1672
 · exact case_closed1673
 · exact case_closed1674
 · exact case_closed1675
 · exact case_closed1676
 · exact case_closed1677
 · exact case_closed1678
 · exact case_closed1679
 · exact case_closed1680
 · exact case_closed1681
 · exact case_closed1682
 · exact case_closed1683
 · exact case_closed1684
 · exact case_closed1685
 · exact case_closed1686
 · exact case_closed1687
 · exact case_closed1688
 · exact case_closed1689
 · exact case_closed1690
 · exact case_closed1691
 · exact case_closed1692
 · exact case_closed1693
 · exact case_closed1694
 · exact case_closed1695
 · exact case_closed1696
 · exact case_closed1697
 · exact case_closed1698
 · exact case_closed1699
end PricingC.GIsomorphic