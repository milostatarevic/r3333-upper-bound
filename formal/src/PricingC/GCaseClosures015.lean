import PricingC.GCoreExcluded
import PricingC.GBindings015
import PricingC.GScopeChecks004
import PricingC.GScopeChecks005
import PricingC.GScopeChecks014
import PricingC.GScopeChecks015
import PricingC.GScopeChecks016
import PricingC.GScopeChecks019
import PricingC.GScopeChecks020
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GScopeChecks028
import PricingC.GScopeChecks038
import PricingC.GScopeChecks039
import PricingC.GScopeChecks040
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

theorem case_closed1500 : CoreExcluded (baseCore 0 60 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 60) owner_valid033
  scope236 binding1500_0 certificate236

theorem case_closed1501 : CoreExcluded (baseCore 0 60 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 60) owner_valid002
  scope237 binding1501_0 certificate237

theorem case_closed1502 : CoreExcluded (baseCore 0 60 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 60) owner_valid034
  scope238 binding1502_0 certificate238

theorem case_closed1503 : CoreExcluded (baseCore 0 60 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 60) owner_valid035
  scope239 binding1503_0 certificate239

theorem case_closed1504 : CoreExcluded (baseCore 0 60 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 60) owner_valid036
  scope240 binding1504_0 certificate240

theorem case_closed1505 : CoreExcluded (baseCore 0 60 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 60) owner_valid009
  scope241 binding1505_0 certificate241

theorem case_closed1506 : CoreExcluded (baseCore 0 60 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 0 60) owner_valid010
  scope242 binding1506_0 certificate242

theorem case_closed1507 : CoreExcluded (baseCore 0 60 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 0 60) owner_valid133
  scope519 binding1507_0 certificate622

theorem case_closed1508 : CoreExcluded (baseCore 0 60 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout135
  (layout_for_all_rows 8 layout135 layout_valid135 0 60) owner_valid135
  scope520 binding1508_0 certificate623

theorem case_closed1509 : CoreExcluded (baseCore 0 60 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 60) owner_valid136
  scope247 binding1509_0 certificate247

theorem case_closed1510 : CoreExcluded (baseCore 0 60 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 60) owner_valid079
  scope247 binding1510_0 certificate247

theorem case_closed1511 : CoreExcluded (baseCore 0 60 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 60) owner_valid017
  scope248 binding1511_0 certificate248

theorem case_closed1512 : CoreExcluded (baseCore 0 60 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 60) owner_valid042
  scope248 binding1512_0 certificate248

theorem case_closed1513 : CoreExcluded (baseCore 0 60 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout137 layout122
  (layout_for_all_rows 13 layout137 layout_valid137 0 60)
  (layout_for_all_rows 13 layout122 layout_valid122 0 60)
  owner_valid137 owner_valid122 scope249 scope517
  binding1513_0 binding1513_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate624 certificate625 (by decide)

theorem case_closed1514 : CoreExcluded (baseCore 0 60 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout138 layout139
  (layout_for_all_rows 14 layout138 layout_valid138 0 60)
  (layout_for_all_rows 14 layout139 layout_valid139 0 60)
  owner_valid138 owner_valid139 scope251 scope485
  binding1514_0 binding1514_1
  0 6 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate251 certificate626 (by decide)

theorem case_closed1515 : CoreExcluded (baseCore 0 60 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 0 60) owner_valid021
  scope253 binding1515_0 certificate253

theorem case_closed1516 : CoreExcluded (baseCore 0 60 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout066
  (layout_for_all_rows 16 layout066 layout_valid066 0 60) owner_valid066
  scope521 binding1516_0 certificate627

theorem case_closed1517 : CoreExcluded (baseCore 0 60 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout140
  (layout_for_all_rows 17 layout140 layout_valid140 0 60) owner_valid140
  scope522 binding1517_0 certificate628

theorem case_closed1518 : CoreExcluded (baseCore 0 60 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 0 60) owner_valid024
  scope256 binding1518_0 certificate256

theorem case_closed1519 : CoreExcluded (baseCore 0 60 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout069
  (layout_for_all_rows 19 layout069 layout_valid069 0 60) owner_valid069
  scope523 binding1519_0 certificate629

theorem case_closed1520 : CoreExcluded (baseCore 0 60 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout071
  (layout_for_all_rows 20 layout071 layout_valid071 0 60) owner_valid071
  scope524 binding1520_0 certificate630

theorem case_closed1521 : CoreExcluded (baseCore 0 60 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout132
  (layout_for_all_rows 21 layout132 layout_valid132 0 60) owner_valid132
  scope525 binding1521_0 certificate631

theorem case_closed1522 : CoreExcluded (baseCore 0 60 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout053
  (layout_for_all_rows 22 layout053 layout_valid053 0 60) owner_valid053
  scope526 binding1522_0 certificate632

theorem case_closed1523 : CoreExcluded (baseCore 0 60 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 60) owner_valid031
  scope265 binding1523_0 certificate265

theorem case_closed1524 : CoreExcluded (baseCore 0 60 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 0 60) owner_valid032
  scope266 binding1524_0 certificate266

theorem case_closed1525 : CoreExcluded (baseCore 0 61 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 61) owner_valid033
  scope361 binding1525_0 certificate362

theorem case_closed1526 : CoreExcluded (baseCore 0 61 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 61) owner_valid002
  scope362 binding1526_0 certificate363

theorem case_closed1527 : CoreExcluded (baseCore 0 61 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 61) owner_valid034
  scope363 binding1527_0 certificate364

theorem case_closed1528 : CoreExcluded (baseCore 0 61 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 61) owner_valid035
  scope364 binding1528_0 certificate365

theorem case_closed1529 : CoreExcluded (baseCore 0 61 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 61) owner_valid036
  scope365 binding1529_0 certificate366

theorem case_closed1530 : CoreExcluded (baseCore 0 61 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 61) owner_valid037
  scope306 binding1530_0 certificate306

theorem case_closed1531 : CoreExcluded (baseCore 0 61 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 61) owner_valid058
  scope305 binding1531_0 certificate305

theorem case_closed1532 : CoreExcluded (baseCore 0 61 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 0 61) owner_valid011
  scope368 binding1532_0 certificate369

theorem case_closed1533 : CoreExcluded (baseCore 0 61 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 0 61) owner_valid134
  scope307 binding1533_0 certificate307

theorem case_closed1534 : CoreExcluded (baseCore 0 61 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 0 61) owner_valid038
  scope369 binding1534_0 certificate370

theorem case_closed1535 : CoreExcluded (baseCore 0 61 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 0 61) owner_valid079
  scope370 binding1535_0 certificate371

theorem case_closed1536 : CoreExcluded (baseCore 0 61 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout199
  (layout_for_all_rows 11 layout199 layout_valid199 0 61) owner_valid199
  scope527 binding1536_0 certificate633

theorem case_closed1537 : CoreExcluded (baseCore 0 61 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 61) owner_valid018
  scope371 binding1537_0 certificate372

theorem case_closed1538 : CoreExcluded (baseCore 0 61 13) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout137 layout179
  (layout_for_all_rows 13 layout137 layout_valid137 0 61)
  (layout_for_all_rows 13 layout179 layout_valid179 0 61)
  owner_valid137 owner_valid179 scope507 scope373
  binding1538_0 binding1538_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate634 certificate374 (by decide)

theorem case_closed1539 : CoreExcluded (baseCore 0 61 14) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout123 layout124
  (layout_for_all_rows 14 layout123 layout_valid123 0 61)
  (layout_for_all_rows 14 layout124 layout_valid124 0 61)
  owner_valid123 owner_valid124 scope374 scope518
  binding1539_0 binding1539_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate635 certificate636 (by decide)

theorem case_closed1540 : CoreExcluded (baseCore 0 61 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout064
  (layout_for_all_rows 15 layout064 layout_valid064 0 61) owner_valid064
  scope319 binding1540_0 certificate319

theorem case_closed1541 : CoreExcluded (baseCore 0 61 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout180
  (layout_for_all_rows 16 layout180 layout_valid180 0 61) owner_valid180
  scope320 binding1541_0 certificate320

theorem case_closed1542 : CoreExcluded (baseCore 0 61 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 0 61) owner_valid129
  scope321 binding1542_0 certificate321

theorem case_closed1543 : CoreExcluded (baseCore 0 61 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 0 61) owner_valid130
  scope322 binding1543_0 certificate322

theorem case_closed1544 : CoreExcluded (baseCore 0 61 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 0 61) owner_valid025
  scope384 binding1544_0 certificate385

theorem case_closed1545 : CoreExcluded (baseCore 0 61 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 61) owner_valid070
  scope324 binding1545_0 certificate324

theorem case_closed1546 : CoreExcluded (baseCore 0 61 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 0 61) owner_valid087
  scope386 binding1546_0 certificate387

theorem case_closed1547 : CoreExcluded (baseCore 0 61 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 61) owner_valid072
  scope387 binding1547_0 certificate388

theorem case_closed1548 : CoreExcluded (baseCore 0 61 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 0 61) owner_valid031
  scope388 binding1548_0 certificate389

theorem case_closed1549 : CoreExcluded (baseCore 0 61 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 0 61) owner_valid074
  scope328 binding1549_0 certificate328

theorem case_closed1550 : CoreExcluded (baseCore 0 62 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 0 62) owner_valid033
  scope064 binding1550_0 certificate064

theorem case_closed1551 : CoreExcluded (baseCore 0 62 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 0 62) owner_valid002
  scope065 binding1551_0 certificate065

theorem case_closed1552 : CoreExcluded (baseCore 0 62 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 0 62) owner_valid034
  scope066 binding1552_0 certificate066

theorem case_closed1553 : CoreExcluded (baseCore 0 62 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 0 62) owner_valid035
  scope067 binding1553_0 certificate067

theorem case_closed1554 : CoreExcluded (baseCore 0 62 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 0 62) owner_valid036
  scope068 binding1554_0 certificate068

theorem case_closed1555 : CoreExcluded (baseCore 0 62 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 0 62) owner_valid009
  scope069 binding1555_0 certificate069

theorem case_closed1556 : CoreExcluded (baseCore 0 62 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 62) owner_valid058
  scope338 binding1556_0 certificate338

theorem case_closed1557 : CoreExcluded (baseCore 0 62 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout112
  (layout_for_all_rows 7 layout112 layout_valid112 0 62) owner_valid112
  scope433 binding1557_0 certificate451

theorem case_closed1558 : CoreExcluded (baseCore 0 62 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout012
  (layout_for_all_rows 8 layout012 layout_valid012 0 62) owner_valid012
  scope070 binding1558_0 certificate070

theorem case_closed1559 : CoreExcluded (baseCore 0 62 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 62) owner_valid136
  scope344 binding1559_0 certificate345

theorem case_closed1560 : CoreExcluded (baseCore 0 62 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 0 62) owner_valid039
  scope343 binding1560_0 certificate344

theorem case_closed1561 : CoreExcluded (baseCore 0 62 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 0 62) owner_valid017
  scope075 binding1561_0 certificate075

theorem case_closed1562 : CoreExcluded (baseCore 0 62 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 0 62) owner_valid018
  scope076 binding1562_0 certificate076

theorem case_closed1563 : CoreExcluded (baseCore 0 62 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 0 62) owner_valid019
  scope077 binding1563_0 certificate077

theorem case_closed1564 : CoreExcluded (baseCore 0 62 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout020
  (layout_for_all_rows 14 layout020 layout_valid020 0 62) owner_valid020
  scope078 binding1564_0 certificate078

theorem case_closed1565 : CoreExcluded (baseCore 0 62 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout065
  (layout_for_all_rows 15 layout064 layout_valid064 0 62)
  (layout_for_all_rows 15 layout065 layout_valid065 0 62)
  owner_valid064 owner_valid065 scope528 scope080
  binding1565_0 binding1565_1
  0 7 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate637 certificate080 (by decide)

theorem case_closed1566 : CoreExcluded (baseCore 0 62 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout066 layout067
  (layout_for_all_rows 16 layout066 layout_valid066 0 62)
  (layout_for_all_rows 16 layout067 layout_valid067 0 62)
  owner_valid066 owner_valid067 scope434 scope082
  binding1566_0 binding1566_1
  0 7 0 7 (by decide) (by decide) 3 2 (by decide)
  certificate454 certificate082 (by decide)

theorem case_closed1567 : CoreExcluded (baseCore 0 62 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 0 62) owner_valid023
  scope083 binding1567_0 certificate083

theorem case_closed1568 : CoreExcluded (baseCore 0 62 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 0 62) owner_valid130
  scope354 binding1568_0 certificate355

theorem case_closed1569 : CoreExcluded (baseCore 0 62 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 0 62) owner_valid131
  scope355 binding1569_0 certificate356

theorem case_closed1570 : CoreExcluded (baseCore 0 62 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 62) owner_valid070
  scope356 binding1570_0 certificate357

theorem case_closed1571 : CoreExcluded (baseCore 0 62 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 0 62) owner_valid050
  scope357 binding1571_0 certificate358

theorem case_closed1572 : CoreExcluded (baseCore 0 62 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 0 62) owner_valid072
  scope090 binding1572_0 certificate090

theorem case_closed1573 : CoreExcluded (baseCore 0 62 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 62) owner_valid054
  scope359 binding1573_0 certificate360

theorem case_closed1574 : CoreExcluded (baseCore 0 62 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 0 62) owner_valid074
  scope360 binding1574_0 certificate361

theorem case_closed1575 : CoreExcluded (baseCore 0 63 0) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout164 layout001
  (layout_for_all_rows 0 layout164 layout_valid164 0 63)
  (layout_for_all_rows 0 layout001 layout_valid001 0 63)
  owner_valid164 owner_valid001 scope403 scope330
  binding1575_0 binding1575_1
  3 9 3 9 (by decide) (by decide) 2 3 (by decide)
  certificate638 certificate330 (by decide)

theorem case_closed1576 : CoreExcluded (baseCore 0 63 1) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout165 layout089
  (layout_for_all_rows 1 layout165 layout_valid165 0 63)
  (layout_for_all_rows 1 layout089 layout_valid089 0 63)
  owner_valid165 owner_valid089 scope163 scope332
  binding1576_0 binding1576_1
  2 8 1 7 (by decide) (by decide) 3 2 (by decide)
  certificate639 certificate332 (by decide)

theorem case_closed1577 : CoreExcluded (baseCore 0 63 2) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout153 layout154
  (layout_for_all_rows 2 layout153 layout_valid153 0 63)
  (layout_for_all_rows 2 layout154 layout_valid154 0 63)
  owner_valid153 owner_valid154 scope404 scope334
  binding1577_0 binding1577_1
  3 9 3 9 (by decide) (by decide) 3 2 (by decide)
  certificate640 certificate334 (by decide)

theorem case_closed1578 : CoreExcluded (baseCore 0 63 3) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout166 layout167
  (layout_for_all_rows 3 layout166 layout_valid166 0 63)
  (layout_for_all_rows 3 layout167 layout_valid167 0 63)
  owner_valid166 owner_valid167 scope529 scope336
  binding1578_0 binding1578_1
  2 8 1 7 (by decide) (by decide) 2 3 (by decide)
  certificate641 certificate336 (by decide)

theorem case_closed1579 : CoreExcluded (baseCore 0 63 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 0 63) owner_valid007
  scope337 binding1579_0 certificate337

theorem case_closed1580 : CoreExcluded (baseCore 0 63 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 0 63) owner_valid037
  scope339 binding1580_0 certificate339

theorem case_closed1581 : CoreExcluded (baseCore 0 63 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 0 63) owner_valid058
  scope338 binding1581_0 certificate338

theorem case_closed1582 : CoreExcluded (baseCore 0 63 7) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout112 layout113
  (layout_for_all_rows 7 layout112 layout_valid112 0 63)
  (layout_for_all_rows 7 layout113 layout_valid113 0 63)
  owner_valid112 owner_valid113 scope175 scope530
  binding1582_0 binding1582_1
  4 8 4 8 (by decide) (by decide) 3 2 (by decide)
  certificate642 certificate643 (by decide)

theorem case_closed1583 : CoreExcluded (baseCore 0 63 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout114 layout115
  (layout_for_all_rows 8 layout114 layout_valid114 0 63)
  (layout_for_all_rows 8 layout115 layout_valid115 0 63)
  owner_valid114 owner_valid115 scope177 scope514
  binding1583_0 binding1583_1
  4 8 4 8 (by decide) (by decide) 2 3 (by decide)
  certificate644 certificate645 (by decide)

theorem case_closed1584 : CoreExcluded (baseCore 0 63 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 0 63) owner_valid136
  scope344 binding1584_0 certificate345

theorem case_closed1585 : CoreExcluded (baseCore 0 63 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 0 63) owner_valid039
  scope343 binding1585_0 certificate344

theorem case_closed1586 : CoreExcluded (baseCore 0 63 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 0 63) owner_valid149
  scope346 binding1586_0 certificate347

theorem case_closed1587 : CoreExcluded (baseCore 0 63 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout042
  (layout_for_all_rows 12 layout042 layout_valid042 0 63) owner_valid042
  scope345 binding1587_0 certificate346

theorem case_closed1588 : CoreExcluded (baseCore 0 63 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 0 63) owner_valid137
  scope347 binding1588_0 certificate348

theorem case_closed1589 : CoreExcluded (baseCore 0 63 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 0 63) owner_valid138
  scope348 binding1589_0 certificate349

theorem case_closed1590 : CoreExcluded (baseCore 0 63 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout125 layout126
  (layout_for_all_rows 15 layout125 layout_valid125 0 63)
  (layout_for_all_rows 15 layout126 layout_valid126 0 63)
  owner_valid125 owner_valid126 scope191 scope531
  binding1590_0 binding1590_1
  3 7 2 6 (by decide) (by decide) 2 3 (by decide)
  certificate646 certificate647 (by decide)

theorem case_closed1591 : CoreExcluded (baseCore 0 63 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout127 layout128
  (layout_for_all_rows 16 layout127 layout_valid127 0 63)
  (layout_for_all_rows 16 layout128 layout_valid128 0 63)
  owner_valid127 owner_valid128 scope193 scope532
  binding1591_0 binding1591_1
  3 7 2 6 (by decide) (by decide) 3 2 (by decide)
  certificate648 certificate649 (by decide)

theorem case_closed1592 : CoreExcluded (baseCore 0 63 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 0 63) owner_valid129
  scope353 binding1592_0 certificate354

theorem case_closed1593 : CoreExcluded (baseCore 0 63 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 0 63) owner_valid130
  scope354 binding1593_0 certificate355

theorem case_closed1594 : CoreExcluded (baseCore 0 63 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 0 63) owner_valid131
  scope355 binding1594_0 certificate356

theorem case_closed1595 : CoreExcluded (baseCore 0 63 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout070
  (layout_for_all_rows 20 layout070 layout_valid070 0 63) owner_valid070
  scope356 binding1595_0 certificate357

theorem case_closed1596 : CoreExcluded (baseCore 0 63 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 0 63) owner_valid050
  scope357 binding1596_0 certificate358

theorem case_closed1597 : CoreExcluded (baseCore 0 63 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 0 63) owner_valid052
  scope358 binding1597_0 certificate359

theorem case_closed1598 : CoreExcluded (baseCore 0 63 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 0 63) owner_valid054
  scope359 binding1598_0 certificate360

theorem case_closed1599 : CoreExcluded (baseCore 0 63 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout074
  (layout_for_all_rows 24 layout074 layout_valid074 0 63) owner_valid074
  scope360 binding1599_0 certificate361

theorem block_closed015 (i : Fin 100) : CoreExcluded (caseCore (blockCase 15 i)) := by
 fin_cases i
 · exact case_closed1500
 · exact case_closed1501
 · exact case_closed1502
 · exact case_closed1503
 · exact case_closed1504
 · exact case_closed1505
 · exact case_closed1506
 · exact case_closed1507
 · exact case_closed1508
 · exact case_closed1509
 · exact case_closed1510
 · exact case_closed1511
 · exact case_closed1512
 · exact case_closed1513
 · exact case_closed1514
 · exact case_closed1515
 · exact case_closed1516
 · exact case_closed1517
 · exact case_closed1518
 · exact case_closed1519
 · exact case_closed1520
 · exact case_closed1521
 · exact case_closed1522
 · exact case_closed1523
 · exact case_closed1524
 · exact case_closed1525
 · exact case_closed1526
 · exact case_closed1527
 · exact case_closed1528
 · exact case_closed1529
 · exact case_closed1530
 · exact case_closed1531
 · exact case_closed1532
 · exact case_closed1533
 · exact case_closed1534
 · exact case_closed1535
 · exact case_closed1536
 · exact case_closed1537
 · exact case_closed1538
 · exact case_closed1539
 · exact case_closed1540
 · exact case_closed1541
 · exact case_closed1542
 · exact case_closed1543
 · exact case_closed1544
 · exact case_closed1545
 · exact case_closed1546
 · exact case_closed1547
 · exact case_closed1548
 · exact case_closed1549
 · exact case_closed1550
 · exact case_closed1551
 · exact case_closed1552
 · exact case_closed1553
 · exact case_closed1554
 · exact case_closed1555
 · exact case_closed1556
 · exact case_closed1557
 · exact case_closed1558
 · exact case_closed1559
 · exact case_closed1560
 · exact case_closed1561
 · exact case_closed1562
 · exact case_closed1563
 · exact case_closed1564
 · exact case_closed1565
 · exact case_closed1566
 · exact case_closed1567
 · exact case_closed1568
 · exact case_closed1569
 · exact case_closed1570
 · exact case_closed1571
 · exact case_closed1572
 · exact case_closed1573
 · exact case_closed1574
 · exact case_closed1575
 · exact case_closed1576
 · exact case_closed1577
 · exact case_closed1578
 · exact case_closed1579
 · exact case_closed1580
 · exact case_closed1581
 · exact case_closed1582
 · exact case_closed1583
 · exact case_closed1584
 · exact case_closed1585
 · exact case_closed1586
 · exact case_closed1587
 · exact case_closed1588
 · exact case_closed1589
 · exact case_closed1590
 · exact case_closed1591
 · exact case_closed1592
 · exact case_closed1593
 · exact case_closed1594
 · exact case_closed1595
 · exact case_closed1596
 · exact case_closed1597
 · exact case_closed1598
 · exact case_closed1599
end PricingC.GIsomorphic