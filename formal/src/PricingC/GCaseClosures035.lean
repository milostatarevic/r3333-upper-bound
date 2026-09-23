import PricingC.GCoreExcluded
import PricingC.GBindings035
import PricingC.GScopeChecks012
import PricingC.GScopeChecks015
import PricingC.GScopeChecks017
import PricingC.GScopeChecks019
import PricingC.GScopeChecks021
import PricingC.GScopeChecks022
import PricingC.GScopeChecks023
import PricingC.GScopeChecks024
import PricingC.GScopeChecks025
import PricingC.GScopeChecks036
import PricingC.GScopeChecks037
import PricingC.GScopeChecks039
import PricingC.GScopeChecks041
import PricingC.GScopeChecks042
import PricingC.GScopeChecks046
import PricingC.GScopeChecks047
import PricingC.GScopeChecks048
import PricingC.GScopeChecks049
import PricingC.GScopeChecks058
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

theorem case_closed3500 : CoreExcluded (baseCore 1 68 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout187
  (layout_for_all_rows 0 layout187 layout_valid187 1 68) owner_valid187
  scope361 binding3500_0 certificate362

theorem case_closed3501 : CoreExcluded (baseCore 1 68 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout075
  (layout_for_all_rows 1 layout075 layout_valid075 1 68) owner_valid075
  scope362 binding3501_0 certificate363

theorem case_closed3502 : CoreExcluded (baseCore 1 68 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout003
  (layout_for_all_rows 2 layout003 layout_valid003 1 68) owner_valid003
  scope363 binding3502_0 certificate364

theorem case_closed3503 : CoreExcluded (baseCore 1 68 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout077
  (layout_for_all_rows 3 layout077 layout_valid077 1 68) owner_valid077
  scope364 binding3503_0 certificate365

theorem case_closed3504 : CoreExcluded (baseCore 1 68 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout007
  (layout_for_all_rows 4 layout007 layout_valid007 1 68) owner_valid007
  scope365 binding3504_0 certificate366

theorem case_closed3505 : CoreExcluded (baseCore 1 68 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout108
  (layout_for_all_rows 5 layout108 layout_valid108 1 68) owner_valid108
  scope757 binding3505_0 certificate936

theorem case_closed3506 : CoreExcluded (baseCore 1 68 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout110
  (layout_for_all_rows 6 layout110 layout_valid110 1 68) owner_valid110
  scope758 binding3506_0 certificate937

theorem case_closed3507 : CoreExcluded (baseCore 1 68 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 1 68) owner_valid133
  scope549 binding3507_0 certificate673

theorem case_closed3508 : CoreExcluded (baseCore 1 68 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 68) owner_valid134
  scope368 binding3508_0 certificate369

theorem case_closed3509 : CoreExcluded (baseCore 1 68 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 1 68) owner_valid136
  scope370 binding3509_0 certificate371

theorem case_closed3510 : CoreExcluded (baseCore 1 68 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 68) owner_valid039
  scope369 binding3510_0 certificate370

theorem case_closed3511 : CoreExcluded (baseCore 1 68 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 68) owner_valid149
  scope371 binding3511_0 certificate372

theorem case_closed3512 : CoreExcluded (baseCore 1 68 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout119
  (layout_for_all_rows 12 layout119 layout_valid119 1 68) owner_valid119
  scope527 binding3512_0 certificate633

theorem case_closed3513 : CoreExcluded (baseCore 1 68 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout122
  (layout_for_all_rows 13 layout122 layout_valid122 1 68) owner_valid122
  scope759 binding3513_0 certificate938

theorem case_closed3514 : CoreExcluded (baseCore 1 68 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout124
  (layout_for_all_rows 14 layout124 layout_valid124 1 68) owner_valid124
  scope760 binding3514_0 certificate939

theorem case_closed3515 : CoreExcluded (baseCore 1 68 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout150
  (layout_for_all_rows 15 layout064 layout_valid064 1 68)
  (layout_for_all_rows 15 layout150 layout_valid150 1 68)
  owner_valid064 owner_valid150 scope376 scope377
  binding3515_0 binding3515_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate377 certificate378 (by decide)

theorem case_closed3516 : CoreExcluded (baseCore 1 68 16) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout180 layout066
  (layout_for_all_rows 16 layout180 layout_valid180 1 68)
  (layout_for_all_rows 16 layout066 layout_valid066 1 68)
  owner_valid180 owner_valid066 scope378 scope379
  binding3516_0 binding3516_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate379 certificate380 (by decide)

theorem case_closed3517 : CoreExcluded (baseCore 1 68 17) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout129 layout046
  (layout_for_all_rows 17 layout129 layout_valid129 1 68)
  (layout_for_all_rows 17 layout046 layout_valid046 1 68)
  owner_valid129 owner_valid046 scope380 scope313
  binding3517_0 binding3517_1
  0 7 0 6 (by decide) (by decide) 3 2 (by decide)
  certificate381 certificate797 (by decide)

theorem case_closed3518 : CoreExcluded (baseCore 1 68 18) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout068 layout048
  (layout_for_all_rows 18 layout068 layout_valid068 1 68)
  (layout_for_all_rows 18 layout048 layout_valid048 1 68)
  owner_valid068 owner_valid048 scope382 scope475
  binding3518_0 binding3518_1
  0 7 0 7 (by decide) (by decide) 2 3 (by decide)
  certificate383 certificate798 (by decide)

theorem case_closed3519 : CoreExcluded (baseCore 1 68 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 68) owner_valid131
  scope384 binding3519_0 certificate385

theorem case_closed3520 : CoreExcluded (baseCore 1 68 20) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout026 layout141
  (layout_for_all_rows 20 layout026 layout_valid026 1 68)
  (layout_for_all_rows 20 layout141 layout_valid141 1 68)
  owner_valid026 owner_valid141 scope202 scope201
  binding3520_0 binding3520_1
  0 6 0 6 (by decide) (by decide) 2 3 (by decide)
  certificate202 certificate201 (by decide)

theorem case_closed3521 : CoreExcluded (baseCore 1 68 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 68) owner_valid050
  scope386 binding3521_0 certificate387

theorem case_closed3522 : CoreExcluded (baseCore 1 68 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 68) owner_valid052
  scope387 binding3522_0 certificate388

theorem case_closed3523 : CoreExcluded (baseCore 1 68 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 1 68) owner_valid054
  scope388 binding3523_0 certificate389

theorem case_closed3524 : CoreExcluded (baseCore 1 68 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout057
  (layout_for_all_rows 24 layout057 layout_valid057 1 68) owner_valid057
  scope761 binding3524_0 certificate940

theorem case_closed3525 : CoreExcluded (baseCore 1 69 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 69) owner_valid033
  scope503 binding3525_0 certificate590

theorem case_closed3526 : CoreExcluded (baseCore 1 69 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 69) owner_valid002
  scope502 binding3526_0 certificate589

theorem case_closed3527 : CoreExcluded (baseCore 1 69 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 69) owner_valid034
  scope504 binding3527_0 certificate591

theorem case_closed3528 : CoreExcluded (baseCore 1 69 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 69) owner_valid035
  scope594 binding3528_0 certificate737

theorem case_closed3529 : CoreExcluded (baseCore 1 69 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 69) owner_valid036
  scope505 binding3529_0 certificate592

theorem case_closed3530 : CoreExcluded (baseCore 1 69 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout009
  (layout_for_all_rows 5 layout009 layout_valid009 1 69) owner_valid009
  scope595 binding3530_0 certificate738

theorem case_closed3531 : CoreExcluded (baseCore 1 69 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout010
  (layout_for_all_rows 6 layout010 layout_valid010 1 69) owner_valid010
  scope596 binding3531_0 certificate739

theorem case_closed3532 : CoreExcluded (baseCore 1 69 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 1 69) owner_valid133
  scope492 binding3532_0 certificate579

theorem case_closed3533 : CoreExcluded (baseCore 1 69 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 69) owner_valid134
  scope368 binding3533_0 certificate369

theorem case_closed3534 : CoreExcluded (baseCore 1 69 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout038
  (layout_for_all_rows 9 layout038 layout_valid038 1 69) owner_valid038
  scope254 binding3534_0 certificate254

theorem case_closed3535 : CoreExcluded (baseCore 1 69 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 69) owner_valid039
  scope369 binding3535_0 certificate370

theorem case_closed3536 : CoreExcluded (baseCore 1 69 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 69) owner_valid149
  scope371 binding3536_0 certificate372

theorem case_closed3537 : CoreExcluded (baseCore 1 69 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 69) owner_valid018
  scope255 binding3537_0 certificate255

theorem case_closed3538 : CoreExcluded (baseCore 1 69 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout044
  (layout_for_all_rows 13 layout044 layout_valid044 1 69) owner_valid044
  scope604 binding3538_0 certificate747

theorem case_closed3539 : CoreExcluded (baseCore 1 69 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout139
  (layout_for_all_rows 14 layout139 layout_valid139 1 69) owner_valid139
  scope498 binding3539_0 certificate585

theorem case_closed3540 : CoreExcluded (baseCore 1 69 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout150
  (layout_for_all_rows 15 layout150 layout_valid150 1 69) owner_valid150
  scope499 binding3540_0 certificate586

theorem case_closed3541 : CoreExcluded (baseCore 1 69 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 69) owner_valid022
  scope408 binding3541_0 certificate415

theorem case_closed3542 : CoreExcluded (baseCore 1 69 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout023
  (layout_for_all_rows 17 layout023 layout_valid023 1 69) owner_valid023
  scope506 binding3542_0 certificate593

theorem case_closed3543 : CoreExcluded (baseCore 1 69 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout068
  (layout_for_all_rows 18 layout068 layout_valid068 1 69) owner_valid068
  scope606 binding3543_0 certificate749

theorem case_closed3544 : CoreExcluded (baseCore 1 69 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout131
  (layout_for_all_rows 19 layout131 layout_valid131 1 69) owner_valid131
  scope384 binding3544_0 certificate385

theorem case_closed3545 : CoreExcluded (baseCore 1 69 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout071
  (layout_for_all_rows 20 layout071 layout_valid071 1 69) owner_valid071
  scope609 binding3545_0 certificate752

theorem case_closed3546 : CoreExcluded (baseCore 1 69 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout050
  (layout_for_all_rows 21 layout050 layout_valid050 1 69) owner_valid050
  scope386 binding3546_0 certificate387

theorem case_closed3547 : CoreExcluded (baseCore 1 69 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 69) owner_valid052
  scope387 binding3547_0 certificate388

theorem case_closed3548 : CoreExcluded (baseCore 1 69 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 69) owner_valid031
  scope597 binding3548_0 certificate740

theorem case_closed3549 : CoreExcluded (baseCore 1 69 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 69) owner_valid032
  scope598 binding3549_0 certificate741

theorem case_closed3550 : CoreExcluded (baseCore 1 70 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 70) owner_valid033
  scope546 binding3550_0 certificate670

theorem case_closed3551 : CoreExcluded (baseCore 1 70 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 70) owner_valid002
  scope545 binding3551_0 certificate669

theorem case_closed3552 : CoreExcluded (baseCore 1 70 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 70) owner_valid034
  scope547 binding3552_0 certificate671

theorem case_closed3553 : CoreExcluded (baseCore 1 70 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 70) owner_valid035
  scope548 binding3553_0 certificate672

theorem case_closed3554 : CoreExcluded (baseCore 1 70 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 70) owner_valid036
  scope621 binding3554_0 certificate766

theorem case_closed3555 : CoreExcluded (baseCore 1 70 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout108
  (layout_for_all_rows 5 layout108 layout_valid108 1 70) owner_valid108
  scope757 binding3555_0 certificate936

theorem case_closed3556 : CoreExcluded (baseCore 1 70 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout110
  (layout_for_all_rows 6 layout110 layout_valid110 1 70) owner_valid110
  scope758 binding3556_0 certificate937

theorem case_closed3557 : CoreExcluded (baseCore 1 70 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout133
  (layout_for_all_rows 7 layout133 layout_valid133 1 70) owner_valid133
  scope549 binding3557_0 certificate673

theorem case_closed3558 : CoreExcluded (baseCore 1 70 8) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout134
  (layout_for_all_rows 8 layout134 layout_valid134 1 70) owner_valid134
  scope368 binding3558_0 certificate369

theorem case_closed3559 : CoreExcluded (baseCore 1 70 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 1 70) owner_valid136
  scope370 binding3559_0 certificate371

theorem case_closed3560 : CoreExcluded (baseCore 1 70 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout039
  (layout_for_all_rows 10 layout039 layout_valid039 1 70) owner_valid039
  scope369 binding3560_0 certificate370

theorem case_closed3561 : CoreExcluded (baseCore 1 70 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout149
  (layout_for_all_rows 11 layout149 layout_valid149 1 70) owner_valid149
  scope371 binding3561_0 certificate372

theorem case_closed3562 : CoreExcluded (baseCore 1 70 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout119
  (layout_for_all_rows 12 layout119 layout_valid119 1 70) owner_valid119
  scope527 binding3562_0 certificate633

theorem case_closed3563 : CoreExcluded (baseCore 1 70 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout019
  (layout_for_all_rows 13 layout019 layout_valid019 1 70) owner_valid019
  scope549 binding3563_0 certificate673

theorem case_closed3564 : CoreExcluded (baseCore 1 70 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout123
  (layout_for_all_rows 14 layout123 layout_valid123 1 70) owner_valid123
  scope368 binding3564_0 certificate369

theorem case_closed3565 : CoreExcluded (baseCore 1 70 15) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout021
  (layout_for_all_rows 15 layout021 layout_valid021 1 70) owner_valid021
  scope624 binding3565_0 certificate770

theorem case_closed3566 : CoreExcluded (baseCore 1 70 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout022
  (layout_for_all_rows 16 layout022 layout_valid022 1 70) owner_valid022
  scope625 binding3566_0 certificate771

theorem case_closed3567 : CoreExcluded (baseCore 1 70 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout045
  (layout_for_all_rows 17 layout045 layout_valid045 1 70) owner_valid045
  scope371 binding3567_0 certificate372

theorem case_closed3568 : CoreExcluded (baseCore 1 70 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout024
  (layout_for_all_rows 18 layout024 layout_valid024 1 70) owner_valid024
  scope527 binding3568_0 certificate633

theorem case_closed3569 : CoreExcluded (baseCore 1 70 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 70) owner_valid025
  scope626 binding3569_0 certificate772

theorem case_closed3570 : CoreExcluded (baseCore 1 70 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout142
  (layout_for_all_rows 20 layout142 layout_valid142 1 70) owner_valid142
  scope762 binding3570_0 certificate941

theorem case_closed3571 : CoreExcluded (baseCore 1 70 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 70) owner_valid087
  scope627 binding3571_0 certificate773

theorem case_closed3572 : CoreExcluded (baseCore 1 70 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout072
  (layout_for_all_rows 22 layout072 layout_valid072 1 70) owner_valid072
  scope628 binding3572_0 certificate774

theorem case_closed3573 : CoreExcluded (baseCore 1 70 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout031
  (layout_for_all_rows 23 layout031 layout_valid031 1 70) owner_valid031
  scope629 binding3573_0 certificate775

theorem case_closed3574 : CoreExcluded (baseCore 1 70 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout057
  (layout_for_all_rows 24 layout057 layout_valid057 1 70) owner_valid057
  scope761 binding3574_0 certificate940

theorem case_closed3575 : CoreExcluded (baseCore 1 71 0) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout033
  (layout_for_all_rows 0 layout033 layout_valid033 1 71) owner_valid033
  scope630 binding3575_0 certificate776

theorem case_closed3576 : CoreExcluded (baseCore 1 71 1) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout002
  (layout_for_all_rows 1 layout002 layout_valid002 1 71) owner_valid002
  scope631 binding3576_0 certificate777

theorem case_closed3577 : CoreExcluded (baseCore 1 71 2) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout034
  (layout_for_all_rows 2 layout034 layout_valid034 1 71) owner_valid034
  scope632 binding3577_0 certificate778

theorem case_closed3578 : CoreExcluded (baseCore 1 71 3) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout035
  (layout_for_all_rows 3 layout035 layout_valid035 1 71) owner_valid035
  scope633 binding3578_0 certificate779

theorem case_closed3579 : CoreExcluded (baseCore 1 71 4) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout036
  (layout_for_all_rows 4 layout036 layout_valid036 1 71) owner_valid036
  scope634 binding3579_0 certificate780

theorem case_closed3580 : CoreExcluded (baseCore 1 71 5) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout037
  (layout_for_all_rows 5 layout037 layout_valid037 1 71) owner_valid037
  scope339 binding3580_0 certificate339

theorem case_closed3581 : CoreExcluded (baseCore 1 71 6) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout058
  (layout_for_all_rows 6 layout058 layout_valid058 1 71) owner_valid058
  scope338 binding3581_0 certificate338

theorem case_closed3582 : CoreExcluded (baseCore 1 71 7) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout011
  (layout_for_all_rows 7 layout011 layout_valid011 1 71) owner_valid011
  scope285 binding3582_0 certificate285

theorem case_closed3583 : CoreExcluded (baseCore 1 71 8) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout170 layout171
  (layout_for_all_rows 8 layout170 layout_valid170 1 71)
  (layout_for_all_rows 8 layout171 layout_valid171 1 71)
  owner_valid170 owner_valid171 scope340 scope342
  binding3583_0 binding3583_1
  0 6 6 2 (by decide) (by decide) 3 2 (by decide)
  certificate342 certificate343 (by decide)

theorem case_closed3584 : CoreExcluded (baseCore 1 71 9) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout136
  (layout_for_all_rows 9 layout136 layout_valid136 1 71) owner_valid136
  scope344 binding3584_0 certificate345

theorem case_closed3585 : CoreExcluded (baseCore 1 71 10) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout079
  (layout_for_all_rows 10 layout079 layout_valid079 1 71) owner_valid079
  scope286 binding3585_0 certificate286

theorem case_closed3586 : CoreExcluded (baseCore 1 71 11) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout017
  (layout_for_all_rows 11 layout017 layout_valid017 1 71) owner_valid017
  scope635 binding3586_0 certificate781

theorem case_closed3587 : CoreExcluded (baseCore 1 71 12) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout018
  (layout_for_all_rows 12 layout018 layout_valid018 1 71) owner_valid018
  scope636 binding3587_0 certificate782

theorem case_closed3588 : CoreExcluded (baseCore 1 71 13) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout137
  (layout_for_all_rows 13 layout137 layout_valid137 1 71) owner_valid137
  scope347 binding3588_0 certificate348

theorem case_closed3589 : CoreExcluded (baseCore 1 71 14) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout138
  (layout_for_all_rows 14 layout138 layout_valid138 1 71) owner_valid138
  scope348 binding3589_0 certificate349

theorem case_closed3590 : CoreExcluded (baseCore 1 71 15) := by
 intro c hc phys hr hh
 exact conflict_core_excludes c hc phys _ hr hh layout064 layout150
  (layout_for_all_rows 15 layout064 layout_valid064 1 71)
  (layout_for_all_rows 15 layout150 layout_valid150 1 71)
  owner_valid064 owner_valid150 scope528 scope377
  binding3590_0 binding3590_1
  1 5 1 5 (by decide) (by decide) 3 2 (by decide)
  certificate674 certificate378 (by decide)

theorem case_closed3591 : CoreExcluded (baseCore 1 71 16) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout192
  (layout_for_all_rows 16 layout192 layout_valid192 1 71) owner_valid192
  scope309 binding3591_0 certificate309

theorem case_closed3592 : CoreExcluded (baseCore 1 71 17) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout129
  (layout_for_all_rows 17 layout129 layout_valid129 1 71) owner_valid129
  scope353 binding3592_0 certificate354

theorem case_closed3593 : CoreExcluded (baseCore 1 71 18) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout130
  (layout_for_all_rows 18 layout130 layout_valid130 1 71) owner_valid130
  scope354 binding3593_0 certificate355

theorem case_closed3594 : CoreExcluded (baseCore 1 71 19) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout025
  (layout_for_all_rows 19 layout025 layout_valid025 1 71) owner_valid025
  scope639 binding3594_0 certificate786

theorem case_closed3595 : CoreExcluded (baseCore 1 71 20) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout026
  (layout_for_all_rows 20 layout026 layout_valid026 1 71) owner_valid026
  scope640 binding3595_0 certificate787

theorem case_closed3596 : CoreExcluded (baseCore 1 71 21) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout087
  (layout_for_all_rows 21 layout087 layout_valid087 1 71) owner_valid087
  scope641 binding3596_0 certificate788

theorem case_closed3597 : CoreExcluded (baseCore 1 71 22) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout052
  (layout_for_all_rows 22 layout052 layout_valid052 1 71) owner_valid052
  scope358 binding3597_0 certificate359

theorem case_closed3598 : CoreExcluded (baseCore 1 71 23) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout054
  (layout_for_all_rows 23 layout054 layout_valid054 1 71) owner_valid054
  scope359 binding3598_0 certificate360

theorem case_closed3599 : CoreExcluded (baseCore 1 71 24) := by
 intro c hc phys hr hh
 exact empty_core_excludes c hc phys _ hr hh layout032
  (layout_for_all_rows 24 layout032 layout_valid032 1 71) owner_valid032
  scope642 binding3599_0 certificate789

theorem block_closed035 (i : Fin 100) : CoreExcluded (caseCore (blockCase 35 i)) := by
 fin_cases i
 · exact case_closed3500
 · exact case_closed3501
 · exact case_closed3502
 · exact case_closed3503
 · exact case_closed3504
 · exact case_closed3505
 · exact case_closed3506
 · exact case_closed3507
 · exact case_closed3508
 · exact case_closed3509
 · exact case_closed3510
 · exact case_closed3511
 · exact case_closed3512
 · exact case_closed3513
 · exact case_closed3514
 · exact case_closed3515
 · exact case_closed3516
 · exact case_closed3517
 · exact case_closed3518
 · exact case_closed3519
 · exact case_closed3520
 · exact case_closed3521
 · exact case_closed3522
 · exact case_closed3523
 · exact case_closed3524
 · exact case_closed3525
 · exact case_closed3526
 · exact case_closed3527
 · exact case_closed3528
 · exact case_closed3529
 · exact case_closed3530
 · exact case_closed3531
 · exact case_closed3532
 · exact case_closed3533
 · exact case_closed3534
 · exact case_closed3535
 · exact case_closed3536
 · exact case_closed3537
 · exact case_closed3538
 · exact case_closed3539
 · exact case_closed3540
 · exact case_closed3541
 · exact case_closed3542
 · exact case_closed3543
 · exact case_closed3544
 · exact case_closed3545
 · exact case_closed3546
 · exact case_closed3547
 · exact case_closed3548
 · exact case_closed3549
 · exact case_closed3550
 · exact case_closed3551
 · exact case_closed3552
 · exact case_closed3553
 · exact case_closed3554
 · exact case_closed3555
 · exact case_closed3556
 · exact case_closed3557
 · exact case_closed3558
 · exact case_closed3559
 · exact case_closed3560
 · exact case_closed3561
 · exact case_closed3562
 · exact case_closed3563
 · exact case_closed3564
 · exact case_closed3565
 · exact case_closed3566
 · exact case_closed3567
 · exact case_closed3568
 · exact case_closed3569
 · exact case_closed3570
 · exact case_closed3571
 · exact case_closed3572
 · exact case_closed3573
 · exact case_closed3574
 · exact case_closed3575
 · exact case_closed3576
 · exact case_closed3577
 · exact case_closed3578
 · exact case_closed3579
 · exact case_closed3580
 · exact case_closed3581
 · exact case_closed3582
 · exact case_closed3583
 · exact case_closed3584
 · exact case_closed3585
 · exact case_closed3586
 · exact case_closed3587
 · exact case_closed3588
 · exact case_closed3589
 · exact case_closed3590
 · exact case_closed3591
 · exact case_closed3592
 · exact case_closed3593
 · exact case_closed3594
 · exact case_closed3595
 · exact case_closed3596
 · exact case_closed3597
 · exact case_closed3598
 · exact case_closed3599
end PricingC.GIsomorphic