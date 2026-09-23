import PricingIntegration.RemainingGLayouts017

import PricingIntegration.RemainingGLayouts018

import PricingIntegration.RemainingGRejectType

import PricingIntegration.RemainingGScopeChecks000

import PricingIntegration.RemainingGScopeChecks001

import PricingIntegration.RemainingGScopeChecks009

import PricingIntegration.RemainingGScopeChecks010

import PricingIntegration.RemainingGScopeChecks022

import PricingIntegration.RemainingGScopeChecks025

import PricingIntegration.RemainingGScopeChecks026


namespace PricingIntegration.RemainingGWitnesses

open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.CoreLayout PricingIntegration.LocalRelations PricingIntegration.RemainingGCore PricingIntegration.GCoreConsumer PricingC.GScopeAgreement PricingC.GLayoutRefinement

set_option maxHeartbeats 0

set_option maxRecDepth 100000

private theorem bind02664_0 : Agrees (spec (fastBase 0 37 0) layout0143) scope0401 := by decide

private theorem bind02664_1 : Agrees (spec (fastBase 0 37 0) layout0144) scope0402 := by decide

theorem reject02664 : Rejected (base 0 37 0) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0143 layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 0) _ validLayout0143) (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 0) _ validLayout0144) (by decide) (by decide) scope0401 scope0402 (by rw [← fastBase_exact]; exact bind02664_0) (by rw [← fastBase_exact]; exact bind02664_1) 2 7 2 7 (by decide) (by decide) 3 2 (by decide) certificate0414 certificate0415 (by decide)

private theorem bind02665_0 : Agrees (spec (fastBase 0 37 1) layout0145) scope0012 := by decide

theorem reject02665 : Rejected (base 0 37 1) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 1) _ validLayout0145) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind02665_0) certificate0012

private theorem bind02666_0 : Agrees (spec (fastBase 0 37 2) layout0145) scope0011 := by decide

theorem reject02666 : Rejected (base 0 37 2) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 2) _ validLayout0145) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind02666_0) certificate0011

private theorem bind02667_0 : Agrees (spec (fastBase 0 37 3) layout0145) scope0009 := by decide

theorem reject02667 : Rejected (base 0 37 3) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 3) _ validLayout0145) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind02667_0) certificate0009

private theorem bind02668_0 : Agrees (spec (fastBase 0 37 4) layout0145) scope0013 := by decide

theorem reject02668 : Rejected (base 0 37 4) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 4) _ validLayout0145) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind02668_0) certificate0013

private theorem bind02669_0 : Agrees (spec (fastBase 0 37 5) layout0145) scope0004 := by decide

theorem reject02669 : Rejected (base 0 37 5) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 5) _ validLayout0145) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind02669_0) certificate0004

private theorem bind02670_0 : Agrees (spec (fastBase 0 37 6) layout0145) scope0010 := by decide

theorem reject02670 : Rejected (base 0 37 6) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 6) _ validLayout0145) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind02670_0) certificate0010

private theorem bind02671_0 : Agrees (spec (fastBase 0 37 7) layout0143) scope0000 := by decide

private theorem bind02671_1 : Agrees (spec (fastBase 0 37 7) layout0144) scope0398 := by decide

theorem reject02671 : Rejected (base 0 37 7) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0143 layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 7) _ validLayout0143) (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 7) _ validLayout0144) (by decide) (by decide) scope0000 scope0398 (by rw [← fastBase_exact]; exact bind02671_0) (by rw [← fastBase_exact]; exact bind02671_1) 2 7 2 7 (by decide) (by decide) 3 2 (by decide) certificate0416 certificate0417 (by decide)

private theorem bind02672_0 : Agrees (spec (fastBase 0 37 8) layout0145) scope0005 := by decide

theorem reject02672 : Rejected (base 0 37 8) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 8) _ validLayout0145) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind02672_0) certificate0005

private theorem bind02673_0 : Agrees (spec (fastBase 0 37 9) layout0145) scope0003 := by decide

theorem reject02673 : Rejected (base 0 37 9) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 9) _ validLayout0145) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind02673_0) certificate0003

private theorem bind02674_0 : Agrees (spec (fastBase 0 37 10) layout0145) scope0002 := by decide

theorem reject02674 : Rejected (base 0 37 10) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 10) _ validLayout0145) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind02674_0) certificate0002

private theorem bind02675_0 : Agrees (spec (fastBase 0 37 11) layout0145) scope0008 := by decide

theorem reject02675 : Rejected (base 0 37 11) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 11) _ validLayout0145) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind02675_0) certificate0008

private theorem bind02676_0 : Agrees (spec (fastBase 0 37 12) layout0143) scope0023 := by decide

theorem reject02676 : Rejected (base 0 37 12) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0143 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 12) _ validLayout0143) (by decide) scope0023 (by rw [← fastBase_exact]; exact bind02676_0) certificate0023

private theorem bind02677_0 : Agrees (spec (fastBase 0 37 13) layout0143) scope0401 := by decide

private theorem bind02677_1 : Agrees (spec (fastBase 0 37 13) layout0144) scope0402 := by decide

theorem reject02677 : Rejected (base 0 37 13) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0143 layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 13) _ validLayout0143) (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 13) _ validLayout0144) (by decide) (by decide) scope0401 scope0402 (by rw [← fastBase_exact]; exact bind02677_0) (by rw [← fastBase_exact]; exact bind02677_1) 2 7 2 7 (by decide) (by decide) 3 2 (by decide) certificate0414 certificate0415 (by decide)

private theorem bind02678_0 : Agrees (spec (fastBase 0 37 14) layout0144) scope0403 := by decide

theorem reject02678 : Rejected (base 0 37 14) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 14) _ validLayout0144) (by decide) scope0403 (by rw [← fastBase_exact]; exact bind02678_0) certificate0418

private theorem bind02679_0 : Agrees (spec (fastBase 0 37 15) layout0143) scope0401 := by decide

private theorem bind02679_1 : Agrees (spec (fastBase 0 37 15) layout0144) scope0398 := by decide

theorem reject02679 : Rejected (base 0 37 15) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0143 layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 15) _ validLayout0143) (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 15) _ validLayout0144) (by decide) (by decide) scope0401 scope0398 (by rw [← fastBase_exact]; exact bind02679_0) (by rw [← fastBase_exact]; exact bind02679_1) 2 7 2 7 (by decide) (by decide) 3 2 (by decide) certificate0414 certificate0417 (by decide)

private theorem bind02680_0 : Agrees (spec (fastBase 0 37 16) layout0143) scope0357 := by decide

theorem reject02680 : Rejected (base 0 37 16) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0143 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 16) _ validLayout0143) (by decide) scope0357 (by rw [← fastBase_exact]; exact bind02680_0) certificate0364

private theorem bind02681_0 : Agrees (spec (fastBase 0 37 17) layout0145) scope0012 := by decide

theorem reject02681 : Rejected (base 0 37 17) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 17) _ validLayout0145) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind02681_0) certificate0012

private theorem bind02682_0 : Agrees (spec (fastBase 0 37 18) layout0145) scope0020 := by decide

theorem reject02682 : Rejected (base 0 37 18) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 18) _ validLayout0145) (by decide) scope0020 (by rw [← fastBase_exact]; exact bind02682_0) certificate0020

private theorem bind02683_0 : Agrees (spec (fastBase 0 37 19) layout0145) scope0013 := by decide

theorem reject02683 : Rejected (base 0 37 19) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 19) _ validLayout0145) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind02683_0) certificate0013

private theorem bind02684_0 : Agrees (spec (fastBase 0 37 20) layout0145) scope0022 := by decide

theorem reject02684 : Rejected (base 0 37 20) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 20) _ validLayout0145) (by decide) scope0022 (by rw [← fastBase_exact]; exact bind02684_0) certificate0022

private theorem bind02685_0 : Agrees (spec (fastBase 0 37 21) layout0145) scope0003 := by decide

theorem reject02685 : Rejected (base 0 37 21) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 21) _ validLayout0145) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind02685_0) certificate0003

private theorem bind02686_0 : Agrees (spec (fastBase 0 37 22) layout0145) scope0011 := by decide

theorem reject02686 : Rejected (base 0 37 22) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 22) _ validLayout0145) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind02686_0) certificate0011

private theorem bind02687_0 : Agrees (spec (fastBase 0 37 23) layout0145) scope0021 := by decide

theorem reject02687 : Rejected (base 0 37 23) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 23) _ validLayout0145) (by decide) scope0021 (by rw [← fastBase_exact]; exact bind02687_0) certificate0021

private theorem bind02688_0 : Agrees (spec (fastBase 0 37 24) layout0145) scope0015 := by decide

theorem reject02688 : Rejected (base 0 37 24) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 24) _ validLayout0145) (by decide) scope0015 (by rw [← fastBase_exact]; exact bind02688_0) certificate0015

private theorem bind02689_0 : Agrees (spec (fastBase 0 37 25) layout0145) scope0010 := by decide

theorem reject02689 : Rejected (base 0 37 25) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 25) _ validLayout0145) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind02689_0) certificate0010

private theorem bind02690_0 : Agrees (spec (fastBase 0 37 26) layout0145) scope0002 := by decide

theorem reject02690 : Rejected (base 0 37 26) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 26) _ validLayout0145) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind02690_0) certificate0002

private theorem bind02691_0 : Agrees (spec (fastBase 0 37 27) layout0146) scope0158 := by decide

theorem reject02691 : Rejected (base 0 37 27) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0146 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 27) _ validLayout0146) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02691_0) certificate0161

private theorem bind02692_0 : Agrees (spec (fastBase 0 37 28) layout0145) scope0016 := by decide

theorem reject02692 : Rejected (base 0 37 28) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 28) _ validLayout0145) (by decide) scope0016 (by rw [← fastBase_exact]; exact bind02692_0) certificate0016

private theorem bind02693_0 : Agrees (spec (fastBase 0 37 29) layout0145) scope0004 := by decide

theorem reject02693 : Rejected (base 0 37 29) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 29) _ validLayout0145) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind02693_0) certificate0004

private theorem bind02694_0 : Agrees (spec (fastBase 0 37 30) layout0146) scope0145 := by decide

theorem reject02694 : Rejected (base 0 37 30) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0146 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 30) _ validLayout0146) (by decide) scope0145 (by rw [← fastBase_exact]; exact bind02694_0) certificate0148

private theorem bind02695_0 : Agrees (spec (fastBase 0 37 31) layout0145) scope0009 := by decide

theorem reject02695 : Rejected (base 0 37 31) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 31) _ validLayout0145) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind02695_0) certificate0009

private theorem bind02696_0 : Agrees (spec (fastBase 0 37 32) layout0145) scope0012 := by decide

theorem reject02696 : Rejected (base 0 37 32) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 32) _ validLayout0145) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind02696_0) certificate0012

private theorem bind02697_0 : Agrees (spec (fastBase 0 37 33) layout0145) scope0025 := by decide

theorem reject02697 : Rejected (base 0 37 33) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 33) _ validLayout0145) (by decide) scope0025 (by rw [← fastBase_exact]; exact bind02697_0) certificate0025

private theorem bind02698_0 : Agrees (spec (fastBase 0 37 34) layout0145) scope0019 := by decide

theorem reject02698 : Rejected (base 0 37 34) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 34) _ validLayout0145) (by decide) scope0019 (by rw [← fastBase_exact]; exact bind02698_0) certificate0019

private theorem bind02699_0 : Agrees (spec (fastBase 0 37 35) layout0145) scope0005 := by decide

theorem reject02699 : Rejected (base 0 37 35) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 35) _ validLayout0145) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind02699_0) certificate0005

private theorem bind02700_0 : Agrees (spec (fastBase 0 37 36) layout0145) scope0013 := by decide

theorem reject02700 : Rejected (base 0 37 36) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 36) _ validLayout0145) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind02700_0) certificate0013

private theorem bind02701_0 : Agrees (spec (fastBase 0 37 37) layout0145) scope0004 := by decide

theorem reject02701 : Rejected (base 0 37 37) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 37) _ validLayout0145) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind02701_0) certificate0004

private theorem bind02702_0 : Agrees (spec (fastBase 0 37 38) layout0145) scope0020 := by decide

theorem reject02702 : Rejected (base 0 37 38) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 38) _ validLayout0145) (by decide) scope0020 (by rw [← fastBase_exact]; exact bind02702_0) certificate0020

private theorem bind02703_0 : Agrees (spec (fastBase 0 37 39) layout0145) scope0009 := by decide

theorem reject02703 : Rejected (base 0 37 39) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 39) _ validLayout0145) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind02703_0) certificate0009

private theorem bind02704_0 : Agrees (spec (fastBase 0 37 40) layout0145) scope0003 := by decide

theorem reject02704 : Rejected (base 0 37 40) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 40) _ validLayout0145) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind02704_0) certificate0003

private theorem bind02705_0 : Agrees (spec (fastBase 0 37 41) layout0145) scope0014 := by decide

theorem reject02705 : Rejected (base 0 37 41) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 41) _ validLayout0145) (by decide) scope0014 (by rw [← fastBase_exact]; exact bind02705_0) certificate0014

private theorem bind02706_0 : Agrees (spec (fastBase 0 37 42) layout0145) scope0025 := by decide

theorem reject02706 : Rejected (base 0 37 42) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 42) _ validLayout0145) (by decide) scope0025 (by rw [← fastBase_exact]; exact bind02706_0) certificate0025

private theorem bind02707_0 : Agrees (spec (fastBase 0 37 43) layout0145) scope0011 := by decide

theorem reject02707 : Rejected (base 0 37 43) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 43) _ validLayout0145) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind02707_0) certificate0011

private theorem bind02708_0 : Agrees (spec (fastBase 0 37 44) layout0145) scope0005 := by decide

theorem reject02708 : Rejected (base 0 37 44) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 44) _ validLayout0145) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind02708_0) certificate0005

private theorem bind02709_0 : Agrees (spec (fastBase 0 37 45) layout0146) scope0157 := by decide

theorem reject02709 : Rejected (base 0 37 45) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0146 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 45) _ validLayout0146) (by decide) scope0157 (by rw [← fastBase_exact]; exact bind02709_0) certificate0160

private theorem bind02710_0 : Agrees (spec (fastBase 0 37 46) layout0145) scope0010 := by decide

theorem reject02710 : Rejected (base 0 37 46) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 46) _ validLayout0145) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind02710_0) certificate0010

private theorem bind02711_0 : Agrees (spec (fastBase 0 37 47) layout0143) scope0000 := by decide

private theorem bind02711_1 : Agrees (spec (fastBase 0 37 47) layout0144) scope0402 := by decide

theorem reject02711 : Rejected (base 0 37 47) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0143 layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 47) _ validLayout0143) (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 47) _ validLayout0144) (by decide) (by decide) scope0000 scope0402 (by rw [← fastBase_exact]; exact bind02711_0) (by rw [← fastBase_exact]; exact bind02711_1) 2 7 2 7 (by decide) (by decide) 3 2 (by decide) certificate0416 certificate0415 (by decide)

private theorem bind02712_0 : Agrees (spec (fastBase 0 37 48) layout0145) scope0009 := by decide

theorem reject02712 : Rejected (base 0 37 48) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 48) _ validLayout0145) (by decide) scope0009 (by rw [← fastBase_exact]; exact bind02712_0) certificate0009

private theorem bind02713_0 : Agrees (spec (fastBase 0 37 49) layout0145) scope0015 := by decide

theorem reject02713 : Rejected (base 0 37 49) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 49) _ validLayout0145) (by decide) scope0015 (by rw [← fastBase_exact]; exact bind02713_0) certificate0015

private theorem bind02714_0 : Agrees (spec (fastBase 0 37 50) layout0145) scope0014 := by decide

theorem reject02714 : Rejected (base 0 37 50) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 50) _ validLayout0145) (by decide) scope0014 (by rw [← fastBase_exact]; exact bind02714_0) certificate0014

private theorem bind02715_0 : Agrees (spec (fastBase 0 37 51) layout0145) scope0002 := by decide

theorem reject02715 : Rejected (base 0 37 51) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 51) _ validLayout0145) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind02715_0) certificate0002

private theorem bind02716_0 : Agrees (spec (fastBase 0 37 52) layout0145) scope0005 := by decide

theorem reject02716 : Rejected (base 0 37 52) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 52) _ validLayout0145) (by decide) scope0005 (by rw [← fastBase_exact]; exact bind02716_0) certificate0005

private theorem bind02717_0 : Agrees (spec (fastBase 0 37 53) layout0145) scope0013 := by decide

theorem reject02717 : Rejected (base 0 37 53) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 53) _ validLayout0145) (by decide) scope0013 (by rw [← fastBase_exact]; exact bind02717_0) certificate0013

private theorem bind02718_0 : Agrees (spec (fastBase 0 37 54) layout0145) scope0010 := by decide

theorem reject02718 : Rejected (base 0 37 54) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 54) _ validLayout0145) (by decide) scope0010 (by rw [← fastBase_exact]; exact bind02718_0) certificate0010

private theorem bind02719_0 : Agrees (spec (fastBase 0 37 55) layout0145) scope0022 := by decide

theorem reject02719 : Rejected (base 0 37 55) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 55) _ validLayout0145) (by decide) scope0022 (by rw [← fastBase_exact]; exact bind02719_0) certificate0022

private theorem bind02720_0 : Agrees (spec (fastBase 0 37 56) layout0145) scope0021 := by decide

theorem reject02720 : Rejected (base 0 37 56) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 56) _ validLayout0145) (by decide) scope0021 (by rw [← fastBase_exact]; exact bind02720_0) certificate0021

private theorem bind02721_0 : Agrees (spec (fastBase 0 37 57) layout0145) scope0012 := by decide

theorem reject02721 : Rejected (base 0 37 57) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 57) _ validLayout0145) (by decide) scope0012 (by rw [← fastBase_exact]; exact bind02721_0) certificate0012

private theorem bind02722_0 : Agrees (spec (fastBase 0 37 58) layout0145) scope0004 := by decide

theorem reject02722 : Rejected (base 0 37 58) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 58) _ validLayout0145) (by decide) scope0004 (by rw [← fastBase_exact]; exact bind02722_0) certificate0004

private theorem bind02723_0 : Agrees (spec (fastBase 0 37 59) layout0145) scope0019 := by decide

theorem reject02723 : Rejected (base 0 37 59) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 59) _ validLayout0145) (by decide) scope0019 (by rw [← fastBase_exact]; exact bind02723_0) certificate0019

private theorem bind02724_0 : Agrees (spec (fastBase 0 37 60) layout0146) scope0158 := by decide

theorem reject02724 : Rejected (base 0 37 60) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0146 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 60) _ validLayout0146) (by decide) scope0158 (by rw [← fastBase_exact]; exact bind02724_0) certificate0161

private theorem bind02725_0 : Agrees (spec (fastBase 0 37 61) layout0145) scope0003 := by decide

theorem reject02725 : Rejected (base 0 37 61) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 61) _ validLayout0145) (by decide) scope0003 (by rw [← fastBase_exact]; exact bind02725_0) certificate0003

private theorem bind02726_0 : Agrees (spec (fastBase 0 37 62) layout0145) scope0011 := by decide

theorem reject02726 : Rejected (base 0 37 62) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 62) _ validLayout0145) (by decide) scope0011 (by rw [← fastBase_exact]; exact bind02726_0) certificate0011

private theorem bind02727_0 : Agrees (spec (fastBase 0 37 63) layout0145) scope0016 := by decide

theorem reject02727 : Rejected (base 0 37 63) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 63) _ validLayout0145) (by decide) scope0016 (by rw [← fastBase_exact]; exact bind02727_0) certificate0016

private theorem bind02728_0 : Agrees (spec (fastBase 0 37 64) layout0143) scope0000 := by decide

private theorem bind02728_1 : Agrees (spec (fastBase 0 37 64) layout0144) scope0404 := by decide

theorem reject02728 : Rejected (base 0 37 64) := by
  intro c hc phys hr hh

  exact conflict_core_excludes c hc phys _ hr hh layout0143 layout0144 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 64) _ validLayout0143) (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 64) _ validLayout0144) (by decide) (by decide) scope0000 scope0404 (by rw [← fastBase_exact]; exact bind02728_0) (by rw [← fastBase_exact]; exact bind02728_1) 2 7 2 7 (by decide) (by decide) 3 2 (by decide) certificate0416 certificate0419 (by decide)

private theorem bind02729_0 : Agrees (spec (fastBase 0 37 65) layout0146) scope0163 := by decide

theorem reject02729 : Rejected (base 0 37 65) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0146 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 65) _ validLayout0146) (by decide) scope0163 (by rw [← fastBase_exact]; exact bind02729_0) certificate0166

private theorem bind02730_0 : Agrees (spec (fastBase 0 37 66) layout0145) scope0002 := by decide

theorem reject02730 : Rejected (base 0 37 66) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 66) _ validLayout0145) (by decide) scope0002 (by rw [← fastBase_exact]; exact bind02730_0) certificate0002

private theorem bind02731_0 : Agrees (spec (fastBase 0 37 67) layout0145) scope0008 := by decide

theorem reject02731 : Rejected (base 0 37 67) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 67) _ validLayout0145) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind02731_0) certificate0008

private theorem bind02732_0 : Agrees (spec (fastBase 0 37 68) layout0145) scope0008 := by decide

theorem reject02732 : Rejected (base 0 37 68) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 68) _ validLayout0145) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind02732_0) certificate0008

private theorem bind02733_0 : Agrees (spec (fastBase 0 37 69) layout0145) scope0008 := by decide

theorem reject02733 : Rejected (base 0 37 69) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 69) _ validLayout0145) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind02733_0) certificate0008

private theorem bind02734_0 : Agrees (spec (fastBase 0 37 70) layout0145) scope0008 := by decide

theorem reject02734 : Rejected (base 0 37 70) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 70) _ validLayout0145) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind02734_0) certificate0008

private theorem bind02735_0 : Agrees (spec (fastBase 0 37 71) layout0145) scope0008 := by decide

theorem reject02735 : Rejected (base 0 37 71) := by
  intro c hc phys hr hh

  exact empty_core_excludes c hc phys _ hr hh layout0145 (layoutValid_of_refines _ _ (base_refines_skeleton 0 37 71) _ validLayout0145) (by decide) scope0008 (by rw [← fastBase_exact]; exact bind02735_0) certificate0008

theorem allCases037 : ∀ y : Fin 72, Rejected (base 0 37 y) := by
  intro y
  fin_cases y

  · exact reject02664

  · exact reject02665

  · exact reject02666

  · exact reject02667

  · exact reject02668

  · exact reject02669

  · exact reject02670

  · exact reject02671

  · exact reject02672

  · exact reject02673

  · exact reject02674

  · exact reject02675

  · exact reject02676

  · exact reject02677

  · exact reject02678

  · exact reject02679

  · exact reject02680

  · exact reject02681

  · exact reject02682

  · exact reject02683

  · exact reject02684

  · exact reject02685

  · exact reject02686

  · exact reject02687

  · exact reject02688

  · exact reject02689

  · exact reject02690

  · exact reject02691

  · exact reject02692

  · exact reject02693

  · exact reject02694

  · exact reject02695

  · exact reject02696

  · exact reject02697

  · exact reject02698

  · exact reject02699

  · exact reject02700

  · exact reject02701

  · exact reject02702

  · exact reject02703

  · exact reject02704

  · exact reject02705

  · exact reject02706

  · exact reject02707

  · exact reject02708

  · exact reject02709

  · exact reject02710

  · exact reject02711

  · exact reject02712

  · exact reject02713

  · exact reject02714

  · exact reject02715

  · exact reject02716

  · exact reject02717

  · exact reject02718

  · exact reject02719

  · exact reject02720

  · exact reject02721

  · exact reject02722

  · exact reject02723

  · exact reject02724

  · exact reject02725

  · exact reject02726

  · exact reject02727

  · exact reject02728

  · exact reject02729

  · exact reject02730

  · exact reject02731

  · exact reject02732

  · exact reject02733

  · exact reject02734

  · exact reject02735

end PricingIntegration.RemainingGWitnesses
