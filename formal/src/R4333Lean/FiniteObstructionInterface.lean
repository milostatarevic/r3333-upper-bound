import R4333Lean.Attaching61Reduction
import R4333Lean.CriticalCatalogues
import R4333Lean.CriticalTemplateOverlap
import R4333Lean.AttachingPartition
import R4333Lean.DegreeTargets61

/-!
# Kernel-visible interface to the remaining finite obstruction

This file packages exactly the finite data already forced by the semantic
reduction: two entries of the 35-row degree table, the labeled six-region
partition, and one of the `4 × 4` critical-template overlaps.  It adds no
restriction on the two neighbourhood orders or on the overlap size and does
not assert the final finite contradiction.
-/

namespace R4333

open Finset

/-- Read one of the 35 explicit degree rows by a bounded index. -/
def degreeTargetAt61 (i : Fin 35) : FourDegreeTuple :=
  degreeTargets61.getD i (0, 0, 0, 0)

/-- Membership in the 35-row list supplies a concrete bounded selector. -/
theorem exists_degreeTargetAt61_of_mem {target : FourDegreeTuple}
    (htarget : target ∈ degreeTargets61) :
    ∃ i : Fin 35, degreeTargetAt61 i = target := by
  let j := degreeTargets61.idxOf target
  have hj : j < degreeTargets61.length :=
    List.idxOf_lt_length_iff.mpr htarget
  let i : Fin 35 := ⟨j, by simpa [degreeTargets61_length] using hj⟩
  refine ⟨i, ?_⟩
  simp only [degreeTargetAt61, i, j]
  rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf htarget]
  rfl

/-- One exact 35-row degree selector for every vertex of an order-61 host. -/
structure DegreeTargetSelection61
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) where
  index : V → Fin 35
  index_eq : ∀ v, degreeTargetAt61 (index v) = fourColorDegreeTuple c v

/-- The degree bound and degree-sum theorem select all vertex rows
simultaneously.  This includes every vertex of the outside region, not only
the two attaching roots. -/
theorem exists_degreeTargetSelection61
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c) :
    Nonempty (DegreeTargetSelection61 c) := by
  classical
  have hexists : ∀ v : V, ∃ i : Fin 35,
      degreeTargetAt61 i = fourColorDegreeTuple c v := by
    intro v
    exact exists_degreeTargetAt61_of_mem
      (fourColorDegreeTuple_mem_degreeTargets61 hcard c hc v)
  choose index hindex using hexists
  exact ⟨{ index := index, index_eq := hindex }⟩

/-- The six exact cardinality equations, specialized to the actual degrees
and actual intersection size of the selected roots. -/
def ExactAttachingRegionCards
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (delta : FourColor) (u v : V) : Prop :=
  let du := colorDegree c delta u
  let dv := colorDegree c delta v
  let k := #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v)
  #(attachingRegionFinset c delta u v .leftRoot) = 1 ∧
  #(attachingRegionFinset c delta u v .rightRoot) = 1 ∧
  #(attachingRegionFinset c delta u v .common) = k ∧
  #(attachingRegionFinset c delta u v .leftOnly) = du - k ∧
  #(attachingRegionFinset c delta u v .rightOnly) = dv - k ∧
  #(attachingRegionFinset c delta u v .outside) =
    59 - du - dv + k

/-- All currently proved finite information attached to one selected pair.
The original configuration is retained verbatim, so all of its asymmetric
attaching inequalities remain available to a future checker. -/
structure FiniteObstructionInterface
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (u v : V) where
  hostCard : Fintype.card V = 61
  attaching : CataloguedAttachingConfiguration c hc delta u v

  leftDegreeTarget : Fin 35
  leftDegreeTarget_eq :
    degreeTargetAt61 leftDegreeTarget = fourColorDegreeTuple c u
  rightDegreeTarget : Fin 35
  rightDegreeTarget_eq :
    degreeTargetAt61 rightDegreeTarget = fourColorDegreeTuple c v

  partitionLabels : AttachingPartitionLabels c delta u v
    (colorDegree c delta u)
    (colorDegree c delta v)
    #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v)
  partitionCards : ExactAttachingRegionCards c delta u v

  criticalOverlap : LabeledCriticalTemplateOverlap
    #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v)
  leftTemplateOrder :
    colorDegree c delta u = criticalTemplateOrder criticalOverlap.leftKind
  rightTemplateOrder :
    colorDegree c delta v = criticalTemplateOrder criticalOverlap.rightKind
  overlapCompatible :
    ∀ i j : Fin
        #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v),
      i ≠ j →
      criticalOverlap.overlap.relativeColors
          (criticalTemplateColoring criticalOverlap.leftKind
            (criticalOverlap.overlap.leftVertex i)
            (criticalOverlap.overlap.leftVertex j)) =
        criticalTemplateColoring criticalOverlap.rightKind
          (criticalOverlap.overlap.rightVertex i)
          (criticalOverlap.overlap.rightVertex j)

/-- Extract the complete finite interface from one already catalogued
attaching configuration. -/
theorem finiteObstructionInterface_of_config
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 61)
    (c : EdgeColoring V FourColor) (hc : NoMonochromaticTriangle c)
    (delta : FourColor) (u v : V)
    (hconfig : CataloguedAttachingConfiguration c hc delta u v) :
    Nonempty (FiniteObstructionInterface c hc delta u v) := by
  obtain ⟨huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
      huCatalogue, hvCatalogue⟩ := hconfig
  have hconfig' : CataloguedAttachingConfiguration c hc delta u v :=
    ⟨huv, hedge, hgamma, huLower, huUpper,
      hvLower, hvUpper, hkLower, hkUpper, hsharp, hplus,
      huCatalogue, hvCatalogue⟩

  have huTargetMem :=
    fourColorDegreeTuple_mem_degreeTargets61 hcard c hc u
  have hvTargetMem :=
    fourColorDegreeTuple_mem_degreeTargets61 hcard c hc v
  obtain ⟨huTarget, huTargetEq⟩ :=
    exists_degreeTargetAt61_of_mem huTargetMem
  obtain ⟨hvTarget, hvTargetEq⟩ :=
    exists_degreeTargetAt61_of_mem hvTargetMem

  let k := #(colorNeighborhood c delta u ∩ colorNeighborhood c delta v)
  obtain ⟨criticalOverlap, huOrder, hvOrder⟩ :=
    exists_labeledCriticalTemplateOverlap_of_witnesses
      (k := k) c hc delta u v huCatalogue hvCatalogue (by rfl)

  have hdegreeSum :
      colorDegree c delta u + colorDegree c delta v ≤ 59 := by
    omega
  let partitionLabels := attachingPartitionLabels hcard c delta u v
    huv hedge (by rfl) (by rfl) (by rfl) hdegreeSum
  have hregionCards : ExactAttachingRegionCards c delta u v := by
    exact attachingRegion_cards hcard c delta u v huv hedge
      (by rfl) (by rfl) (by rfl) hdegreeSum

  refine ⟨{
    hostCard := hcard
    attaching := hconfig'
    leftDegreeTarget := huTarget
    leftDegreeTarget_eq := huTargetEq
    rightDegreeTarget := hvTarget
    rightDegreeTarget_eq := hvTargetEq
    partitionLabels := partitionLabels
    partitionCards := hregionCards
    criticalOverlap := criticalOverlap
    leftTemplateOrder := huOrder
    rightTemplateOrder := hvOrder
    overlapCompatible := ?_
  }⟩
  intro i j hij
  exact criticalOverlap.compatible i j hij

/-- Every good labeled K61 colouring with complete critical catalogues has a
selected pair carrying the finite interface.  This is an extraction theorem,
not an obstruction or contradiction. -/
theorem exists_finiteObstructionInterface61
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c)
    (h15 : ThreeColorCatalogueComplete 15 k15CriticalCatalogue)
    (h16 : ThreeColorCatalogueComplete 16 k16CriticalCatalogue) :
    ∃ delta : FourColor, ∃ u v : Fin 61,
      Nonempty (FiniteObstructionInterface c hc delta u v) := by
  obtain ⟨delta, u, v, hconfig⟩ :=
    exists_cataloguedAttachingConfiguration61 c hc h15 h16
  exact ⟨delta, u, v,
    finiteObstructionInterface_of_config (by simp) c hc delta u v hconfig⟩

/-- The checked K15/K16 catalogues discharge the final two hypotheses of the
finite-interface entrance theorem. -/
theorem exists_finiteObstructionInterface61_checked
    (c : EdgeColoring (Fin 61) FourColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ delta : FourColor, ∃ u v : Fin 61,
      Nonempty (FiniteObstructionInterface c hc delta u v) :=
  exists_finiteObstructionInterface61 c hc
    k15CriticalCatalogue_complete k16CriticalCatalogue_complete

#print axioms R4333.exists_degreeTargetAt61_of_mem
#print axioms R4333.exists_degreeTargetSelection61
#print axioms R4333.finiteObstructionInterface_of_config
#print axioms R4333.exists_finiteObstructionInterface61
#print axioms R4333.exists_finiteObstructionInterface61_checked

end R4333
