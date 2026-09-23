import R4333Lean.ProfileDUUUFiveSupportPositionSymmetry
import R4333Lean.ProfileDDegreeNineFullNeighborhoodNormalForm61

/-!
# Finite boundary for the UUU degree-nine five-support branch

The selected-position quotient previously retained only the interval
`9 ≤ d ≤ 10`.  This module proves that its certified transports preserve the
exact value `d = 9`, and then combines the quotient with the full-neighbourhood
normal form.  It also identifies the three concrete groups of sizes `5,5,4`
with the complete colour-neighbourhood parts of the normalized critical
`K15`.  Thus no choice of a proper subset of a template part remains.
-/

namespace R4333
namespace ProfileDUUUDegreeNineFiniteBoundary61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDSelectedPositionTransport
open ProfileDFourRowKindSymmetry
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDDegreeNineFullNeighborhoodNormalForm61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SemanticFiveSupport :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension
abbrev PositionedFiveSupport :=
  ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport
abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex

/-! ## Exact degree is preserved by every position transport -/

theorem normalizeSupportBlockZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFiveSupport .uuu 0 selected) :
    colorDegree
        (normalizeSupportBlockZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (k15Representative selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0) (blockVertex 0 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermZero .uuu selected).symm)
      (blockRootColor 0)
      (blockVertex 0 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermZero_uuu_selected selected,
    Equiv.symm_apply_apply]

theorem normalizeSupportBlockOne_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFiveSupport .uuu 1 selected) :
    colorDegree
        (normalizeSupportBlockOne selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1)
        (blockVertex 1 (k15Representative selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1) (blockVertex 1 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermOne .uuu selected).symm)
      (blockRootColor 1)
      (blockVertex 1 (k15Representative selected).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermOne_uuu_selected selected,
    Equiv.symm_apply_apply]

theorem normalizeSupportBlockTwo_tailOwnDegree
    (selected : Fin 16)
    (branch : PositionedFiveSupport .uuu 2 selected) :
    colorDegree
        (normalizeSupportBlockTwo selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 selected.val) := by
  change colorDegree
      (relabelVertices
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (selectedPositionPermTwo .uuu selected).symm)
      (blockRootColor 2) (blockVertex 2 (Fin.last 15).val) = _
  rw [colorDegree_relabelVertices]
  rw [← selectedPositionPermTwo_uuu_selected selected,
    Equiv.symm_apply_apply]

theorem swapSupportBlockOneToZero_tailOwnDegree
    (selected : Fin 15)
    (branch : PositionedFiveSupport .uuu 1 selected) :
    colorDegree
        (swapSupportBlockOneToZero selected branch).toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 0)
        (blockVertex 0 (blockOneTargetPosition selected).val) =
      colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 1) (blockVertex 1 selected.val) := by
  change colorDegree
      (mapEdgeColors
        (relabelVertices
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (tailVertexPerm .uuu))
        hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockZeroRoot,
    tailVertexPerm_uuu_blockOneTarget]

/-- Exact degree nine, not merely the interval `[9,10]`, survives the
certified four-position quotient. -/
theorem exists_positioned_degreeNine_representative
    (ext : SemanticFiveSupport .uuu)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 9) :
    ∃ index : SelectedIndex,
      index ∈ uuuRepresentatives ∧
        ∃ branch : PositionedFiveSupport .uuu index.1 index.2,
          colorDegree
              branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
              (blockRootColor index.1)
              (blockVertex index.1 index.2.val) = 9 := by
  cases ext with
  | mk degree block position allFive lower upper =>
      fin_cases block
      · let source : PositionedFiveSupport .uuu 0 position :=
          ⟨degree, allFive, lower, upper⟩
        let normalized := normalizeSupportBlockZero position source
        have hnormalized :
            colorDegree
                normalized.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
                (blockRootColor 0)
                (blockVertex 0 (k15Representative position).val) = 9 := by
          rw [normalizeSupportBlockZero_tailOwnDegree]
          exact hdegree
        refine ⟨k15Index (k15Representative position),
          k15Index_representative_mem position, normalized, ?_⟩
        simpa [k15Index] using hnormalized
      · let source : PositionedFiveSupport .uuu 1 position :=
          ⟨degree, allFive, lower, upper⟩
        let swapped := swapSupportBlockOneToZero position source
        let normalized := normalizeSupportBlockZero
          (blockOneTargetPosition position) swapped
        have hnormalized :
            colorDegree
                normalized.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
                (blockRootColor 0)
                (blockVertex 0 (k15Representative
                  (blockOneTargetPosition position)).val) = 9 := by
          rw [normalizeSupportBlockZero_tailOwnDegree,
            swapSupportBlockOneToZero_tailOwnDegree]
          exact hdegree
        refine ⟨k15Index (k15Representative
            (blockOneTargetPosition position)),
          k15Index_representative_mem (blockOneTargetPosition position),
          normalized, ?_⟩
        simpa [k15Index] using hnormalized
      · let source : PositionedFiveSupport .uuu 2 position :=
          ⟨degree, allFive, lower, upper⟩
        let normalized := normalizeSupportBlockTwo position source
        have hnormalized :
            colorDegree
                normalized.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
                (blockRootColor 2)
                (blockVertex 2 (Fin.last 15).val) = 9 := by
          rw [normalizeSupportBlockTwo_tailOwnDegree]
          exact hdegree
        refine ⟨k16Index (Fin.last 15), k16Index_last_mem,
          normalized, ?_⟩
        simpa [k16Index] using hnormalized

/-! ## The concrete `5+5+4` groups are entire template parts -/

noncomputable def freeLabelEmbedding
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    FiveVertex ↪ Fin 15 where
  toFun a := normal.vertex.symm (restLabel (.inl (.inl a)))
  inj' := by
    intro a b hab
    have hlabel := normal.vertex.symm.injective hab
    have hoption := fin15EquivRootedRest.symm.injective hlabel
    exact Sum.inl.inj (Sum.inl.inj (Option.some.inj hoption))

noncomputable def largeLabelEmbedding
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    FiveVertex ↪ Fin 15 where
  toFun a := normal.vertex.symm (restLabel (.inl (.inr a)))
  inj' := by
    intro a b hab
    have hlabel := normal.vertex.symm.injective hab
    have hoption := fin15EquivRootedRest.symm.injective hlabel
    exact Sum.inr.inj (Sum.inl.inj (Option.some.inj hoption))

noncomputable def smallLabelEmbedding
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    Fin 4 ↪ Fin 15 where
  toFun a := normal.vertex.symm (restLabel (.inr a))
  inj' := by
    intro a b hab
    have hlabel := normal.vertex.symm.injective hab
    have hoption := fin15EquivRootedRest.symm.injective hlabel
    exact Sum.inr.inj (Option.some.inj hoption)

noncomputable def freeLabelSet
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    Finset (Fin 15) := Finset.univ.image (freeLabelEmbedding normal)

noncomputable def largeLabelSet
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    Finset (Fin 15) := Finset.univ.image (largeLabelEmbedding normal)

noncomputable def smallLabelSet
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    Finset (Fin 15) := Finset.univ.image (smallLabelEmbedding normal)

theorem freeLabelSet_eq_colorNeighborhood
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    freeLabelSet normal =
      colorNeighborhood (k15Template normal.twisted)
        (freeDecodedColor ext) (normal.vertex.symm restoredRootLabel) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [freeLabelSet] at hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_colorNeighborhood _ _ _ _).2
    exact ⟨normal.vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inl (.inl a))).symm,
      normal.rootToFreeConstant a⟩
  · have htarget :
        (colorNeighborhood (k15Template normal.twisted)
          (freeDecodedColor ext)
          (normal.vertex.symm restoredRootLabel)).card = 5 :=
      normal.freeDegree
    have hsource : (freeLabelSet normal).card = 5 := by
      rw [freeLabelSet, Finset.card_image_of_injective _
        (freeLabelEmbedding normal).injective]
      decide
    omega

theorem largeLabelSet_eq_colorNeighborhood
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    largeLabelSet normal =
      colorNeighborhood (k15Template normal.twisted)
        (largeDecodedColor skeleton)
        (normal.vertex.symm restoredRootLabel) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [largeLabelSet] at hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_colorNeighborhood _ _ _ _).2
    exact ⟨normal.vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inl (.inr a))).symm,
      normal.rootToLargeConstant a⟩
  · have htarget :
        (colorNeighborhood (k15Template normal.twisted)
          (largeDecodedColor skeleton)
          (normal.vertex.symm restoredRootLabel)).card = 5 :=
      normal.largeDegree
    have hsource : (largeLabelSet normal).card = 5 := by
      rw [largeLabelSet, Finset.card_image_of_injective _
        (largeLabelEmbedding normal).injective]
      decide
    omega

theorem smallLabelSet_eq_colorNeighborhood
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    smallLabelSet normal =
      colorNeighborhood (k15Template normal.twisted)
        (smallDecodedColor skeleton)
        (normal.vertex.symm restoredRootLabel) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [smallLabelSet] at hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_colorNeighborhood _ _ _ _).2
    exact ⟨normal.vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inr a)).symm,
      normal.rootToSmallConstant a⟩
  · have htarget :
        (colorNeighborhood (k15Template normal.twisted)
          (smallDecodedColor skeleton)
          (normal.vertex.symm restoredRootLabel)).card = 4 :=
      normal.smallDegree
    have hsource : (smallLabelSet normal).card = 4 := by
      rw [smallLabelSet, Finset.card_image_of_injective _
        (smallLabelEmbedding normal).injective]
      decide
    omega

/-- Exact canonical partition retained for the finite residual problem. -/
structure ExactDegreeNineTemplatePartition
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} (skeleton : DegreeNineSkeleton ext)
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) : Prop where
  freePart : freeLabelSet normal =
    colorNeighborhood (k15Template normal.twisted)
      (freeDecodedColor ext) (normal.vertex.symm restoredRootLabel)
  largePart : largeLabelSet normal =
    colorNeighborhood (k15Template normal.twisted)
      (largeDecodedColor skeleton) (normal.vertex.symm restoredRootLabel)
  smallPart : smallLabelSet normal =
    colorNeighborhood (k15Template normal.twisted)
      (smallDecodedColor skeleton) (normal.vertex.symm restoredRootLabel)

theorem exactDegreeNineTemplatePartition
    {kind : ProfileDTripleJoinReduction.Kind}
    {ext : SemanticFiveSupport kind} {skeleton : DegreeNineSkeleton ext}
    (normal : DegreeNineFullNeighborhoodNormalForm ext skeleton) :
    ExactDegreeNineTemplatePartition skeleton normal := by
  exact ⟨freeLabelSet_eq_colorNeighborhood normal,
    largeLabelSet_eq_colorNeighborhood normal,
    smallLabelSet_eq_colorNeighborhood normal⟩

/-! ## Exact cardinality of the residual local normal forms -/

/-- A concrete four-element indexing of the already-certified position
representatives.  Keeping this as a function from `Fin 4` makes the later
cardinality statement independent of list/subtype bookkeeping. -/
def uuuRepresentativeIndexBySlot (slot : Fin 4) : SelectedIndex :=
  ![k15Index 0, k15Index 1, k15Index 2, k16Index (Fin.last 15)] slot

theorem uuuRepresentativeIndexBySlot_mem (slot : Fin 4) :
    uuuRepresentativeIndexBySlot slot ∈ uuuRepresentatives := by
  fin_cases slot <;> decide

theorem uuuRepresentativeIndexBySlot_injective :
    Function.Injective uuuRepresentativeIndexBySlot := by
  intro first second heq
  fin_cases first <;> fin_cases second <;> simp_all [uuuRepresentativeIndexBySlot,
    k15Index, k16Index]

theorem exists_uuuRepresentativeSlot_of_mem
    {index : SelectedIndex} (hindex : index ∈ uuuRepresentatives) :
    ∃ slot : Fin 4, uuuRepresentativeIndexBySlot slot = index := by
  simp only [uuuRepresentatives, List.mem_cons, List.not_mem_nil] at hindex
  rcases hindex with hindex | hindex | hindex | hindex
  · exact ⟨0, hindex.symm⟩
  · exact ⟨1, hindex.symm⟩
  · exact ⟨2, hindex.symm⟩
  · rcases hindex with hindex | hfalse
    · exact ⟨3, hindex.symm⟩
    · contradiction

/-- The exact-degree quotient can be indexed by `Fin 4`, rather than merely
returning membership in the representative list. -/
theorem exists_positioned_degreeNine_indexed_representative
    (ext : SemanticFiveSupport .uuu)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 9) :
    ∃ slot : Fin 4,
      ∃ branch : PositionedFiveSupport .uuu
          (uuuRepresentativeIndexBySlot slot).1
          (uuuRepresentativeIndexBySlot slot).2,
        colorDegree
            branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockRootColor (uuuRepresentativeIndexBySlot slot).1)
            (blockVertex (uuuRepresentativeIndexBySlot slot).1
              (uuuRepresentativeIndexBySlot slot).2.val) = 9 := by
  obtain ⟨index, hindex, branch, hbranch⟩ :=
    exists_positioned_degreeNine_representative ext hdegree
  obtain ⟨slot, hslot⟩ := exists_uuuRepresentativeSlot_of_mem hindex
  subst index
  exact ⟨slot, branch, hbranch⟩

/-- For a fixed deficient colour, the template bit and orbit-reduced root
label together form a four-element type: one untwisted case and three
twisted cases. -/
def DegreeNineTemplateRootCase (deficient : ThreeColor) :=
  Σ twisted : Bool, ↥(degreeNineRootRepresentativeSet twisted deficient)

noncomputable instance degreeNineTemplateRootCaseFintype
    (deficient : ThreeColor) :
    Fintype (DegreeNineTemplateRootCase deficient) := by
  unfold DegreeNineTemplateRootCase
  infer_instance

theorem degreeNineTemplateRootCase_card (deficient : ThreeColor) :
    Fintype.card (DegreeNineTemplateRootCase deficient) = 4 := by
  classical
  change Fintype.card
    (Σ twisted : Bool,
      ↥(degreeNineRootRepresentativeSet twisted deficient)) = 4
  rw [Fintype.card_sigma]
  simp [degreeNineRootRepresentativeSet_card]

/-- The deficient decoded colour belonging to one position representative
and one of the two possible physical placements of the foreign `5+4`
split. -/
noncomputable def residualDeficientColor
    (slot : Fin 4) (firstLarge : Bool) : ThreeColor :=
  decodeNonBlockColor
    (blockRootColor (uuuRepresentativeIndexBySlot slot).1)
    (blockRootColor (smallForeignBlock
      (uuuRepresentativeIndexBySlot slot).1 firstLarge))

/-- The deficient abstract colour is independent of the selected-position
slot.  It records only which physical foreign block is the four-set. -/
theorem residualDeficientColor_eq (slot : Fin 4) (firstLarge : Bool) :
    residualDeficientColor slot firstLarge =
      if firstLarge then (2 : ThreeColor) else 1 := by
  cases firstLarge <;> fin_cases slot
  all_goals
    change decodeNonBlockColor _ _ = _
    apply SingleRootStarWitness61.canonicalPalette_injective
    rw [canonicalPalette_decodeNonBlockColor _ _
      (blockRootColor_injective.ne (smallForeignBlock_ne_source _ _))]
    decide

theorem residualUntwistedRootRepresentativeSet
    (slot : Fin 4) (firstLarge : Bool) :
    degreeNineRootRepresentativeSet false
        (residualDeficientColor slot firstLarge) =
      if firstLarge then ({1} : Finset (Fin 15)) else {2} := by
  rw [residualDeficientColor_eq]
  cases firstLarge <;> decide

theorem residualTwistedRootRepresentativeSet
    (slot : Fin 4) (firstLarge : Bool) :
    degreeNineRootRepresentativeSet true
        (residualDeficientColor slot firstLarge) =
      if firstLarge then ({2, 6, 9} : Finset (Fin 15)) else {1, 4, 12} := by
  rw [residualDeficientColor_eq]
  cases firstLarge <;> decide

/-- Semantic coverage of the four-element template/root factor.  Every
exact-degree-nine branch already placed in one of the four position slots
produces a skeleton, an orbit-reduced normal form, and an inhabitant of the
corresponding residual root-case type. -/
theorem exists_templateRootCase_for_positioned_degreeNine
    (slot : Fin 4)
    (branch : PositionedFiveSupport .uuu
      (uuuRepresentativeIndexBySlot slot).1
      (uuuRepresentativeIndexBySlot slot).2)
    (hdegree :
      colorDegree
          branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor (uuuRepresentativeIndexBySlot slot).1)
          (blockVertex (uuuRepresentativeIndexBySlot slot).1
            (uuuRepresentativeIndexBySlot slot).2.val) = 9) :
    ∃ skeleton : DegreeNineSkeleton branch.toSemantic,
      ∃ normal : OrbitReducedDegreeNineFullNeighborhoodNormalForm
          branch.toSemantic skeleton,
        ∃ rootCase : DegreeNineTemplateRootCase
            (residualDeficientColor slot skeleton.firstLarge),
          rootCase.1 = normal.twisted ∧
            rootCase.2.1 = normal.vertex.symm restoredRootLabel := by
  have hsemantic :
      colorDegree
          branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor branch.toSemantic.block)
          (blockVertex branch.toSemantic.block branch.toSemantic.position.val) = 9 := by
    simpa [PositionedFiveSupport.toSemantic] using hdegree
  obtain ⟨skeleton⟩ := exists_degreeNineSkeleton branch.toSemantic hsemantic
  obtain ⟨normal⟩ :=
    exists_orbitReducedDegreeNineFullNeighborhoodNormalForm skeleton
  have hroot :
      normal.vertex.symm restoredRootLabel ∈
        degreeNineRootRepresentativeSet normal.twisted
          (residualDeficientColor slot skeleton.firstLarge) := by
    simpa [smallDecodedColor, residualDeficientColor,
      PositionedFiveSupport.toSemantic] using normal.rootRepresentative
  let rootCase : DegreeNineTemplateRootCase
      (residualDeficientColor slot skeleton.firstLarge) :=
    ⟨normal.twisted, ⟨normal.vertex.symm restoredRootLabel, hroot⟩⟩
  exact ⟨skeleton, normal, rootCase, rfl, rfl⟩

/-- The complete local finite boundary after all currently proved semantic
reductions: four selected-position orbits, two orientations of the foreign
`5+4` split, and four `(template bit, root orbit)` cases. -/
noncomputable def DegreeNineResidualLocalCase :=
  Σ slot : Fin 4, Σ firstLarge : Bool,
    DegreeNineTemplateRootCase (residualDeficientColor slot firstLarge)

noncomputable instance degreeNineResidualLocalCaseFintype :
    Fintype DegreeNineResidualLocalCase := by
  unfold DegreeNineResidualLocalCase
  infer_instance

/-- There are exactly `4 * 2 * (1 + 3) = 32` local normal-form cases at the
remaining boundary. -/
theorem degreeNineResidualLocalCase_card :
    Fintype.card DegreeNineResidualLocalCase = 32 := by
  classical
  change Fintype.card
    (Σ slot : Fin 4, Σ firstLarge : Bool,
      DegreeNineTemplateRootCase
        (residualDeficientColor slot firstLarge)) = 32
  rw [Fintype.card_sigma]
  simp [degreeNineTemplateRootCase_card]

#print axioms normalizeSupportBlockZero_tailOwnDegree
#print axioms swapSupportBlockOneToZero_tailOwnDegree
#print axioms exists_positioned_degreeNine_representative
#print axioms exists_positioned_degreeNine_indexed_representative
#print axioms exists_templateRootCase_for_positioned_degreeNine
#print axioms exactDegreeNineTemplatePartition
#print axioms residualDeficientColor_eq
#print axioms residualUntwistedRootRepresentativeSet
#print axioms residualTwistedRootRepresentativeSet
#print axioms degreeNineResidualLocalCase_card

end ProfileDUUUDegreeNineFiniteBoundary61
end R4333
