import R4333Lean.ProfileDUUUDegreeNineBlockTwoSwap61

/-! Continuation-authored (locks/duuu), 2026-08-05.
Twisted case (slot 3, firstLarge=false, twisted=true, root 4) — generated from
ProfileDUUUDegreeNineStrongCase61 by role-aware substitution (label sites ->
k15Template true/root 12; physical sites unchanged). -/

/-!
# A concrete finite boundary for the strongest UUU degree-nine case

After the equal-K15 swap, the block-two position only needs the physical
orientation in which block one is the five-set and block zero is the
four-set.  This file studies the untwisted neighbourhood/root representative
of that reduced case.  It proves two additional facts which were not part of
the 28-case interface:

* the physical five- and four-supports lie in explicit kernel-enumerated
  families of respectively 11 and 60 compatible subsets of the two
  canonical K15s (the latter is cut from 90 independent four-sets);
* all `5 x 5`, `5 x 4`, and `4 x 5` local cross edges are exactly the edges
  of the fixed untwisted K15 normal form after decoding the selected colour.

The result is a finite semantic interface, not a contradiction.  In
particular, the local families are nonempty, so eliminating this case still
requires completing the remaining rows/cross-block edges.
-/

namespace R4333
namespace ContinuationDegreeNineTwistedRoot4Case61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDDegreeNineFullNeighborhoodNormalForm61
open ProfileDUUUDegreeNineFiniteBoundary61
open ProfileDUUUDegreeNineCaseRealization61
open ProfileDUUUDegreeNineBlockTwoSwap61
open CriticalK15PartitionClassification

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev ResidualCase := DegreeNineResidualLocalCase

/-! ## The fixed reduced case -/

noncomputable def twistedRoot4RootCase :
    DegreeNineTemplateRootCase (residualDeficientColor 3 false) :=
  ⟨true, ⟨4, by
    rw [residualTwistedRootRepresentativeSet 3 false]
    decide⟩⟩

noncomputable def twistedRoot4Case : ResidualCase :=
  ⟨3, false, twistedRoot4RootCase⟩

abbrev TwistedRoot4Realization := DegreeNineCaseRealization twistedRoot4Case

theorem TwistedRoot4Realization.firstLarge_eq_false
    (realization : TwistedRoot4Realization) :
    realization.skeleton.firstLarge = false := by
  simpa [twistedRoot4Case] using realization.caseFirstLarge_eq.symm

theorem TwistedRoot4Realization.twisted_eq_false
    (realization : TwistedRoot4Realization) :
    realization.normal.twisted = true := by
  simpa [twistedRoot4Case, twistedRoot4RootCase] using realization.caseTwisted_eq.symm

theorem TwistedRoot4Realization.rootLabel_eq_two
    (realization : TwistedRoot4Realization) :
    realization.normal.vertex.symm restoredRootLabel = 4 := by
  simpa [twistedRoot4Case, twistedRoot4RootCase] using realization.caseRoot_eq.symm

theorem TwistedRoot4Realization.branchBlock_eq_two
    (realization : TwistedRoot4Realization) :
    realization.branch.toSemantic.block = 2 := by
  change (uuuRepresentativeIndexBySlot (caseSlot twistedRoot4Case)).1 = 2
  simp [twistedRoot4Case, caseSlot, uuuRepresentativeIndexBySlot,
    ProfileDUUUFiveSupportPositionSymmetry.k16Index]

theorem TwistedRoot4Realization.freeDecodedColor_eq_zero
    (realization : TwistedRoot4Realization) :
    freeDecodedColor realization.branch.toSemantic = 0 := by
  change decodeNonBlockColor (blockRootColor 2) 0 = 0
  apply SingleRootStarWitness61.canonicalPalette_injective
  rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
  rfl

theorem TwistedRoot4Realization.largeDecodedColor_eq_two
    (realization : TwistedRoot4Realization) :
    largeDecodedColor realization.skeleton = 2 := by
  rw [largeDecodedColor, realization.firstLarge_eq_false]
  change decodeNonBlockColor (blockRootColor 2)
      (blockRootColor (largeForeignBlock 2 false)) = 2
  apply SingleRootStarWitness61.canonicalPalette_injective
  rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
  rfl

theorem TwistedRoot4Realization.smallDecodedColor_eq_one
    (realization : TwistedRoot4Realization) :
    smallDecodedColor realization.skeleton = 1 := by
  calc
    smallDecodedColor realization.skeleton =
        residualDeficientColor 3 false :=
      realization.smallDecodedColor_eq
    _ = 1 := by rw [residualDeficientColor_eq]; rfl

/-! ## Exact finite physical support families -/

def independentSupportCandidates (n : Nat) (q : ThreeColor) :
    Finset (Finset (Fin 15)) :=
  ((Finset.univ : Finset (Fin 15)).powersetCard n).filter fun support =>
    colorViolationCount (k15Template false) q support = 0

theorem mem_independentSupportCandidates_iff
    (n : Nat) (q : ThreeColor) (support : Finset (Fin 15)) :
    support ∈ independentSupportCandidates n q ↔
      support.card = n ∧
        IsColorIndependentSet (k15Template false) q support := by
  simp [independentSupportCandidates, colorViolationCount_eq_zero_iff]

/-- The five-set in physical block one must be one of eleven maximum
independent sets of its omitted-source colour. -/
def twistedRoot4LargeSupportCandidates : Finset (Finset (Fin 15)) :=
  independentSupportCandidates 5 2

/-- The four-set in physical block zero must be one of ninety independent
four-subsets.  Later compatibility with the normalized K15 cuts this further;
the present theorem records the first exact physical boundary. -/
def twistedRoot4SmallSupportCandidates : Finset (Finset (Fin 15)) :=
  independentSupportCandidates 4 2

/-- The normalized four-set for the fixed untwisted root representative. -/
def twistedRoot4SmallLabelSet : Finset (Fin 15) :=
  colorNeighborhood (k15Template true) 1 4

/-- Host block zero uses palette `[0,2,3]`; after deleting selected colour
three, its surviving local colours `0,1` decode to normalized colours `0,2`.
The value at local colour two is irrelevant on an independent support. -/
def twistedRoot4SmallPhysicalColorMap : ThreeColor → ThreeColor := ![0, 2, 0]

def twistedRoot4SmallPhysicalColoring : EdgeColoring (Fin 15) ThreeColor where
  color left right := twistedRoot4SmallPhysicalColorMap
    (k15Template false left right)
  color_symm left right := by
    exact congrArg twistedRoot4SmallPhysicalColorMap
      ((k15Template false).color_symm left right)

def StrongSmallSupportCompatible (support : Finset (Fin 15)) : Prop :=
  ∃ equivalence : ↑twistedRoot4SmallLabelSet ≃ ↑support,
    ∀ left right, left ≠ right →
      k15Template true left.1 right.1 =
        twistedRoot4SmallPhysicalColoring (equivalence left).1
          (equivalence right).1

instance (support : Finset (Fin 15)) :
    Decidable (StrongSmallSupportCompatible support) := by
  unfold StrongSmallSupportCompatible
  infer_instance

/-- Internal K4 compatibility with the fixed normalized neighbourhood cuts
the ninety physical four-sets to sixty. -/
def twistedRoot4CompatibleSmallSupportCandidates : Finset (Finset (Fin 15)) :=
  twistedRoot4SmallSupportCandidates.filter StrongSmallSupportCompatible

theorem twistedRoot4LargeSupportCandidates_card :
    twistedRoot4LargeSupportCandidates.card = 11 := by
  decide

theorem twistedRoot4SmallSupportCandidates_card :
    twistedRoot4SmallSupportCandidates.card = 90 := by
  decide

theorem twistedRoot4CompatibleSmallSupportCandidates_card :
    twistedRoot4CompatibleSmallSupportCandidates.card = 60 := by
  decide

abbrev StrongPhysicalSupportPair :=
  ↑twistedRoot4LargeSupportCandidates ×
    ↑twistedRoot4CompatibleSmallSupportCandidates

theorem twistedRoot4PhysicalSupportPair_card :
    Fintype.card StrongPhysicalSupportPair = 660 := by
  simp [StrongPhysicalSupportPair, twistedRoot4LargeSupportCandidates_card,
    twistedRoot4CompatibleSmallSupportCandidates_card]

noncomputable def twistedRoot4LargeSupport (realization : TwistedRoot4Realization) :
    Finset (Fin 15) := by
  simpa [ProfileDTripleJoinReduction.blockSize] using
    (foreignOwnSupport realization.branch.toSemantic 1)

noncomputable def smallPhysicalEmbedding
    (realization : TwistedRoot4Realization) : Fin 4 ↪ Fin 15 where
  toFun index := ⟨(realization.skeleton.smallSupport.embedding index).val, by
    simpa [realization.firstLarge_eq_false,
      realization.branchBlock_eq_two, smallForeignBlock, firstForeignBlock,
      ProfileDTripleJoinReduction.blockSize] using
        (realization.skeleton.smallSupport.embedding index).isLt⟩
  inj' := by
    intro left right h
    have hv : (realization.skeleton.smallSupport.embedding left).val =
        (realization.skeleton.smallSupport.embedding right).val :=
      congrArg (fun x : Fin 15 => x.val) h
    apply realization.skeleton.smallSupport.embedding.injective
    exact Fin.ext hv

noncomputable def twistedRoot4SmallSupport (realization : TwistedRoot4Realization) :
    Finset (Fin 15) :=
  Finset.univ.image (smallPhysicalEmbedding realization)

private theorem support_blockOne_independent
    (realization : TwistedRoot4Realization) :
    IsColorIndependentSet (k15Template false) 2
      (twistedRoot4LargeSupport realization) := by
  intro left hleft right hright hlr
  have hleft' : left ∈ foreignOwnSupport realization.branch.toSemantic 1 := by
    change left ∈ twistedRoot4LargeSupport realization
    exact hleft
  have hright' : right ∈ foreignOwnSupport realization.branch.toSemantic 1 := by
    change right ∈ twistedRoot4LargeSupport realization
    exact hright
  have hnotOwn := foreignOwnSupport_edge_ne_own
    realization.branch.toSemantic 1 (by
      change (1 : Fin 3) ≠ 2
      decide) left hleft' right hright' hlr
  rw [realization.branchBlock_eq_two] at hnotOwn
  have hnotOwn' :
      realization.branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 1 left.val) (blockVertex 1 right.val) ≠
        blockRootColor 2 := by
    change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 1 left.val) (blockVertex 1 right.val) ≠
      blockRootColor 2 at hnotOwn
    exact hnotOwn
  intro hedge
  apply hnotOwn'
  rw [ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
    realization.branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail
    1 (by rfl) left right hlr]
  change canonicalPalette 2 (k15Template false left right) = blockRootColor 2
  rw [hedge]
  rfl

private theorem support_blockZero_independent
    (realization : TwistedRoot4Realization) :
    IsColorIndependentSet (k15Template false) 2
      (twistedRoot4SmallSupport realization) := by
  intro left hleft right hright hlr
  obtain ⟨leftIndex, _hleftIndex, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightIndex, _hrightIndex, rfl⟩ := Finset.mem_image.mp hright
  have hindex : leftIndex ≠ rightIndex := by
    intro h
    exact hlr (congrArg (smallPhysicalEmbedding realization) h)
  have hleft' := exactSupport_embedding_mem
    realization.skeleton.smallSupport leftIndex
  have hright' := exactSupport_embedding_mem
    realization.skeleton.smallSupport rightIndex
  have hnotOwn := foreignOwnSupport_edge_ne_own
    realization.branch.toSemantic
      (smallForeignBlock realization.branch.toSemantic.block
        realization.skeleton.firstLarge)
      realization.skeleton.smallSupport.targetNeSource
      (realization.skeleton.smallSupport.embedding leftIndex) hleft'
      (realization.skeleton.smallSupport.embedding rightIndex) hright'
      (realization.skeleton.smallSupport.embedding.injective.ne hindex)
  have hnotOwn' :
      realization.branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 0 (smallPhysicalEmbedding realization leftIndex).val)
          (blockVertex 0 (smallPhysicalEmbedding realization rightIndex).val) ≠
        blockRootColor 2 := by
    simpa [tailBlockColoring, pullbackColoring, smallPhysicalEmbedding,
      realization.firstLarge_eq_false, realization.branchBlock_eq_two,
      smallForeignBlock, firstForeignBlock,
      ProfileDTripleJoinReduction.blockSize] using hnotOwn
  intro hedge
  apply hnotOwn'
  rw [ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
    realization.branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail
    0 (by rfl) (smallPhysicalEmbedding realization leftIndex)
      (smallPhysicalEmbedding realization rightIndex) hlr]
  change canonicalPalette 1
      (k15Template false (smallPhysicalEmbedding realization leftIndex)
        (smallPhysicalEmbedding realization rightIndex)) = blockRootColor 2
  rw [hedge]
  rfl

theorem TwistedRoot4Realization.largeSupport_mem_candidates
    (realization : TwistedRoot4Realization) :
    twistedRoot4LargeSupport realization ∈
      twistedRoot4LargeSupportCandidates := by
  change twistedRoot4LargeSupport realization ∈ independentSupportCandidates 5 2
  rw [mem_independentSupportCandidates_iff]
  constructor
  · have hcard := degreeNineSkeleton_blockTwo_blockOne_card
      realization.skeleton
    rw [realization.firstLarge_eq_false] at hcard
    change (foreignOwnSupport realization.branch.toSemantic 1).card = 5
    exact hcard
  · exact support_blockOne_independent realization

theorem TwistedRoot4Realization.smallSupport_mem_candidates
    (realization : TwistedRoot4Realization) :
    twistedRoot4SmallSupport realization ∈
      twistedRoot4SmallSupportCandidates := by
  change twistedRoot4SmallSupport realization ∈ independentSupportCandidates 4 2
  rw [mem_independentSupportCandidates_iff]
  constructor
  · rw [twistedRoot4SmallSupport,
      Finset.card_image_of_injective _
        (smallPhysicalEmbedding realization).injective]
    simp
  · exact support_blockZero_independent realization

/-! ## The fixed normal-form labels and all local cross edges -/

noncomputable def freeLabel (realization : TwistedRoot4Realization)
    (a : FiveVertex) : Fin 15 :=
  realization.normal.vertex.symm (restLabel (.inl (.inl a)))

noncomputable def largeLabel (realization : TwistedRoot4Realization)
    (a : FiveVertex) : Fin 15 :=
  realization.normal.vertex.symm (restLabel (.inl (.inr a)))

noncomputable def smallLabel (realization : TwistedRoot4Realization)
    (a : Fin 4) : Fin 15 :=
  realization.normal.vertex.symm (restLabel (.inr a))

private theorem restLabel_injective : Function.Injective restLabel := by
  intro x y hxy
  apply Option.some.inj
  simpa [restLabel] using congrArg fin15EquivRootedRest hxy

private theorem freeLabel_injective (realization : TwistedRoot4Realization) :
    Function.Injective (freeLabel realization) := by
  intro a b hab
  apply Sum.inl.inj
  apply Sum.inl.inj
  apply restLabel_injective
  exact realization.normal.vertex.symm.injective hab

private theorem largeLabel_injective (realization : TwistedRoot4Realization) :
    Function.Injective (largeLabel realization) := by
  intro a b hab
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply restLabel_injective
  exact realization.normal.vertex.symm.injective hab

private theorem smallLabel_injective (realization : TwistedRoot4Realization) :
    Function.Injective (smallLabel realization) := by
  intro a b hab
  apply Sum.inr.inj
  apply restLabel_injective
  exact realization.normal.vertex.symm.injective hab

noncomputable def embeddingEquivRange {n : Nat} {A : Type*}
    [Fintype A] [DecidableEq A] (embedding : Fin n ↪ A)
    (support : Finset A)
    (range_eq : Finset.univ.image embedding = support) :
    Fin n ≃ ↑support :=
  Equiv.ofBijective
    (fun index => ⟨embedding index, by
      rw [← range_eq]
      exact Finset.mem_image.mpr ⟨index, by simp, rfl⟩⟩)
    ⟨by
      intro left right h
      exact embedding.injective (congrArg Subtype.val h), by
      intro value
      have hmem : value.1 ∈ Finset.univ.image embedding := by
        rw [range_eq]
        exact value.2
      obtain ⟨index, _hindex, hvalue⟩ := Finset.mem_image.mp hmem
      refine ⟨index, Subtype.ext ?_⟩
      exact hvalue⟩

theorem TwistedRoot4Realization.smallPhysicalRange
    (realization : TwistedRoot4Realization) :
    Finset.univ.image (smallPhysicalEmbedding realization) =
      twistedRoot4SmallSupport realization := by
  rfl

theorem TwistedRoot4Realization.freeLabel_image
    (realization : TwistedRoot4Realization) :
    Finset.univ.image (freeLabel realization) =
      colorNeighborhood (k15Template true) 0 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro label hlabel
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hlabel
    apply (mem_colorNeighborhood _ _ _ _).2
    constructor
    · rw [← realization.rootLabel_eq_two]
      exact realization.normal.vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inl (.inl a))).symm
    · rw [← realization.rootLabel_eq_two,
        ← realization.freeDecodedColor_eq_zero,
        ← realization.twisted_eq_false]
      have hnormal := realization.normal.normalizes
        (realization.normal.vertex.symm restoredRootLabel)
        (freeLabel realization a)
        (realization.normal.vertex.symm.injective.ne
          (restoredRootLabel_ne_restLabel (.inl (.inl a))))
      rw [← hnormal]
      simpa [freeLabel, freeDecodedColor, restRootColor] using
        encodedNeighborhoodColoring_root_rest realization.skeleton
          (.inl (.inl a))
  · rw [Finset.card_image_of_injective _ (freeLabel_injective realization)]
    decide

theorem TwistedRoot4Realization.largeLabel_image
    (realization : TwistedRoot4Realization) :
    Finset.univ.image (largeLabel realization) =
      colorNeighborhood (k15Template true) 2 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro label hlabel
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hlabel
    apply (mem_colorNeighborhood _ _ _ _).2
    constructor
    · rw [← realization.rootLabel_eq_two]
      exact realization.normal.vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inl (.inr a))).symm
    · rw [← realization.rootLabel_eq_two,
        ← realization.largeDecodedColor_eq_two,
        ← realization.twisted_eq_false]
      have hnormal := realization.normal.normalizes
        (realization.normal.vertex.symm restoredRootLabel)
        (largeLabel realization a)
        (realization.normal.vertex.symm.injective.ne
          (restoredRootLabel_ne_restLabel (.inl (.inr a))))
      rw [← hnormal]
      simpa [largeLabel, largeDecodedColor, restRootColor] using
        encodedNeighborhoodColoring_root_rest realization.skeleton
          (.inl (.inr a))
  · rw [Finset.card_image_of_injective _ (largeLabel_injective realization)]
    decide

theorem TwistedRoot4Realization.smallLabel_image
    (realization : TwistedRoot4Realization) :
    Finset.univ.image (smallLabel realization) =
      colorNeighborhood (k15Template true) 1 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro label hlabel
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hlabel
    apply (mem_colorNeighborhood _ _ _ _).2
    constructor
    · rw [← realization.rootLabel_eq_two]
      exact realization.normal.vertex.symm.injective.ne
        (restoredRootLabel_ne_restLabel (.inr a)).symm
    · rw [← realization.rootLabel_eq_two,
        ← realization.smallDecodedColor_eq_one,
        ← realization.twisted_eq_false]
      have hnormal := realization.normal.normalizes
        (realization.normal.vertex.symm restoredRootLabel)
        (smallLabel realization a)
        (realization.normal.vertex.symm.injective.ne
          (restoredRootLabel_ne_restLabel (.inr a)))
      rw [← hnormal]
      simpa [smallLabel, smallDecodedColor, restRootColor] using
        encodedNeighborhoodColoring_root_rest realization.skeleton (.inr a)
  · rw [Finset.card_image_of_injective _ (smallLabel_injective realization)]
    decide

noncomputable def templateLabel (realization : TwistedRoot4Realization)
    (x : RestCoordinates) : Fin 15 :=
  realization.normal.vertex.symm (restLabel x)

theorem templateEdge_eq_encoded_rest
    (realization : TwistedRoot4Realization) (x y : RestCoordinates)
    (hxy : x ≠ y) :
    k15Template true (templateLabel realization x)
        (templateLabel realization y) =
      encodedNeighborhoodColoring realization.skeleton
        (restLabel x) (restLabel y) := by
  have hrest : restLabel x ≠ restLabel y := by
    intro h
    apply hxy
    exact restLabel_injective h
  have hlabel : templateLabel realization x ≠
      templateLabel realization y :=
    realization.normal.vertex.symm.injective.ne hrest
  have hnormal := realization.normal.normalizes
    (templateLabel realization x) (templateLabel realization y) hlabel
  rw [realization.twisted_eq_false] at hnormal
  simpa [templateLabel] using hnormal.symm

theorem encodedNeighborhoodColoring_rest_rest
    (realization : TwistedRoot4Realization) (x y : RestCoordinates) :
    encodedNeighborhoodColoring realization.skeleton
        (restLabel x) (restLabel y) =
      decodeNonBlockColor (blockRootColor 2)
        (restColoring realization.skeleton x y) := by
  change decodeNonBlockColor (blockRootColor 2)
      (rootedHostColoring realization.skeleton
        (fin15EquivRootedRest (restLabel x))
        (fin15EquivRootedRest (restLabel y))) = _
  simp [restLabel, rootedHostColoring, addRootColoring]

/-- Internal edges of the normalized four-set are also fixed, and agree
with the decoded physical block-zero K15. -/
theorem TwistedRoot4Realization.small_small_edge
    (realization : TwistedRoot4Realization) (left right : Fin 4)
    (hlr : left ≠ right) :
    k15Template true (smallLabel realization left)
        (smallLabel realization right) =
      decodeNonBlockColor (blockRootColor 2)
        (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 0
            (realization.skeleton.smallSupport.embedding left).val)
          (blockVertex 0
            (realization.skeleton.smallSupport.embedding right).val)) := by
  rw [show smallLabel realization = fun a =>
      templateLabel realization (.inr a) by rfl,
    templateEdge_eq_encoded_rest realization (.inr left) (.inr right)
      (by intro h; exact hlr (Sum.inr.inj h)),
    encodedNeighborhoodColoring_rest_rest]
  simp [restColoring, pullbackColoring, restEmbedding,
    retainedJoinedColoring, joinColoring,
    realization.firstLarge_eq_false, smallForeignBlock, firstForeignBlock,
    ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
    twistedRoot4Case, caseSlot, uuuRepresentativeIndexBySlot,
    ProfileDUUUFiveSupportPositionSymmetry.k16Index]

private theorem decode_blockZero_template
    (q : ThreeColor) (hq : q ≠ 2) :
    decodeNonBlockColor (blockRootColor 2) (canonicalPalette 1 q) =
      twistedRoot4SmallPhysicalColorMap q := by
  fin_cases q
  · change decodeNonBlockColor 3 0 = 0
    apply SingleRootStarWitness61.canonicalPalette_injective
    rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
    rfl
  · change decodeNonBlockColor 3 2 = 2
    apply SingleRootStarWitness61.canonicalPalette_injective
    rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
    rfl
  · contradiction

theorem TwistedRoot4Realization.small_small_edge_physical
    (realization : TwistedRoot4Realization) (left right : Fin 4)
    (hlr : left ≠ right) :
    k15Template true (smallLabel realization left)
        (smallLabel realization right) =
      twistedRoot4SmallPhysicalColoring
        (smallPhysicalEmbedding realization left)
        (smallPhysicalEmbedding realization right) := by
  have hedge := realization.small_small_edge left right hlr
  have hphysical : smallPhysicalEmbedding realization left ≠
      smallPhysicalEmbedding realization right :=
    (smallPhysicalEmbedding realization).injective.ne hlr
  have hedge' :
      k15Template true (smallLabel realization left)
          (smallLabel realization right) =
        decodeNonBlockColor (blockRootColor 2)
          (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockVertex 0 (smallPhysicalEmbedding realization left).val)
            (blockVertex 0
              (smallPhysicalEmbedding realization right).val)) := by
    simpa [smallPhysicalEmbedding] using hedge
  have hinternal :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
    realization.branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail
    0 (by rfl) (smallPhysicalEmbedding realization left)
      (smallPhysicalEmbedding realization right) hphysical
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 0 (smallPhysicalEmbedding realization left).val)
      (blockVertex 0 (smallPhysicalEmbedding realization right).val) =
    canonicalPalette 1
      (k15Template false (smallPhysicalEmbedding realization left)
        (smallPhysicalEmbedding realization right)) at hinternal
  rw [hinternal] at hedge'
  have hleftMem : smallPhysicalEmbedding realization left ∈
      twistedRoot4SmallSupport realization := by
    simp [twistedRoot4SmallSupport]
  have hrightMem : smallPhysicalEmbedding realization right ∈
      twistedRoot4SmallSupport realization := by
    simp [twistedRoot4SmallSupport]
  have hnotTwo := support_blockZero_independent realization
    (smallPhysicalEmbedding realization left) hleftMem
    (smallPhysicalEmbedding realization right) hrightMem hphysical
  rw [decode_blockZero_template _ hnotTwo] at hedge'
  simpa [twistedRoot4SmallPhysicalColoring] using hedge'

noncomputable def smallLabelEquiv (realization : TwistedRoot4Realization) :
    Fin 4 ≃ ↑twistedRoot4SmallLabelSet :=
  embeddingEquivRange
    (⟨smallLabel realization, smallLabel_injective realization⟩)
    twistedRoot4SmallLabelSet (by
      simpa [twistedRoot4SmallLabelSet] using realization.smallLabel_image)

noncomputable def smallPhysicalEquiv (realization : TwistedRoot4Realization) :
    Fin 4 ≃ ↑(twistedRoot4SmallSupport realization) :=
  embeddingEquivRange (smallPhysicalEmbedding realization)
    (twistedRoot4SmallSupport realization) realization.smallPhysicalRange

theorem TwistedRoot4Realization.smallSupport_mem_compatibleCandidates
    (realization : TwistedRoot4Realization) :
    twistedRoot4SmallSupport realization ∈
      twistedRoot4CompatibleSmallSupportCandidates := by
  apply Finset.mem_filter.mpr
  constructor
  · exact realization.smallSupport_mem_candidates
  · refine ⟨(smallLabelEquiv realization).symm.trans
        (smallPhysicalEquiv realization), ?_⟩
    intro left right hlr
    let leftIndex := (smallLabelEquiv realization).symm left
    let rightIndex := (smallLabelEquiv realization).symm right
    have hindex : leftIndex ≠ rightIndex :=
      (smallLabelEquiv realization).symm.injective.ne hlr
    have hleft := congrArg Subtype.val
      ((smallLabelEquiv realization).apply_symm_apply left)
    change smallLabel realization leftIndex = left.1 at hleft
    have hright := congrArg Subtype.val
      ((smallLabelEquiv realization).apply_symm_apply right)
    change smallLabel realization rightIndex = right.1 at hright
    rw [← hleft, ← hright]
    simpa [leftIndex, rightIndex, smallPhysicalEquiv,
      embeddingEquivRange] using
        realization.small_small_edge_physical leftIndex rightIndex hindex

/-- Exact `5 x 5` row-to-large-support colours in the strong case. -/
theorem TwistedRoot4Realization.free_large_edge
    (realization : TwistedRoot4Realization) (free large : FiveVertex) :
    k15Template true (freeLabel realization free)
        (largeLabel realization large) =
      decodeNonBlockColor (blockRootColor 2)
        (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
          free
          (blockVertex 1
            (realization.skeleton.largeSupport.embedding large).val)) := by
  rw [show freeLabel realization = fun a =>
      templateLabel realization (.inl (.inl a)) by rfl,
    show largeLabel realization = fun a =>
      templateLabel realization (.inl (.inr a)) by rfl,
    templateEdge_eq_encoded_rest realization
      (.inl (.inl free)) (.inl (.inr large)) (by simp),
    encodedNeighborhoodColoring_rest_rest]
  simp [restColoring, pullbackColoring, restEmbedding,
    retainedJoinedColoring, joinColoring,
    realization.firstLarge_eq_false,
    largeForeignBlock, secondForeignBlock,
    ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
    twistedRoot4Case, caseSlot, uuuRepresentativeIndexBySlot,
    ProfileDUUUFiveSupportPositionSymmetry.k16Index]

/-- Exact `5 x 4` row-to-small-support colours in the strong case. -/
theorem TwistedRoot4Realization.free_small_edge
    (realization : TwistedRoot4Realization) (free : FiveVertex) (small : Fin 4) :
    k15Template true (freeLabel realization free)
        (smallLabel realization small) =
      decodeNonBlockColor (blockRootColor 2)
        (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
          free
          (blockVertex 0
            (realization.skeleton.smallSupport.embedding small).val)) := by
  rw [show freeLabel realization = fun a =>
      templateLabel realization (.inl (.inl a)) by rfl,
    show smallLabel realization = fun a =>
      templateLabel realization (.inr a) by rfl,
    templateEdge_eq_encoded_rest realization
      (.inl (.inl free)) (.inr small) (by simp),
    encodedNeighborhoodColoring_rest_rest]
  simp [restColoring, pullbackColoring, restEmbedding,
    retainedJoinedColoring, joinColoring,
    realization.firstLarge_eq_false,
    smallForeignBlock, firstForeignBlock,
    ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
    twistedRoot4Case, caseSlot, uuuRepresentativeIndexBySlot,
    ProfileDUUUFiveSupportPositionSymmetry.k16Index]

/-- Exact `5 x 4` tail cross-block matrix between the two physical
supports. -/
theorem TwistedRoot4Realization.large_small_edge
    (realization : TwistedRoot4Realization) (large : FiveVertex) (small : Fin 4) :
    k15Template true (largeLabel realization large)
        (smallLabel realization small) =
      decodeNonBlockColor (blockRootColor 2)
        (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 1
            (realization.skeleton.largeSupport.embedding large).val)
          (blockVertex 0
            (realization.skeleton.smallSupport.embedding small).val)) := by
  rw [show largeLabel realization = fun a =>
      templateLabel realization (.inl (.inr a)) by rfl,
    show smallLabel realization = fun a =>
      templateLabel realization (.inr a) by rfl,
    templateEdge_eq_encoded_rest realization
      (.inl (.inr large)) (.inr small) (by simp),
    encodedNeighborhoodColoring_rest_rest]
  simp [restColoring, pullbackColoring, restEmbedding,
    retainedJoinedColoring, joinColoring,
    realization.firstLarge_eq_false,
    largeForeignBlock, smallForeignBlock, firstForeignBlock,
    secondForeignBlock,
    ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
    twistedRoot4Case, caseSlot, uuuRepresentativeIndexBySlot,
    ProfileDUUUFiveSupportPositionSymmetry.k16Index]

/-- A compact package suitable as the semantic entrance to a future finite
completion CNF for this case. -/
structure StrongCaseFiniteBoundary (realization : TwistedRoot4Realization) : Prop where
  largeSupport : twistedRoot4LargeSupport realization ∈
    twistedRoot4LargeSupportCandidates
  smallSupport : twistedRoot4SmallSupport realization ∈
    twistedRoot4CompatibleSmallSupportCandidates
  freeLabels : Finset.univ.image (freeLabel realization) =
    colorNeighborhood (k15Template true) 0 4
  largeLabels : Finset.univ.image (largeLabel realization) =
    colorNeighborhood (k15Template true) 2 4
  smallLabels : Finset.univ.image (smallLabel realization) =
    colorNeighborhood (k15Template true) 1 4
  freeLarge : ∀ free large, k15Template true
      (freeLabel realization free) (largeLabel realization large) =
    decodeNonBlockColor (blockRootColor 2)
      (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
        free (blockVertex 1
          (realization.skeleton.largeSupport.embedding large).val))
  freeSmall : ∀ free small, k15Template true
      (freeLabel realization free) (smallLabel realization small) =
    decodeNonBlockColor (blockRootColor 2)
      (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
        free (blockVertex 0
          (realization.skeleton.smallSupport.embedding small).val))
  largeSmall : ∀ large small, k15Template true
      (largeLabel realization large) (smallLabel realization small) =
    decodeNonBlockColor (blockRootColor 2)
      (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 1
          (realization.skeleton.largeSupport.embedding large).val)
        (blockVertex 0
          (realization.skeleton.smallSupport.embedding small).val))

theorem twistedRoot4CaseFiniteBoundary (realization : TwistedRoot4Realization) :
    StrongCaseFiniteBoundary realization := ⟨
  realization.largeSupport_mem_candidates,
  realization.smallSupport_mem_compatibleCandidates,
  realization.freeLabel_image,
  realization.largeLabel_image,
  realization.smallLabel_image,
  realization.free_large_edge,
  realization.free_small_edge,
  realization.large_small_edge⟩

#print axioms twistedRoot4LargeSupportCandidates_card
#print axioms twistedRoot4SmallSupportCandidates_card
#print axioms twistedRoot4CompatibleSmallSupportCandidates_card
#print axioms twistedRoot4PhysicalSupportPair_card
#print axioms TwistedRoot4Realization.largeSupport_mem_candidates
#print axioms TwistedRoot4Realization.smallSupport_mem_candidates
#print axioms TwistedRoot4Realization.smallSupport_mem_compatibleCandidates
#print axioms TwistedRoot4Realization.small_small_edge_physical
#print axioms TwistedRoot4Realization.free_large_edge
#print axioms TwistedRoot4Realization.free_small_edge
#print axioms TwistedRoot4Realization.large_small_edge
#print axioms twistedRoot4CaseFiniteBoundary

end ContinuationDegreeNineTwistedRoot4Case61
end R4333
