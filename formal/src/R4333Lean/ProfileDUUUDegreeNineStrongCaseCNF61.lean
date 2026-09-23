import R4333Lean.ProfileDUUUDegreeNineStrongCase61
import R4333Lean.ProfileDDegreeTenMatrixCNF

/-!
# A pair-indexed completion CNF for the strongest UUU degree-nine case

The existing five-row formula already contains every row/tail completion
variable, the full four-colour triangle constraints, the three fixed tail
templates, the canonical inside `C5`, all five row-degree intervals, and the
selected-tail degree interval `[9,10]`.

This file adds the finite information certified by
`ProfileDUUUDegreeNineStrongCase61`.  A physical support pair consists of an
independent five-set in block one and a compatible four-set in block zero.
For each pair we enumerate the internally compatible labelings of the three
root-neighbourhood parts (free five, block-one five, block-zero four).  One
fresh selector chooses a labeling, and 65 guarded ordinary-edge clauses fix
all cross-part edges of the resulting rooted `K15` normal form.  Exact
selected-endpoint support units are included separately.

No solver result is asserted here.  The semantic endpoint proved below is
the trusted entrance for a later DIMACS export and checked LRAT replay.
-/

namespace R4333
namespace ProfileDUUUDegreeNineStrongCaseCNF61

open ColoringJoinRows FiniteColorCNF
open SequentialAtMostCNF SequentialAtMostManyCNF
open ThresholdDegreeCapsCNF
open SingleRootStarCNF
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnForeignC5Skeleton61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open ProfileDHighOwnFiveSupportC5CounterNamespace
open ProfileDDegreeNineFullNeighborhoodNormalForm61
open ProfileDUUUDegreeNineFiniteBoundary61
open ProfileDUUUDegreeNineCaseRealization61
open ProfileDUUUDegreeNineStrongCase61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex
abbrev StrongPair := StrongPhysicalSupportPair

/-! ## The three finite parts of the rooted normal form -/

def strongFreeLabelSet : Finset (Fin 15) :=
  colorNeighborhood (k15Template false) 0 2

def strongLargeLabelSet : Finset (Fin 15) :=
  colorNeighborhood (k15Template false) 2 2

theorem strongFreeLabelSet_card : strongFreeLabelSet.card = 5 := by decide

theorem strongLargeLabelSet_card : strongLargeLabelSet.card = 5 := by decide

theorem strongSmallLabelSet_card : strongSmallLabelSet.card = 4 := by decide

def strongPairOfSupports?
    (large small : Finset (Fin 15)) : Option StrongPair :=
  if hlarge : large ∈ strongLargeSupportCandidates then
    if hsmall : small ∈ strongCompatibleSmallSupportCandidates then
      some ⟨⟨large, hlarge⟩, ⟨small, hsmall⟩⟩
    else none
  else none

/-- On a block-one support, local colours zero and one become the same
normal-form colours.  Local colour two is the selected endpoint's colour and
does not occur internally; its displayed value is therefore irrelevant. -/
def strongLargePhysicalColorMap : ThreeColor → ThreeColor := ![0, 1, 0]

def strongLargePhysicalColoring : EdgeColoring (Fin 15) ThreeColor where
  color left right := strongLargePhysicalColorMap
    (k15Template false left right)
  color_symm left right := by
    exact congrArg strongLargePhysicalColorMap
      ((k15Template false).color_symm left right)

/-- The fixed canonical free `C5`, decoded into the selected root's normal
three-colour palette.  Cycle edges have normal colour one and complementary
cycle edges have normal colour two. -/
def strongFreeNormalColor (left right : FiveVertex) : ThreeColor :=
  if canonicalCycleWord.coloring left right then 1 else 2

/-! ## Internally compatible finite labelings -/

theorem pairLarge_card (pair : StrongPair) : pair.1.1.card = 5 := by
  exact (mem_independentSupportCandidates_iff 5 2 pair.1.1).mp pair.1.2 |>.1

theorem pairSmall_card (pair : StrongPair) : pair.2.1.card = 4 := by
  have hsmall := (Finset.mem_filter.mp pair.2.2).1
  exact (mem_independentSupportCandidates_iff 4 2 pair.2.1).mp hsmall |>.1

def freeLabelOrder : Fin 5 ≃ ↑strongFreeLabelSet :=
  (Finset.orderIsoOfFin strongFreeLabelSet strongFreeLabelSet_card).toEquiv

def largeLabelOrder : Fin 5 ≃ ↑strongLargeLabelSet :=
  (Finset.orderIsoOfFin strongLargeLabelSet strongLargeLabelSet_card).toEquiv

def smallLabelOrder : Fin 4 ≃ ↑strongSmallLabelSet :=
  (Finset.orderIsoOfFin strongSmallLabelSet strongSmallLabelSet_card).toEquiv

def pairLargeOrder (pair : StrongPair) : Fin 5 ≃ ↑pair.1.1 :=
  (Finset.orderIsoOfFin pair.1.1 (pairLarge_card pair)).toEquiv

def pairSmallOrder (pair : StrongPair) : Fin 4 ≃ ↑pair.2.1 :=
  (Finset.orderIsoOfFin pair.2.1 (pairSmall_card pair)).toEquiv

/-- Three explicit permutations relative to the increasing orders above.
This representation makes the selector catalogue executable: it is generated
from the concrete `5!`, `5!`, and `4!` permutation lists. -/
structure LocalAssignmentData where
  freePerm : Equiv.Perm (Fin 5)
  largePerm : Equiv.Perm (Fin 5)
  smallPerm : Equiv.Perm (Fin 4)
deriving DecidableEq, Fintype

def LocalAssignmentData.freeLabel
    (assignment : LocalAssignmentData) (free : FiveVertex) : Fin 15 :=
  (freeLabelOrder (assignment.freePerm free)).1

def LocalAssignmentData.largeLabel
    (assignment : LocalAssignmentData) (index : Fin 5) : Fin 15 :=
  (largeLabelOrder index).1

def LocalAssignmentData.largePhysical (pair : StrongPair)
    (assignment : LocalAssignmentData) (index : Fin 5) : Fin 15 :=
  (pairLargeOrder pair (assignment.largePerm index)).1

def LocalAssignmentData.smallLabel
    (assignment : LocalAssignmentData) (index : Fin 4) : Fin 15 :=
  (smallLabelOrder index).1

def LocalAssignmentData.smallPhysical (pair : StrongPair)
    (assignment : LocalAssignmentData) (index : Fin 4) : Fin 15 :=
  (pairSmallOrder pair (assignment.smallPerm index)).1

def FreePermutationCompatible (freePerm : Equiv.Perm (Fin 5)) : Prop :=
  ∀ left right : FiveVertex, left ≠ right →
    k15Template false
        (freeLabelOrder (freePerm left)).1
        (freeLabelOrder (freePerm right)).1 =
      strongFreeNormalColor left right

def LargePermutationCompatible (pair : StrongPair)
    (largePerm : Equiv.Perm (Fin 5)) : Prop :=
  ∀ left right : Fin 5, left ≠ right →
    k15Template false (largeLabelOrder left).1
        (largeLabelOrder right).1 =
      strongLargePhysicalColoring
        (pairLargeOrder pair (largePerm left)).1
        (pairLargeOrder pair (largePerm right)).1

def SmallPermutationCompatible (pair : StrongPair)
    (smallPerm : Equiv.Perm (Fin 4)) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    k15Template false (smallLabelOrder left).1
        (smallLabelOrder right).1 =
      strongSmallPhysicalColoring
        (pairSmallOrder pair (smallPerm left)).1
        (pairSmallOrder pair (smallPerm right)).1

def LocalAssignmentCompatible (pair : StrongPair)
    (assignment : LocalAssignmentData) : Prop :=
  FreePermutationCompatible assignment.freePerm ∧
    LargePermutationCompatible pair assignment.largePerm ∧
      SmallPermutationCompatible pair assignment.smallPerm

instance (freePerm : Equiv.Perm (Fin 5)) :
    Decidable (FreePermutationCompatible freePerm) := by
  unfold FreePermutationCompatible
  infer_instance

instance (pair : StrongPair) (largePerm : Equiv.Perm (Fin 5)) :
    Decidable (LargePermutationCompatible pair largePerm) := by
  unfold LargePermutationCompatible
  infer_instance

instance (pair : StrongPair) (smallPerm : Equiv.Perm (Fin 4)) :
    Decidable (SmallPermutationCompatible pair smallPerm) := by
  unfold SmallPermutationCompatible
  infer_instance

instance (pair : StrongPair) (assignment : LocalAssignmentData) :
    Decidable (LocalAssignmentCompatible pair assignment) := by
  unfold LocalAssignmentCompatible
  infer_instance

abbrev LocalAssignment (pair : StrongPair) :=
  {assignment : LocalAssignmentData //
    LocalAssignmentCompatible pair assignment}

def fourVertexPermutations : List (Equiv.Perm (Fin 4)) :=
  permsOfList ([0, 1, 2, 3] : List (Fin 4))

def rawLocalAssignments : List LocalAssignmentData :=
  fiveVertexPermutations.flatMap fun freePerm =>
    fiveVertexPermutations.flatMap fun largePerm =>
      fourVertexPermutations.map fun smallPerm =>
        ⟨freePerm, largePerm, smallPerm⟩

def compatibleFreePermutations :
    List {freePerm : Equiv.Perm (Fin 5) //
      FreePermutationCompatible freePerm} :=
  fiveVertexPermutations.filterMap fun freePerm =>
    if h : FreePermutationCompatible freePerm then some ⟨freePerm, h⟩
    else none

def compatibleLargePermutations (pair : StrongPair) :
    List {largePerm : Equiv.Perm (Fin 5) //
      LargePermutationCompatible pair largePerm} :=
  fiveVertexPermutations.filterMap fun largePerm =>
    if h : LargePermutationCompatible pair largePerm then some ⟨largePerm, h⟩
    else none

def compatibleSmallPermutations (pair : StrongPair) :
    List {smallPerm : Equiv.Perm (Fin 4) //
      SmallPermutationCompatible pair smallPerm} :=
  fourVertexPermutations.filterMap fun smallPerm =>
    if h : SmallPermutationCompatible pair smallPerm then some ⟨smallPerm, h⟩
    else none

def localAssignments (pair : StrongPair) : List (LocalAssignment pair) :=
  compatibleFreePermutations.flatMap fun freePerm =>
    (compatibleLargePermutations pair).flatMap fun largePerm =>
      (compatibleSmallPermutations pair).map fun smallPerm =>
        ⟨⟨freePerm.1, largePerm.1, smallPerm.1⟩,
          ⟨freePerm.2, largePerm.2, smallPerm.2⟩⟩

private theorem mem_compatibleFreePermutations
    (freePerm : Equiv.Perm (Fin 5))
    (h : FreePermutationCompatible freePerm) :
    (⟨freePerm, h⟩ : {p // FreePermutationCompatible p}) ∈
      compatibleFreePermutations := by
  simp only [compatibleFreePermutations, List.mem_filterMap]
  exact ⟨freePerm, mem_fiveVertexPermutations freePerm, by simp [h]⟩

private theorem mem_compatibleLargePermutations
    (pair : StrongPair) (largePerm : Equiv.Perm (Fin 5))
    (h : LargePermutationCompatible pair largePerm) :
    (⟨largePerm, h⟩ : {p // LargePermutationCompatible pair p}) ∈
      compatibleLargePermutations pair := by
  simp only [compatibleLargePermutations, List.mem_filterMap]
  exact ⟨largePerm, mem_fiveVertexPermutations largePerm, by simp [h]⟩

private theorem mem_fourVertexPermutations
    (smallPerm : Equiv.Perm (Fin 4)) :
    smallPerm ∈ fourVertexPermutations := by
  apply mem_permsOfList_of_mem
  intro x _
  fin_cases x <;> simp

private theorem mem_compatibleSmallPermutations
    (pair : StrongPair) (smallPerm : Equiv.Perm (Fin 4))
    (h : SmallPermutationCompatible pair smallPerm) :
    (⟨smallPerm, h⟩ : {p // SmallPermutationCompatible pair p}) ∈
      compatibleSmallPermutations pair := by
  simp only [compatibleSmallPermutations, List.mem_filterMap]
  exact ⟨smallPerm, mem_fourVertexPermutations smallPerm, by simp [h]⟩

theorem mem_localAssignments (pair : StrongPair)
    (assignment : LocalAssignment pair) :
    assignment ∈ localAssignments pair := by
  rcases assignment with
    ⟨⟨freePerm, largePerm, smallPerm⟩, hfree, hlarge, hsmall⟩
  simp only [localAssignments, List.mem_flatMap, List.mem_map]
  refine ⟨⟨freePerm, hfree⟩,
    mem_compatibleFreePermutations freePerm hfree, ?_⟩
  refine ⟨⟨largePerm, hlarge⟩,
    mem_compatibleLargePermutations pair largePerm hlarge, ?_⟩
  exact ⟨⟨smallPerm, hsmall⟩,
    mem_compatibleSmallPermutations pair smallPerm hsmall, rfl⟩

/-! ## Semantic labelings enter the executable catalogue -/

private theorem restLabel_injective_local : Function.Injective restLabel := by
  intro x y hxy
  apply Option.some.inj
  simpa [restLabel] using congrArg fin15EquivRootedRest hxy

noncomputable def freeLabelEquiv (realization : StrongRealization) :
    FiveVertex ≃ ↑strongFreeLabelSet :=
  embeddingEquivRange
    (⟨freeLabel realization, by
      intro left right h
      apply Sum.inl.inj
      apply Sum.inl.inj
      apply restLabel_injective_local
      exact realization.normal.vertex.symm.injective h⟩)
    strongFreeLabelSet (by
      simpa [strongFreeLabelSet] using realization.freeLabel_image)

noncomputable def largeLabelEquiv (realization : StrongRealization) :
    FiveVertex ≃ ↑strongLargeLabelSet :=
  embeddingEquivRange
    (⟨largeLabel realization, by
      intro left right h
      apply Sum.inr.inj
      apply Sum.inl.inj
      apply restLabel_injective_local
      exact realization.normal.vertex.symm.injective h⟩)
    strongLargeLabelSet (by
      simpa [strongLargeLabelSet] using realization.largeLabel_image)

theorem StrongRealization.largeTarget_eq_one
    (realization : StrongRealization) :
    largeForeignBlock realization.branch.toSemantic.block
      realization.skeleton.firstLarge = 1 := by
  rw [realization.firstLarge_eq_false, realization.branchBlock_eq_two]
  rfl

theorem StrongRealization.largeTargetSize_eq_fifteen
    (realization : StrongRealization) :
    blockSize (largeForeignBlock realization.branch.toSemantic.block
      realization.skeleton.firstLarge) = 15 := by
  rw [StrongRealization.largeTarget_eq_one realization]
  rfl

noncomputable def largePhysicalEmbedding
    (realization : StrongRealization) : Fin 5 ↪ Fin 15 where
  toFun index := Fin.cast
    (StrongRealization.largeTargetSize_eq_fifteen realization)
    (realization.skeleton.largeSupport.embedding index)
  inj' := by
    intro left right h
    apply realization.skeleton.largeSupport.embedding.injective
    apply Fin.ext
    exact congrArg (fun x : Fin 15 => x.val) h

noncomputable def strongLargePhysicalSupport (realization : StrongRealization) :
    Finset (Fin 15) :=
  Finset.univ.image (largePhysicalEmbedding realization)

theorem StrongRealization.largePhysicalEmbedding_mem
    (realization : StrongRealization) (index : Fin 5) :
    largePhysicalEmbedding realization index ∈
      strongLargeSupport realization := by
  have hmem := exactSupport_embedding_mem
    realization.skeleton.largeSupport index
  apply (mem_foreignOwnSupport realization.branch.toSemantic 1
    (largePhysicalEmbedding realization index)).2
  have hcolor :=
    (mem_foreignOwnSupport realization.branch.toSemantic
      (largeForeignBlock realization.branch.toSemantic.block
        realization.skeleton.firstLarge)
      (realization.skeleton.largeSupport.embedding index)).1 hmem
  simpa [largePhysicalEmbedding,
    StrongRealization.largeTarget_eq_one realization] using hcolor

theorem StrongRealization.largePhysicalSupport_eq
    (realization : StrongRealization) :
    strongLargePhysicalSupport realization =
      strongLargeSupport realization := by
  apply Finset.eq_of_subset_of_card_le
  · intro position hposition
    obtain ⟨index, _hindex, rfl⟩ := Finset.mem_image.mp hposition
    exact StrongRealization.largePhysicalEmbedding_mem realization index
  · rw [show (strongLargeSupport realization).card = 5 from
      (mem_independentSupportCandidates_iff 5 2
        (strongLargeSupport realization)).mp
          realization.largeSupport_mem_candidates |>.1]
    simp [strongLargePhysicalSupport,
      Finset.card_image_of_injective _
        (largePhysicalEmbedding realization).injective]

theorem StrongRealization.largePhysicalSupport_mem_candidates
    (realization : StrongRealization) :
    strongLargePhysicalSupport realization ∈
      strongLargeSupportCandidates := by
  rw [StrongRealization.largePhysicalSupport_eq realization]
  exact realization.largeSupport_mem_candidates

noncomputable def strongSupportPair
    (realization : StrongRealization) : StrongPair :=
  ⟨⟨strongLargePhysicalSupport realization,
      StrongRealization.largePhysicalSupport_mem_candidates realization⟩,
    ⟨strongSmallSupport realization,
      realization.smallSupport_mem_compatibleCandidates⟩⟩

noncomputable def largePhysicalEquiv
    (realization : StrongRealization) :
    Fin 5 ≃ ↑(strongLargePhysicalSupport realization) :=
  embeddingEquivRange (largePhysicalEmbedding realization)
    (strongLargePhysicalSupport realization) rfl

theorem StrongRealization.free_free_edge
    (realization : StrongRealization) (left right : FiveVertex)
    (hlr : left ≠ right) :
    k15Template false (freeLabel realization left)
        (freeLabel realization right) =
      decodeNonBlockColor (blockRootColor 2)
        (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
          left right) := by
  rw [show freeLabel realization = fun a =>
      templateLabel realization (.inl (.inl a)) by rfl,
    templateEdge_eq_encoded_rest realization
      (.inl (.inl left)) (.inl (.inl right)) (by
        intro h
        exact hlr (Sum.inl.inj (Sum.inl.inj h))),
    encodedNeighborhoodColoring_rest_rest]
  simp [restColoring, pullbackColoring, restEmbedding,
    retainedJoinedColoring, joinColoring,
    ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic]

private theorem decode_blockOne_template
    (q : ThreeColor) (hq : q ≠ 2) :
    decodeNonBlockColor (blockRootColor 2) (canonicalPalette 2 q) =
      strongLargePhysicalColorMap q := by
  fin_cases q
  · change decodeNonBlockColor 3 0 = 0
    apply SingleRootStarWitness61.canonicalPalette_injective
    rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
    rfl
  · change decodeNonBlockColor 3 1 = 1
    apply SingleRootStarWitness61.canonicalPalette_injective
    rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
    rfl
  · contradiction

theorem StrongRealization.large_large_edge_physical
    (realization : StrongRealization) (left right : Fin 5)
    (hlr : left ≠ right) :
    k15Template false (largeLabel realization left)
        (largeLabel realization right) =
      strongLargePhysicalColoring
        (largePhysicalEmbedding realization left)
        (largePhysicalEmbedding realization right) := by
  have hedge :
      k15Template false (largeLabel realization left)
          (largeLabel realization right) =
        decodeNonBlockColor (blockRootColor 2)
          (realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockVertex 1 (largePhysicalEmbedding realization left).val)
            (blockVertex 1
              (largePhysicalEmbedding realization right).val)) := by
    rw [show largeLabel realization = fun a =>
        templateLabel realization (.inl (.inr a)) by rfl,
      templateEdge_eq_encoded_rest realization
        (.inl (.inr left)) (.inl (.inr right)) (by
          intro h
          exact hlr (Sum.inr.inj (Sum.inl.inj h))),
      encodedNeighborhoodColoring_rest_rest]
    simp [restColoring, pullbackColoring, restEmbedding,
      retainedJoinedColoring, joinColoring, largePhysicalEmbedding,
      realization.firstLarge_eq_false, realization.branchBlock_eq_two,
      largeForeignBlock, secondForeignBlock,
      ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
      strongCase, caseSlot, uuuRepresentativeIndexBySlot,
      ProfileDUUUFiveSupportPositionSymmetry.k16Index]
  have hphysical : largePhysicalEmbedding realization left ≠
      largePhysicalEmbedding realization right :=
    (largePhysicalEmbedding realization).injective.ne hlr
  have hinternal :=
    ProfileDFourRowKindSymmetry.witness_internal_eq_canonicalK15
      realization.branch.toSemantic.toDegreeFlooredFiveExtension.toFiveExtension.tail
      1 (by rfl) (largePhysicalEmbedding realization left)
      (largePhysicalEmbedding realization right) hphysical
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 1 (largePhysicalEmbedding realization left).val)
      (blockVertex 1 (largePhysicalEmbedding realization right).val) =
    canonicalPalette 2
      (k15Template false (largePhysicalEmbedding realization left)
        (largePhysicalEmbedding realization right)) at hinternal
  rw [hinternal] at hedge
  have hleftMem : largePhysicalEmbedding realization left ∈
      strongLargeSupport realization := by
    exact StrongRealization.largePhysicalEmbedding_mem realization left
  have hrightMem : largePhysicalEmbedding realization right ∈
      strongLargeSupport realization := by
    exact StrongRealization.largePhysicalEmbedding_mem realization right
  have hindependent :=
    (mem_independentSupportCandidates_iff 5 2
      (strongLargeSupport realization)).mp
        realization.largeSupport_mem_candidates |>.2
  have hnotTwo := hindependent
    (largePhysicalEmbedding realization left) hleftMem
    (largePhysicalEmbedding realization right) hrightMem hphysical
  rw [decode_blockOne_template _ hnotTwo] at hedge
  simpa [strongLargePhysicalColoring] using hedge

/-! The canonical row transport, retaining its permutation explicitly. -/

structure CanonicalStrongData (realization : StrongRealization) where
  rowPerm : Equiv.Perm FiveVertex
  branch : CanonicalBranch .uuu 2 (Fin.last 15)
  row_eq : ∀ row tail,
    branch.toDegreeFlooredFiveExtension.toFiveExtension.rows row tail =
      realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
        (rowPerm row) tail
  inside_eq : ∀ left right,
    branch.toDegreeFlooredFiveExtension.toFiveExtension.inside left right =
      realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.inside
        (rowPerm left) (rowPerm right)
  tail_eq :
    branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring =
      realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring

theorem exists_canonicalStrongData (realization : StrongRealization) :
    Nonempty (CanonicalStrongData realization) := by
  let ext := realization.branch.toSemantic
  obtain ⟨σ, hσ⟩ := ext.exists_inside_cycle_relabel
  let combined : Equiv.Perm FiveVertex := cycleComplementPerm.trans σ
  let transported := transportDegreeFlooredFiveExtension combined
    ext.toDegreeFlooredFiveExtension
  let branch : CanonicalBranch .uuu 2 (Fin.last 15) := {
    toDegreeFlooredFiveExtension := transported
    allFiveOwn := by
      intro row
      exact ext.allFiveOwn (combined row)
    insideCanonical := by
      intro left right hlr
      change ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
        (combined left) (combined right) = _
      calc
        ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
            (combined left) (combined right) =
          decodeRemainingColor ext.block
            (canonicalCycleWord.coloring (cycleComplementPerm left)
              (cycleComplementPerm right)) := by
                simpa [combined] using hσ
                  (cycleComplementPerm left) (cycleComplementPerm right)
                  (cycleComplementPerm.injective.ne hlr)
        _ = decodeRemainingColor ext.block
            (!canonicalCycleWord.coloring left right) := by
              rw [canonicalCycleWord_cycleComplementPerm left right hlr]
    tailOwnDegreeLower := ext.tailOwnDegreeLower
    tailOwnDegreeUpper := ext.tailOwnDegreeUpper
  }
  refine ⟨{
    rowPerm := combined
    branch := branch
    row_eq := ?_
    inside_eq := ?_
    tail_eq := ?_
  }⟩
  · intro row tail
    rfl
  · intro left right
    rfl
  · rfl

noncomputable def semanticFreeEquiv
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) :
    Fin 5 ≃ ↑strongFreeLabelSet :=
  data.rowPerm.trans (freeLabelEquiv realization)

noncomputable def semanticLargeEquiv
    (realization : StrongRealization) :
    Fin 5 ≃ ↑(strongLargePhysicalSupport realization) :=
  largeLabelOrder |>.trans (largeLabelEquiv realization).symm |>.trans
    (largePhysicalEquiv realization)

noncomputable def semanticSmallEquiv
    (realization : StrongRealization) :
    Fin 4 ≃ ↑(strongSmallSupport realization) :=
  smallLabelOrder |>.trans (smallLabelEquiv realization).symm |>.trans
    (smallPhysicalEquiv realization)

noncomputable def semanticLargePairEquiv
    (realization : StrongRealization) :
    Fin 5 ≃ ↑(strongSupportPair realization).1.1 := by
  change Fin 5 ≃ ↑(strongLargePhysicalSupport realization)
  exact semanticLargeEquiv realization

noncomputable def semanticSmallPairEquiv
    (realization : StrongRealization) :
    Fin 4 ≃ ↑(strongSupportPair realization).2.1 := by
  change Fin 4 ≃ ↑(strongSmallSupport realization)
  exact semanticSmallEquiv realization

noncomputable def semanticAssignmentData
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) : LocalAssignmentData where
  freePerm := (semanticFreeEquiv realization data).trans freeLabelOrder.symm
  largePerm := (semanticLargePairEquiv realization).trans
    (pairLargeOrder (strongSupportPair realization)).symm
  smallPerm := (semanticSmallPairEquiv realization).trans
    (pairSmallOrder (strongSupportPair realization)).symm

theorem semanticAssignmentData_freeLabel
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) (row : Fin 5) :
    (semanticAssignmentData realization data).freeLabel row =
      freeLabel realization (data.rowPerm row) := by
  change (freeLabelOrder
    (((semanticFreeEquiv realization data).trans freeLabelOrder.symm) row)).1 = _
  rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem semanticAssignmentData_largeLabel
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) (index : Fin 5) :
    (semanticAssignmentData realization data).largeLabel index =
      largeLabel realization
        ((largeLabelEquiv realization).symm (largeLabelOrder index)) := by
  change (largeLabelOrder index).1 = _
  symm
  exact congrArg Subtype.val
    ((largeLabelEquiv realization).apply_symm_apply
      (largeLabelOrder index))

theorem semanticAssignmentData_largePhysical
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) (index : Fin 5) :
    (semanticAssignmentData realization data).largePhysical
        (strongSupportPair realization) index =
      largePhysicalEmbedding realization
        ((largeLabelEquiv realization).symm (largeLabelOrder index)) := by
  change (pairLargeOrder (strongSupportPair realization)
    (((semanticLargePairEquiv realization).trans
      (pairLargeOrder (strongSupportPair realization)).symm) index)).1 = _
  rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change (semanticLargePairEquiv realization index).1 = _
  change (largePhysicalEquiv realization
    ((largeLabelEquiv realization).symm (largeLabelOrder index))).1 = _
  rfl

theorem semanticAssignmentData_smallLabel
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) (index : Fin 4) :
    (semanticAssignmentData realization data).smallLabel index =
      smallLabel realization
        ((smallLabelEquiv realization).symm (smallLabelOrder index)) := by
  change (smallLabelOrder index).1 = _
  symm
  exact congrArg Subtype.val
    ((smallLabelEquiv realization).apply_symm_apply
      (smallLabelOrder index))

theorem semanticAssignmentData_smallPhysical
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) (index : Fin 4) :
    (semanticAssignmentData realization data).smallPhysical
        (strongSupportPair realization) index =
      smallPhysicalEmbedding realization
        ((smallLabelEquiv realization).symm (smallLabelOrder index)) := by
  change (pairSmallOrder (strongSupportPair realization)
    (((semanticSmallPairEquiv realization).trans
      (pairSmallOrder (strongSupportPair realization)).symm) index)).1 = _
  rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change (semanticSmallPairEquiv realization index).1 = _
  change (smallPhysicalEquiv realization
    ((smallLabelEquiv realization).symm (smallLabelOrder index))).1 = _
  rfl

private theorem decode_three_one : decodeNonBlockColor 3 1 = 1 := by
  apply SingleRootStarWitness61.canonicalPalette_injective
  rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
  rfl

private theorem decode_three_two : decodeNonBlockColor 3 2 = 2 := by
  apply SingleRootStarWitness61.canonicalPalette_injective
  rw [canonicalPalette_decodeNonBlockColor _ _ (by decide)]
  rfl

theorem decode_canonicalInside_eq_strongFreeNormalColor
    (left right : FiveVertex) :
    decodeNonBlockColor 3
        (decodeRemainingColor 2
          (!canonicalCycleWord.coloring left right)) =
      strongFreeNormalColor left right := by
  by_cases hcycle : canonicalCycleWord.coloring left right
  · simp [strongFreeNormalColor, hcycle, decodeRemainingColor,
      firstRemainingColor, secondRemainingColor, decode_three_one]
  · simp [strongFreeNormalColor, hcycle, decodeRemainingColor,
      firstRemainingColor, secondRemainingColor, decode_three_two]

theorem semanticAssignmentData_compatible
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) :
    LocalAssignmentCompatible (strongSupportPair realization)
      (semanticAssignmentData realization data) := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right hlr
    change k15Template false
        ((semanticAssignmentData realization data).freeLabel left)
        ((semanticAssignmentData realization data).freeLabel right) = _
    rw [semanticAssignmentData_freeLabel,
      semanticAssignmentData_freeLabel,
      StrongRealization.free_free_edge realization (data.rowPerm left)
        (data.rowPerm right) (data.rowPerm.injective.ne hlr),
      ← data.inside_eq]
    rw [data.branch.insideCanonical left right hlr]
    exact decode_canonicalInside_eq_strongFreeNormalColor left right
  · intro left right hlr
    let sourceLeft := (largeLabelEquiv realization).symm
      (largeLabelOrder left)
    let sourceRight := (largeLabelEquiv realization).symm
      (largeLabelOrder right)
    have hsource : sourceLeft ≠ sourceRight := by
      intro h
      apply hlr
      apply largeLabelOrder.injective
      simpa [sourceLeft, sourceRight] using congrArg
        (largeLabelEquiv realization) h
    change k15Template false
        ((semanticAssignmentData realization data).largeLabel left)
        ((semanticAssignmentData realization data).largeLabel right) =
      strongLargePhysicalColoring
        ((semanticAssignmentData realization data).largePhysical
          (strongSupportPair realization) left)
        ((semanticAssignmentData realization data).largePhysical
          (strongSupportPair realization) right)
    rw [semanticAssignmentData_largeLabel realization data left,
      semanticAssignmentData_largeLabel realization data right,
      semanticAssignmentData_largePhysical realization data left,
      semanticAssignmentData_largePhysical realization data right]
    exact StrongRealization.large_large_edge_physical realization
      sourceLeft sourceRight hsource
  · intro left right hlr
    let sourceLeft := (smallLabelEquiv realization).symm
      (smallLabelOrder left)
    let sourceRight := (smallLabelEquiv realization).symm
      (smallLabelOrder right)
    have hsource : sourceLeft ≠ sourceRight := by
      intro h
      apply hlr
      apply smallLabelOrder.injective
      simpa [sourceLeft, sourceRight] using congrArg
        (smallLabelEquiv realization) h
    change k15Template false
        ((semanticAssignmentData realization data).smallLabel left)
        ((semanticAssignmentData realization data).smallLabel right) =
      strongSmallPhysicalColoring
        ((semanticAssignmentData realization data).smallPhysical
          (strongSupportPair realization) left)
        ((semanticAssignmentData realization data).smallPhysical
          (strongSupportPair realization) right)
    rw [semanticAssignmentData_smallLabel realization data left,
      semanticAssignmentData_smallLabel realization data right,
      semanticAssignmentData_smallPhysical realization data left,
      semanticAssignmentData_smallPhysical realization data right]
    exact realization.small_small_edge_physical
      sourceLeft sourceRight hsource

noncomputable def semanticAssignment
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) :
    LocalAssignment (strongSupportPair realization) :=
  ⟨semanticAssignmentData realization data,
    semanticAssignmentData_compatible realization data⟩

theorem StrongRealization.smallSupport_eq_foreignZero
    (realization : StrongRealization) :
    strongSmallSupport realization =
      foreignOwnSupport realization.branch.toSemantic 0 := by
  have htarget :
      smallForeignBlock realization.branch.toSemantic.block
        realization.skeleton.firstLarge = 0 := by
    rw [realization.firstLarge_eq_false, realization.branchBlock_eq_two]
    rfl
  have hsize :
      blockSize (smallForeignBlock realization.branch.toSemantic.block
        realization.skeleton.firstLarge) = 15 := by
    rw [htarget]
    rfl
  apply Finset.Subset.antisymm
  · intro position hposition
    obtain ⟨index, _hindex, rfl⟩ := Finset.mem_image.mp hposition
    have hmem := exactSupport_embedding_mem
      realization.skeleton.smallSupport index
    apply (mem_foreignOwnSupport realization.branch.toSemantic 0
      (smallPhysicalEmbedding realization index)).2
    have hcolor :=
      (mem_foreignOwnSupport realization.branch.toSemantic
        (smallForeignBlock realization.branch.toSemantic.block
          realization.skeleton.firstLarge)
        (realization.skeleton.smallSupport.embedding index)).1 hmem
    simpa [smallPhysicalEmbedding,
      realization.firstLarge_eq_false, realization.branchBlock_eq_two,
      smallForeignBlock, firstForeignBlock,
      ProfileDTripleJoinReduction.blockSize] using hcolor
  · intro position hposition
    let sourcePosition : Fin (blockSize
        (smallForeignBlock realization.branch.toSemantic.block
          realization.skeleton.firstLarge)) :=
      Fin.cast hsize.symm position
    have hcolorZero :=
      (mem_foreignOwnSupport realization.branch.toSemantic 0 position).1
        hposition
    have hvertex :
        blockVertex
            (smallForeignBlock realization.branch.toSemantic.block
              realization.skeleton.firstLarge)
            sourcePosition.val =
          blockVertex 0 position.val := by
      apply Fin.ext
      simp [ProfileDTripleJoinReduction.blockVertex_val,
        sourcePosition, htarget]
    have hcolorTarget :
        realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockVertex realization.branch.toSemantic.block
              realization.branch.toSemantic.position.val)
            (blockVertex
              (smallForeignBlock realization.branch.toSemantic.block
                realization.skeleton.firstLarge)
              sourcePosition.val) =
          blockRootColor realization.branch.toSemantic.block := by
      rw [hvertex]
      simpa [ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic]
        using hcolorZero
    have hmemTarget :=
      (mem_foreignOwnSupport realization.branch.toSemantic
        (smallForeignBlock realization.branch.toSemantic.block
          realization.skeleton.firstLarge) sourcePosition).2 hcolorTarget
    rw [← realization.skeleton.smallSupport.embeddingRange] at hmemTarget
    obtain ⟨index, _hindex, hvalue⟩ := Finset.mem_image.mp hmemTarget
    apply Finset.mem_image.mpr
    refine ⟨index, by simp, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hvalue
    simpa [sourcePosition, smallPhysicalEmbedding] using hval

private theorem hostColor_eq_palette_of_decode
    (actual : Fin 4) (q : ThreeColor) (hne : actual ≠ 3)
    (hdecode : q = decodeNonBlockColor 3 actual) :
    actual = canonicalPalette 3 q := by
  calc
    actual = canonicalPalette 3 (decodeNonBlockColor 3 actual) := by
      symm
      exact canonicalPalette_decodeNonBlockColor 3 actual hne
    _ = canonicalPalette 3 q := congrArg (canonicalPalette 3) hdecode.symm

theorem StrongRealization.free_large_host_edge
    (realization : StrongRealization) (free large : Fin 5) :
    realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
        free (blockVertex 1 (largePhysicalEmbedding realization large).val) =
      canonicalPalette 3
        (k15Template false (freeLabel realization free)
          (largeLabel realization large)) := by
  have hne := restColoring_avoids_selectedOwnColor realization.skeleton
    (.inl (.inl free)) (.inl (.inr large)) (by simp)
  have hne' :
      realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
          free (blockVertex 1
            (largePhysicalEmbedding realization large).val) ≠
        blockRootColor 2 := by
    simpa [restColoring, pullbackColoring, restEmbedding,
      retainedJoinedColoring, joinColoring, largePhysicalEmbedding,
      realization.firstLarge_eq_false, largeForeignBlock,
      secondForeignBlock,
      ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
      strongCase, caseSlot, uuuRepresentativeIndexBySlot,
      ProfileDUUUFiveSupportPositionSymmetry.k16Index] using hne
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      free (blockVertex 1
        (largePhysicalEmbedding realization large).val) ≠ (3 : Fin 4) at hne'
  apply hostColor_eq_palette_of_decode _ _ hne'
  exact realization.free_large_edge free large

theorem StrongRealization.free_small_host_edge
    (realization : StrongRealization) (free : Fin 5) (small : Fin 4) :
    realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
        free (blockVertex 0
          (smallPhysicalEmbedding realization small).val) =
      canonicalPalette 3
        (k15Template false (freeLabel realization free)
          (smallLabel realization small)) := by
  have hne := restColoring_avoids_selectedOwnColor realization.skeleton
    (.inl (.inl free)) (.inr small) (by simp)
  have hne' :
      realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
          free (blockVertex 0
            (smallPhysicalEmbedding realization small).val) ≠
        blockRootColor 2 := by
    simpa [restColoring, pullbackColoring, restEmbedding,
      retainedJoinedColoring, joinColoring, smallPhysicalEmbedding,
      realization.firstLarge_eq_false, smallForeignBlock,
      firstForeignBlock,
      ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
      strongCase, caseSlot, uuuRepresentativeIndexBySlot,
      ProfileDUUUFiveSupportPositionSymmetry.k16Index] using hne
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.rows
      free (blockVertex 0
        (smallPhysicalEmbedding realization small).val) ≠ (3 : Fin 4) at hne'
  apply hostColor_eq_palette_of_decode _ _ hne'
  exact realization.free_small_edge free small

theorem StrongRealization.large_small_host_edge
    (realization : StrongRealization) (large : Fin 5) (small : Fin 4) :
    realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockVertex 1 (largePhysicalEmbedding realization large).val)
        (blockVertex 0 (smallPhysicalEmbedding realization small).val) =
      canonicalPalette 3
        (k15Template false (largeLabel realization large)
          (smallLabel realization small)) := by
  have hne := restColoring_avoids_selectedOwnColor realization.skeleton
    (.inl (.inr large)) (.inr small) (by simp)
  have hne' :
      realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockVertex 1 (largePhysicalEmbedding realization large).val)
          (blockVertex 0 (smallPhysicalEmbedding realization small).val) ≠
        blockRootColor 2 := by
    simpa [restColoring, pullbackColoring, restEmbedding,
      retainedJoinedColoring, joinColoring, largePhysicalEmbedding,
      smallPhysicalEmbedding, realization.firstLarge_eq_false,
      largeForeignBlock, smallForeignBlock, firstForeignBlock,
      secondForeignBlock,
      ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.toSemantic,
      strongCase, caseSlot, uuuRepresentativeIndexBySlot,
      ProfileDUUUFiveSupportPositionSymmetry.k16Index] using hne
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 1 (largePhysicalEmbedding realization large).val)
      (blockVertex 0 (smallPhysicalEmbedding realization small).val) ≠
        (3 : Fin 4) at hne'
  apply hostColor_eq_palette_of_decode _ _ hne'
  exact realization.large_small_edge large small

/-! ## The fresh selector namespace is disjoint from the full base -/

/-- Existing counter namespaces use synthetic vertices zero through eleven.
Synthetic vertex twelve therefore reserves a disjoint leading tag. -/
def selectorNamespaceVertex : Fin 52 := ⟨12, by omega⟩
def selectorNamespaceColor : Fin 4 := 0

def selectorNamespaceTag : Nat :=
  OutsideDegreeCapCNF.outsideDegreeCounterTag
    selectorNamespaceVertex selectorNamespaceColor

private theorem goodColoringFmla51_outside_selectorNamespace :
    FormulaOutsideNamespace selectorNamespaceTag
      (goodColoringFmla 51 4) := by
  intro clause hclause literal hliteral
  change clause ∈
    (atLeastOneClauses 51 4 ++ atMostOneClauses 51 4) ++
      triangleClauses 51 4 at hclause
  rcases List.mem_append.mp hclause with hleft | htriangle
  rcases List.mem_append.mp hleft with hatLeast | hatMost
  · simp only [atLeastOneClauses, List.mem_map] at hatLeast
    obtain ⟨⟨left, right⟩, hedge, rfl⟩ := hatLeast
    have hliteral' : literal ∈
        ((List.range 4).map fun q =>
          Sat.Literal.pos (FiniteColorCNF.edgeAtom left right q)) := hliteral
    simp only [List.mem_map] at hliteral'
    obtain ⟨q, _hq, rfl⟩ := hliteral'
    obtain ⟨hleft, hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hedge
    exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
      selectorNamespaceVertex selectorNamespaceColor (by omega) (by omega)
  · simp only [atMostOneClauses, List.mem_flatMap,
      List.mem_map] at hatMost
    obtain ⟨⟨left, right⟩, hedge,
      ⟨⟨q, r⟩, _hqr, rfl⟩⟩ := hatMost
    obtain ⟨hleft, hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hedge
    have hliteral' : literal ∈
        [Sat.Literal.neg (FiniteColorCNF.edgeAtom left right q),
          Sat.Literal.neg (FiniteColorCNF.edgeAtom left right r)] := hliteral
    simp at hliteral'
    rcases hliteral' with rfl | rfl <;>
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        selectorNamespaceVertex selectorNamespaceColor (by omega) (by omega)
  · simp only [triangleClauses, List.mem_flatMap,
      List.mem_map] at htriangle
    obtain ⟨⟨left, middle, right⟩, htriple,
      ⟨q, _hq, rfl⟩⟩ := htriangle
    obtain ⟨hleft, hmiddle, hright, _hlm, _hmr⟩ :=
      FiniteColorCNF.mem_triples_iff_bounds htriple
    have hliteral' : literal ∈
        [Sat.Literal.neg (FiniteColorCNF.edgeAtom left middle q),
          Sat.Literal.neg (FiniteColorCNF.edgeAtom left right q),
          Sat.Literal.neg (FiniteColorCNF.edgeAtom middle right q)] := hliteral
    simp at hliteral'
    rcases hliteral' with rfl | rfl | rfl <;>
      exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
        selectorNamespaceVertex selectorNamespaceColor (by omega) (by omega)

private theorem blockTemplateUnitClauses_outside_selectorNamespace
    (kind : ProfileDTripleJoinReduction.Kind) (block : Fin 3) :
    FormulaOutsideNamespace selectorNamespaceTag
      (blockTemplateUnitClauses kind block) := by
  unfold selectorNamespaceTag blockTemplateUnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    obtain ⟨hleft, _hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega
  · intro pair hpair
    obtain ⟨_hleft, hright, _hlr⟩ :=
      SingleRootStarCNF.mem_edges_bounds hpair
    have hspan : blockStart block + blockSize block ≤ 46 := by
      fin_cases block <;> decide
    omega

private theorem templateUnitClauses_outside_selectorNamespace
    (kind : ProfileDTripleJoinReduction.Kind) :
    FormulaOutsideNamespace selectorNamespaceTag
      (templateUnitClauses kind) := by
  unfold templateUnitClauses
  exact formulaOutsideNamespace_append
    (formulaOutsideNamespace_append
      (blockTemplateUnitClauses_outside_selectorNamespace kind 0)
      (blockTemplateUnitClauses_outside_selectorNamespace kind 1))
    (blockTemplateUnitClauses_outside_selectorNamespace kind 2)

private theorem insideRootForbidden_outside_selectorNamespace :
    FormulaOutsideNamespace selectorNamespaceTag
      insideRootForbiddenUnitClauses := by
  unfold selectorNamespaceTag insideRootForbiddenUnitClauses
  apply negativeEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).1.trans (by omega)
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).2.1.trans (by omega)

private theorem allFiveOwn_outside_selectorNamespace :
    FormulaOutsideNamespace selectorNamespaceTag
      (allFiveOwnUnitClauses 2 (Fin.last 15)) := by
  unfold selectorNamespaceTag allFiveOwnUnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro row _hrow
    omega
  · intro row _hrow
    have hselected : (blockVertex 2 (Fin.last 15).val).val < 46 :=
      (blockVertex 2 (Fin.last 15).val).isLt
    omega

private theorem insideC5_outside_selectorNamespace :
    FormulaOutsideNamespace selectorNamespaceTag
      (insideC5UnitClauses 2) := by
  unfold selectorNamespaceTag insideC5UnitClauses
  apply positiveEdgeUnitClauses_outside_counterNamespace
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).1.trans (by omega)
  · intro pair hpair
    exact (SingleRootStarCNF.mem_edges_bounds hpair).2.1.trans (by omega)

theorem strongBaseFmla_outside_selectorNamespace :
    FormulaOutsideNamespace selectorNamespaceTag
      (baseFmla .uuu 2 (Fin.last 15)) := by
  change FormulaOutsideNamespace selectorNamespaceTag
    ((((goodColoringFmla 51 4 ++ templateUnitClauses .uuu) ++
      insideRootForbiddenUnitClauses) ++
        allFiveOwnUnitClauses 2 (Fin.last 15)) ++
          insideC5UnitClauses 2)
  exact formulaOutsideNamespace_append
    (formulaOutsideNamespace_append
      (formulaOutsideNamespace_append
        (formulaOutsideNamespace_append
          goodColoringFmla51_outside_selectorNamespace
          (templateUnitClauses_outside_selectorNamespace .uuu))
        insideRootForbidden_outside_selectorNamespace)
      allFiveOwn_outside_selectorNamespace)
    insideC5_outside_selectorNamespace

private theorem rowColorAtoms_outside_selectorNamespace
    (row : FiveVertex) (q : Fin 4) :
    InputsOutsideNamespace selectorNamespaceTag (rowColorAtoms row q) := by
  intro atom hatom
  simp only [rowColorAtoms, List.mem_map] at hatom
  obtain ⟨tail, _htail, rfl⟩ := hatom
  exact OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    selectorNamespaceVertex selectorNamespaceColor (by omega) (by omega)

private theorem rowOtherColorAtoms_outside_selectorNamespace
    (row : FiveVertex) (q : Fin 4) :
    InputsOutsideNamespace selectorNamespaceTag
      (rowOtherColorAtoms row q) := by
  intro atom hatom
  simp only [rowOtherColorAtoms, List.mem_flatMap] at hatom
  obtain ⟨r, _hr, hatom⟩ := hatom
  exact rowColorAtoms_outside_selectorNamespace row r atom hatom

private theorem selectedTailColorAtoms_outside_selectorNamespace
    (q : Fin 4) :
    InputsOutsideNamespace selectorNamespaceTag
      (selectedTailColorAtoms 2 (Fin.last 15) q) := by
  intro atom hatom
  simp only [selectedTailColorAtoms, List.mem_map] at hatom
  obtain ⟨tail, _htail, rfl⟩ := hatom
  unfold selectorNamespaceTag
    OutsideDegreeCapCNF.outsideIncidentEdgeAtom
  apply OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
  · exact lt_of_le_of_lt
      (Nat.min_le_left
        (tailVertex (selectedTailVertex 2 (Fin.last 15))).val
        (tailVertex tail).val)
      ((tailVertex (selectedTailVertex 2 (Fin.last 15))).isLt.trans
        (by omega))
  · exact max_lt
      ((tailVertex (selectedTailVertex 2 (Fin.last 15))).isLt.trans
        (by omega))
      ((tailVertex tail).isLt.trans (by omega))

private theorem selectedTailOtherColorAtoms_outside_selectorNamespace :
    InputsOutsideNamespace selectorNamespaceTag
      (selectedTailOtherColorAtoms 2 (Fin.last 15)) := by
  intro atom hatom
  simp only [selectedTailOtherColorAtoms, List.mem_flatMap] at hatom
  obtain ⟨q, _hq, hatom⟩ := hatom
  exact selectedTailColorAtoms_outside_selectorNamespace q atom hatom

private theorem contextInputs_outside_selectorNamespace
    (context : CounterContext) :
    InputsOutsideNamespace selectorNamespaceTag
      (contextInputs 2 (Fin.last 15) context) := by
  cases context with
  | row row q phase =>
      by_cases hphase : phase = upperPhase
      · simp only [contextInputs, hphase, if_pos]
        exact rowColorAtoms_outside_selectorNamespace row q
      · simp only [contextInputs, hphase]
        exact rowOtherColorAtoms_outside_selectorNamespace row q
  | selectedTail phase =>
      by_cases hphase : phase = upperPhase
      · simp only [contextInputs, hphase, if_pos]
        exact selectedTailColorAtoms_outside_selectorNamespace 3
      · simp only [contextInputs, hphase]
        exact selectedTailOtherColorAtoms_outside_selectorNamespace

private theorem counterTag_ne_selectorNamespaceTag
    (context : CounterContext) :
    counterTag context ≠ selectorNamespaceTag := by
  intro htag
  unfold counterTag selectorNamespaceTag at htag
  obtain ⟨hvertex, _hcolor⟩ :=
    OutsideDegreeCapCNF.outsideDegreeCounterTag_injective htag
  have hval := congrArg Fin.val hvertex
  cases context <;>
    simp [counterTag, namespaceVertex, selectorNamespaceTag,
      selectorNamespaceVertex] at hval <;> omega

theorem strongFmla_outside_selectorNamespace :
    FormulaOutsideNamespace selectorNamespaceTag
      (ProfileDHighOwnFiveSupportC5Formula.fmla
        .uuu 2 (Fin.last 15)) := by
  rw [ProfileDHighOwnFiveSupportC5Formula.fmla,
    manySequentialAtMostFmla_eq_append_flatMap]
  apply formulaOutsideNamespace_append
  · exact strongBaseFmla_outside_selectorNamespace
  · intro clause hclause literal hliteral
    obtain ⟨spec, hspec, hcounter⟩ := List.mem_flatMap.mp hclause
    have hspec' : spec ∈ counterSpecs 2 (Fin.last 15) := hspec
    simp only [counterSpecs, List.mem_map] at hspec'
    obtain ⟨context, _hcontext, rfl⟩ := hspec'
    exact counterBlock_outside_other_namespace
      (counterSpec 2 (Fin.last 15) context) selectorNamespaceTag
      (counterTag_ne_selectorNamespaceTag context)
      (contextInputs_outside_selectorNamespace context)
      clause hcounter literal hliteral

/-! ## Exact pair support units -/

def selectedVertex : TotalVertex :=
  tailVertex (blockVertex 2 (Fin.last 15).val)

def physicalBlockZeroVertex (position : Fin 15) : TotalVertex :=
  tailVertex (blockVertex 0 position.val)

def physicalBlockOneVertex (position : Fin 15) : TotalVertex :=
  tailVertex (blockVertex 1 position.val)

def supportLiteral (atom : Nat) (member : Bool) : Sat.Literal :=
  if member then .pos atom else .neg atom

def blockZeroSupportUnitClauses (pair : StrongPair) : Sat.Fmla :=
  (List.finRange 15).map fun position : Fin 15 =>
    [supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        selectedVertex (physicalBlockZeroVertex position) (3 : Fin 4))
      (decide (position ∈ pair.2.1))]

def blockOneSupportUnitClauses (pair : StrongPair) : Sat.Fmla :=
  (List.finRange 15).map fun position : Fin 15 =>
    [supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        selectedVertex (physicalBlockOneVertex position) (3 : Fin 4))
      (decide (position ∈ pair.1.1))]

def supportUnitClauses (pair : StrongPair) : Sat.Fmla :=
  blockZeroSupportUnitClauses pair ++ blockOneSupportUnitClauses pair

theorem supportUnitClauses_length (pair : StrongPair) :
    (supportUnitClauses pair).length = 30 := by
  simp [supportUnitClauses, blockZeroSupportUnitClauses,
    blockOneSupportUnitClauses]

/-! ## Pair-local selector formula -/

def selectorAtom {pair : StrongPair}
    (assignment : LocalAssignment pair) : Nat :=
  Nat.pair selectorNamespaceTag
    (List.idxOf assignment (localAssignments pair))

def selectorAtLeastOneClause (pair : StrongPair) : Sat.Clause :=
  (localAssignments pair).map fun assignment =>
    Sat.Literal.pos (selectorAtom assignment)

def decodedNormalHostColor (q : ThreeColor) : Fin 4 :=
  canonicalPalette 3 q

def guardedEdgeClause {pair : StrongPair}
    (assignment : LocalAssignment pair)
    (left right : TotalVertex) (q : ThreeColor) : Sat.Clause :=
  [Sat.Literal.neg (selectorAtom assignment),
   Sat.Literal.pos
    (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
      left right (decodedNormalHostColor q))]

def guardedFreeLargeClauses {pair : StrongPair}
    (assignment : LocalAssignment pair) : Sat.Fmla :=
  (List.finRange 5).flatMap fun free : FiveVertex =>
    (List.finRange 5).map fun large : Fin 5 =>
      guardedEdgeClause assignment
        (freeVertex free)
        (physicalBlockOneVertex
          (assignment.1.largePhysical pair large))
        (k15Template false (assignment.1.freeLabel free)
          (assignment.1.largeLabel large))

def guardedFreeSmallClauses {pair : StrongPair}
    (assignment : LocalAssignment pair) : Sat.Fmla :=
  (List.finRange 5).flatMap fun free : FiveVertex =>
    (List.finRange 4).map fun small : Fin 4 =>
      guardedEdgeClause assignment
        (freeVertex free)
        (physicalBlockZeroVertex
          (assignment.1.smallPhysical pair small))
        (k15Template false (assignment.1.freeLabel free)
          (assignment.1.smallLabel small))

def guardedLargeSmallClauses {pair : StrongPair}
    (assignment : LocalAssignment pair) : Sat.Fmla :=
  (List.finRange 5).flatMap fun large : Fin 5 =>
    (List.finRange 4).map fun small : Fin 4 =>
      guardedEdgeClause assignment
        (physicalBlockOneVertex
          (assignment.1.largePhysical pair large))
        (physicalBlockZeroVertex
          (assignment.1.smallPhysical pair small))
        (k15Template false (assignment.1.largeLabel large)
          (assignment.1.smallLabel small))

def guardedAssignmentClauses {pair : StrongPair}
    (assignment : LocalAssignment pair) : Sat.Fmla :=
  guardedFreeLargeClauses assignment ++
    guardedFreeSmallClauses assignment ++
      guardedLargeSmallClauses assignment

theorem guardedAssignmentClauses_length {pair : StrongPair}
    (assignment : LocalAssignment pair) :
    (guardedAssignmentClauses assignment).length = 65 := by
  simp [guardedAssignmentClauses, guardedFreeLargeClauses,
    guardedFreeSmallClauses, guardedLargeSmallClauses]

def selectorFmla (pair : StrongPair) : Sat.Fmla :=
  [selectorAtLeastOneClause pair] ++
    (localAssignments pair).flatMap guardedAssignmentClauses

theorem selectorFmla_length (pair : StrongPair) :
    (selectorFmla pair).length =
      1 + 65 * (localAssignments pair).length := by
  simp [selectorFmla, List.length_flatMap,
    guardedAssignmentClauses_length]
  omega

def pairFmla (pair : StrongPair) : Sat.Fmla :=
  (fmla .uuu 2 (Fin.last 15) ++ supportUnitClauses pair) ++
    selectorFmla pair

/-! ## Selector extension and exact semantic satisfaction -/

noncomputable def selectorExtendedValuation {pair : StrongPair}
    (selected : LocalAssignment pair) (base : Sat.Valuation) :
    Sat.Valuation :=
  fun atom =>
    @ite Prop (InSequentialNamespace selectorNamespaceTag atom)
      (Classical.propDecidable _)
      ((Nat.unpair atom).2 =
        List.idxOf selected (localAssignments pair))
      (base atom)

theorem selectorExtendedValuation_eq_of_outside {pair : StrongPair}
    (selected : LocalAssignment pair) (base : Sat.Valuation) (atom : Nat)
    (houtside : ¬InSequentialNamespace selectorNamespaceTag atom) :
    selectorExtendedValuation selected base atom ↔ base atom := by
  simp [selectorExtendedValuation, houtside]

@[simp] theorem selectorExtendedValuation_selectorAtom
    {pair : StrongPair} (selected assignment : LocalAssignment pair)
    (base : Sat.Valuation) :
    selectorExtendedValuation selected base (selectorAtom assignment) ↔
      assignment = selected := by
  simp only [selectorExtendedValuation, selectorAtom,
    InSequentialNamespace, Nat.unpair_pair, ↓reduceIte]
  exact List.idxOf_inj (mem_localAssignments pair assignment)

private theorem neg_iff_of_atom_iff
    (literal : Sat.Literal) (left right : Sat.Valuation)
    (h : left (literalAtom literal) ↔ right (literalAtom literal)) :
    left.neg literal ↔ right.neg literal := by
  cases literal <;> simp only [literalAtom, Sat.Valuation.neg] at h ⊢
  · exact not_congr h
  · exact h

private theorem satisfies_of_agrees_on_clause
    {left right : Sat.Valuation} (clause : Sat.Clause)
    (hagrees : ∀ literal : Sat.Literal, List.Mem literal clause →
      (left (literalAtom literal) ↔ right (literalAtom literal)))
    (hright : right.satisfies clause) : left.satisfies clause := by
  revert hagrees hright
  induction clause with
  | nil => intro _ hright; exact hright
  | cons literal tail ih =>
      intro hagrees hright hneg
      apply ih
      · intro other hother
        exact hagrees other (List.Mem.tail literal hother)
      · apply hright
        exact (neg_iff_of_atom_iff literal left right
          (hagrees literal (List.Mem.head tail))).mp hneg

theorem selectorExtendedValuation_satisfies_strongFmla
    {pair : StrongPair} (selected : LocalAssignment pair)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15)) :
    (selectorExtendedValuation selected (finalValuation branch)).satisfies_fmla
      (fmla .uuu 2 (Fin.last 15)) := by
  have hbase := canonicalBranch_satisfies_fmla branch
  constructor
  intro clause hclause
  apply satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact selectorExtendedValuation_eq_of_outside selected _ _
      (strongFmla_outside_selectorNamespace
        clause hclause literal hliteral)
  · exact hbase.prop clause hclause

noncomputable def strongFinalValuation
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) : Sat.Valuation :=
  selectorExtendedValuation (semanticAssignment realization data)
    (finalValuation data.branch)

theorem strongFinalValuation_ordinaryEdgeAtom
    (realization : StrongRealization)
    (data : CanonicalStrongData realization)
    (left right : TotalVertex) (hne : left ≠ right) (q : Fin 4) :
    strongFinalValuation realization data
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right q) ↔
      totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        left right = q := by
  unfold strongFinalValuation
  rw [selectorExtendedValuation_eq_of_outside]
  · exact ProfileDDegreeTenMatrixCNF.finalValuation_ordinaryEdgeAtom
      data.branch left right hne q
  · unfold selectorNamespaceTag
      OutsideDegreeCapCNF.outsideIncidentEdgeAtom
    apply OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    · exact lt_of_le_of_lt (Nat.min_le_left left.val right.val)
        (left.isLt.trans (by omega))
    · exact max_lt (left.isLt.trans (by omega))
        (right.isLt.trans (by omega))

private theorem selected_ne_blockZero (position : Fin 15) :
    selectedVertex ≠ physicalBlockZeroVertex position := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 2 0 (by decide)
      (Fin.last 15).isLt position.isLt)

private theorem selected_ne_blockOne (position : Fin 15) :
    selectedVertex ≠ physicalBlockOneVertex position := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 2 1 (by decide)
      (Fin.last 15).isLt position.isLt)

private theorem strongRealization_selectedBlockVertex
    (realization : StrongRealization) :
    blockVertex realization.branch.toSemantic.block
        realization.branch.toSemantic.position.val =
      blockVertex 2 (Fin.last 15).val := by
  change blockVertex
      (uuuRepresentativeIndexBySlot (caseSlot strongCase)).1
      (uuuRepresentativeIndexBySlot (caseSlot strongCase)).2.val =
    blockVertex 2 (Fin.last 15).val
  simp [strongCase, caseSlot, uuuRepresentativeIndexBySlot,
    ProfileDUUUFiveSupportPositionSymmetry.k16Index]

private theorem strongRealization_selectedRootColor
    (realization : StrongRealization) :
    blockRootColor realization.branch.toSemantic.block = (3 : Fin 4) := by
  rw [realization.branchBlock_eq_two]
  rfl

theorem CanonicalStrongData.blockZero_support_iff
    {realization : StrongRealization}
    (data : CanonicalStrongData realization) (position : Fin 15) :
    totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex (physicalBlockZeroVertex position) = 3 ↔
      position ∈ (strongSupportPair realization).2.1 := by
  unfold selectedVertex physicalBlockZeroVertex
  rw [totalColoring_tail_tail, data.tail_eq]
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 (Fin.last 15).val) (blockVertex 0 position.val) = 3 ↔
    position ∈ strongSmallSupport realization
  rw [StrongRealization.smallSupport_eq_foreignZero realization]
  have hmem :=
    (mem_foreignOwnSupport realization.branch.toSemantic 0 position).symm
  rw [strongRealization_selectedBlockVertex realization,
    strongRealization_selectedRootColor realization] at hmem
  exact hmem

theorem CanonicalStrongData.blockOne_support_iff
    {realization : StrongRealization}
    (data : CanonicalStrongData realization) (position : Fin 15) :
    totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex (physicalBlockOneVertex position) = 3 ↔
      position ∈ (strongSupportPair realization).1.1 := by
  unfold selectedVertex physicalBlockOneVertex
  rw [totalColoring_tail_tail, data.tail_eq]
  change realization.branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockVertex 2 (Fin.last 15).val) (blockVertex 1 position.val) = 3 ↔
    position ∈ strongLargePhysicalSupport realization
  rw [StrongRealization.largePhysicalSupport_eq realization]
  change _ ↔ position ∈ foreignOwnSupport realization.branch.toSemantic 1
  have hmem :=
    (mem_foreignOwnSupport realization.branch.toSemantic 1 position).symm
  rw [strongRealization_selectedBlockVertex realization,
    strongRealization_selectedRootColor realization] at hmem
  exact hmem

private theorem satisfies_support_clause
    (realization : StrongRealization)
    (data : CanonicalStrongData realization)
    (target : TotalVertex) (hne : selectedVertex ≠ target)
    (member : Bool)
    (htruth :
      (totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex target = (3 : Fin 4)) ↔ member = true) :
    (strongFinalValuation realization data).satisfies
      [supportLiteral
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)) member] := by
  cases hmember : member
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)))
    · simpa [supportLiteral, hmember] using
        (List.Mem.head ([] : List Sat.Literal))
    · change ¬strongFinalValuation realization data
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4))
      rw [strongFinalValuation_ordinaryEdgeAtom realization data
        selectedVertex target hne (3 : Fin 4)]
      intro hcolor
      have := htruth.mp hcolor
      simp [hmember] at this
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.pos
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)))
    · simpa [supportLiteral, hmember] using
        (List.Mem.head ([] : List Sat.Literal))
    · change strongFinalValuation realization data
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4))
      rw [strongFinalValuation_ordinaryEdgeAtom realization data
        selectedVertex target hne (3 : Fin 4)]
      exact htruth.mpr (by simp [hmember])

theorem strongFinalValuation_satisfies_supportUnits
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) :
    (strongFinalValuation realization data).satisfies_fmla
      (supportUnitClauses (strongSupportPair realization)) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hzero | hone
  · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hzero
    apply satisfies_support_clause realization data
      (physicalBlockZeroVertex position) (selected_ne_blockZero position)
    simpa only [decide_eq_true_eq] using data.blockZero_support_iff position
  · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hone
    apply satisfies_support_clause realization data
      (physicalBlockOneVertex position) (selected_ne_blockOne position)
    simpa only [decide_eq_true_eq] using data.blockOne_support_iff position

private theorem free_ne_blockOne
    (free : Fin 5) (position : Fin 15) :
    freeVertex free ≠ physicalBlockOneVertex position := by
  intro h
  have hval := congrArg Fin.val h
  simp [freeVertex, physicalBlockOneVertex, tailVertex] at hval
  omega

private theorem free_ne_blockZero
    (free : Fin 5) (position : Fin 15) :
    freeVertex free ≠ physicalBlockZeroVertex position := by
  intro h
  have hval := congrArg Fin.val h
  simp [freeVertex, physicalBlockZeroVertex, tailVertex] at hval
  omega

private theorem blockOne_ne_blockZero
    (large small : Fin 15) :
    physicalBlockOneVertex large ≠ physicalBlockZeroVertex small := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 1 0 (by decide) large.isLt small.isLt)

theorem semanticAssignment_freeLarge_edge
    (realization : StrongRealization)
    (data : CanonicalStrongData realization)
    (free large : Fin 5) :
    totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex free)
        (physicalBlockOneVertex
          ((semanticAssignment realization data).1.largePhysical
            (strongSupportPair realization) large)) =
      decodedNormalHostColor
        (k15Template false
          ((semanticAssignment realization data).1.freeLabel free)
          ((semanticAssignment realization data).1.largeLabel large)) := by
  unfold physicalBlockOneVertex
  rw [totalColoring_free_tail, data.row_eq]
  unfold semanticAssignment
  rw [
    semanticAssignmentData_freeLabel realization data free,
    semanticAssignmentData_largeLabel realization data large,
    semanticAssignmentData_largePhysical realization data large]
  exact StrongRealization.free_large_host_edge realization
    (data.rowPerm free)
    ((largeLabelEquiv realization).symm (largeLabelOrder large))

theorem semanticAssignment_freeSmall_edge
    (realization : StrongRealization)
    (data : CanonicalStrongData realization)
    (free : Fin 5) (small : Fin 4) :
    totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        (freeVertex free)
        (physicalBlockZeroVertex
          ((semanticAssignment realization data).1.smallPhysical
            (strongSupportPair realization) small)) =
      decodedNormalHostColor
        (k15Template false
          ((semanticAssignment realization data).1.freeLabel free)
          ((semanticAssignment realization data).1.smallLabel small)) := by
  unfold physicalBlockZeroVertex
  rw [totalColoring_free_tail, data.row_eq]
  unfold semanticAssignment
  rw [
    semanticAssignmentData_freeLabel realization data free,
    semanticAssignmentData_smallLabel realization data small,
    semanticAssignmentData_smallPhysical realization data small]
  exact StrongRealization.free_small_host_edge realization
    (data.rowPerm free)
    ((smallLabelEquiv realization).symm (smallLabelOrder small))

theorem semanticAssignment_largeSmall_edge
    (realization : StrongRealization)
    (data : CanonicalStrongData realization)
    (large : Fin 5) (small : Fin 4) :
    totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        (physicalBlockOneVertex
          ((semanticAssignment realization data).1.largePhysical
            (strongSupportPair realization) large))
        (physicalBlockZeroVertex
          ((semanticAssignment realization data).1.smallPhysical
            (strongSupportPair realization) small)) =
      decodedNormalHostColor
        (k15Template false
          ((semanticAssignment realization data).1.largeLabel large)
          ((semanticAssignment realization data).1.smallLabel small)) := by
  unfold physicalBlockOneVertex physicalBlockZeroVertex
  rw [totalColoring_tail_tail, data.tail_eq]
  unfold semanticAssignment
  rw [
    semanticAssignmentData_largeLabel realization data large,
    semanticAssignmentData_largePhysical realization data large,
    semanticAssignmentData_smallLabel realization data small,
    semanticAssignmentData_smallPhysical realization data small]
  exact StrongRealization.large_small_host_edge realization
    ((largeLabelEquiv realization).symm (largeLabelOrder large))
    ((smallLabelEquiv realization).symm (smallLabelOrder small))

theorem strongFinalValuation_satisfies_selectorFmla
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) :
    (strongFinalValuation realization data).satisfies_fmla
      (selectorFmla (strongSupportPair realization)) := by
  let selected := semanticAssignment realization data
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hatLeast | hguarded
  · have hsingle : clause = selectorAtLeastOneClause
        (strongSupportPair realization) := List.mem_singleton.mp hatLeast
    subst clause
    apply satisfies_of_mem_holds
      (l := Sat.Literal.pos (selectorAtom selected))
    · change Sat.Literal.pos (selectorAtom selected) ∈
        (localAssignments (strongSupportPair realization)).map
          (fun assignment => Sat.Literal.pos (selectorAtom assignment))
      exact List.mem_map.mpr ⟨selected,
        mem_localAssignments _ selected, rfl⟩
    · exact (selectorExtendedValuation_selectorAtom selected selected _).2 rfl
  · obtain ⟨assignment, hassignment, hclause⟩ :=
      List.mem_flatMap.mp hguarded
    by_cases hselected : assignment = selected
    · subst assignment
      rcases List.mem_append.mp hclause with hfirstTwo | hlargeSmall
      · rcases List.mem_append.mp hfirstTwo with hfreeLarge | hfreeSmall
        · obtain ⟨free, _hfree, hlargeClause⟩ :=
          List.mem_flatMap.mp hfreeLarge
          obtain ⟨large, _hlarge, rfl⟩ := List.mem_map.mp hlargeClause
          apply satisfies_of_mem_holds
            (l := Sat.Literal.pos
              (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
                (freeVertex free)
                (physicalBlockOneVertex
                  (selected.1.largePhysical
                    (strongSupportPair realization) large))
                (decodedNormalHostColor
                  (k15Template false (selected.1.freeLabel free)
                    (selected.1.largeLabel large)))))
          · exact List.Mem.tail _ (List.Mem.head _)
          · change strongFinalValuation realization data
              (OutsideDegreeCapCNF.outsideIncidentEdgeAtom _ _ _)
            rw [strongFinalValuation_ordinaryEdgeAtom realization data _ _
              (free_ne_blockOne free _) _]
            exact semanticAssignment_freeLarge_edge realization data free large
        · obtain ⟨free, _hfree, hsmallClause⟩ :=
            List.mem_flatMap.mp hfreeSmall
          obtain ⟨small, _hsmall, rfl⟩ := List.mem_map.mp hsmallClause
          apply satisfies_of_mem_holds
            (l := Sat.Literal.pos
              (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
                (freeVertex free)
                (physicalBlockZeroVertex
                  (selected.1.smallPhysical
                    (strongSupportPair realization) small))
                (decodedNormalHostColor
                  (k15Template false (selected.1.freeLabel free)
                    (selected.1.smallLabel small)))))
          · exact List.Mem.tail _ (List.Mem.head _)
          · change strongFinalValuation realization data
              (OutsideDegreeCapCNF.outsideIncidentEdgeAtom _ _ _)
            rw [strongFinalValuation_ordinaryEdgeAtom realization data _ _
              (free_ne_blockZero free _) _]
            exact semanticAssignment_freeSmall_edge realization data free small
      · obtain ⟨large, _hlarge, hsmallClause⟩ :=
          List.mem_flatMap.mp hlargeSmall
        obtain ⟨small, _hsmall, rfl⟩ := List.mem_map.mp hsmallClause
        apply satisfies_of_mem_holds
          (l := Sat.Literal.pos
            (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
              (physicalBlockOneVertex
                (selected.1.largePhysical
                  (strongSupportPair realization) large))
              (physicalBlockZeroVertex
                (selected.1.smallPhysical
                  (strongSupportPair realization) small))
              (decodedNormalHostColor
                (k15Template false (selected.1.largeLabel large)
                  (selected.1.smallLabel small)))))
        · exact List.Mem.tail _ (List.Mem.head _)
        · change strongFinalValuation realization data
            (OutsideDegreeCapCNF.outsideIncidentEdgeAtom _ _ _)
          rw [strongFinalValuation_ordinaryEdgeAtom realization data _ _
            (blockOne_ne_blockZero _ _) _]
          exact semanticAssignment_largeSmall_edge realization data large small
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg (selectorAtom assignment))
      · rcases List.mem_append.mp hclause with hfirstTwo | hlargeSmall
        · rcases List.mem_append.mp hfirstTwo with hfreeLarge | hfreeSmall
          · obtain ⟨free, _hfree, hmap⟩ := List.mem_flatMap.mp hfreeLarge
            obtain ⟨large, _hlarge, rfl⟩ := List.mem_map.mp hmap
            exact List.Mem.head _
          · obtain ⟨free, _hfree, hmap⟩ := List.mem_flatMap.mp hfreeSmall
            obtain ⟨small, _hsmall, rfl⟩ := List.mem_map.mp hmap
            exact List.Mem.head _
        · obtain ⟨large, _hlarge, hmap⟩ := List.mem_flatMap.mp hlargeSmall
          obtain ⟨small, _hsmall, rfl⟩ := List.mem_map.mp hmap
          exact List.Mem.head _
      · change ¬selectorExtendedValuation selected
          (finalValuation data.branch) (selectorAtom assignment)
        intro htrue
        exact hselected
          ((selectorExtendedValuation_selectorAtom selected assignment _).1 htrue)

theorem strongRealization_satisfies_pairFmla
    (realization : StrongRealization)
    (data : CanonicalStrongData realization) :
    (strongFinalValuation realization data).satisfies_fmla
      (pairFmla (strongSupportPair realization)) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hleft | hselector
  · rcases List.mem_append.mp hleft with hbase | hsupport
    · exact (selectorExtendedValuation_satisfies_strongFmla
        (semanticAssignment realization data) data.branch).prop clause hbase
    · exact (strongFinalValuation_satisfies_supportUnits
        realization data).prop clause hsupport
  · exact (strongFinalValuation_satisfies_selectorFmla
      realization data).prop clause hselector

theorem strongRealization_yields_satisfying_pairFmla
    (realization : StrongRealization) :
    ∃ pair : StrongPair, ∃ valuation : Sat.Valuation,
      valuation.satisfies_fmla (pairFmla pair) := by
  obtain ⟨data⟩ := exists_canonicalStrongData realization
  exact ⟨strongSupportPair realization,
    strongFinalValuation realization data,
    strongRealization_satisfies_pairFmla realization data⟩

def PairLRATRefutation (pair : StrongPair) : Prop :=
  (pairFmla pair).proof Sat.Clause.nil

theorem noStrongRealization_of_all_pair_lrat
    (hunsat : ∀ pair : StrongPair, PairLRATRefutation pair) :
    ¬Nonempty StrongRealization := by
  rintro ⟨realization⟩
  obtain ⟨pair, valuation, hsatisfies⟩ :=
    strongRealization_yields_satisfying_pairFmla realization
  exact hunsat pair valuation hsatisfies

#print axioms strongFreeLabelSet_card
#print axioms strongLargeLabelSet_card
#print axioms strongSmallLabelSet_card
#print axioms supportUnitClauses_length
#print axioms guardedAssignmentClauses_length
#print axioms selectorFmla_length
#print axioms strongFmla_outside_selectorNamespace
#print axioms semanticAssignmentData_compatible
#print axioms strongRealization_satisfies_pairFmla
#print axioms noStrongRealization_of_all_pair_lrat

end ProfileDUUUDegreeNineStrongCaseCNF61
end R4333
