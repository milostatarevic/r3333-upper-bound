import PricingG.UUTD9Root4CNF

/-! Continuation-authored (locks/duuu), 2026-08-05. Twisted root-12 factor CNF,
role-aware clone (all 5 template sites label-side -> true; masks physical, unchanged). -/

/-!
# A factorized completion CNF for the strongest UUU degree-nine case

The pair-indexed formula is exact but would require up to 660 independent
refutations.  Here the three independent finite choices are selected in one
formula: a canonical-free labeling, a labeled large physical support, and a
labeled small physical support.  Pairwise guarded clauses impose exactly the
same cross edges as the corresponding pair-local assignment.

The semantic endpoint at the bottom is the trusted entrance for one DIMACS
export and one checked LRAT replay.
-/

namespace R4333
namespace UUTD9Root4Factor

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
open UUTD9Realization
open UUTD9Root4Case
open UUTD9Root4CNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex
abbrev FreeFactorChoice :=
  {freePerm : Equiv.Perm (Fin 5) // FreePermutationCompatible freePerm}
abbrev LargeFactorSupport := ↑twistedRoot4LargeSupportCandidates
abbrev SmallFactorSupport := ↑twistedRoot4CompatibleSmallSupportCandidates

theorem largeFactorSupport_card (support : LargeFactorSupport) :
    support.1.card = 5 := by
  exact (mem_independentSupportCandidates_iff 5 2 support.1).mp
    support.2 |>.1

theorem smallFactorSupport_card (support : SmallFactorSupport) :
    support.1.card = 4 := by
  have hsmall := (Finset.mem_filter.mp support.2).1
  exact (mem_independentSupportCandidates_iff 4 2 support.1).mp hsmall |>.1

def largeFactorOrder (support : LargeFactorSupport) : Fin 5 ≃ ↑support.1 :=
  (Finset.orderIsoOfFin support.1 (largeFactorSupport_card support)).toEquiv

def smallFactorOrder (support : SmallFactorSupport) : Fin 4 ≃ ↑support.1 :=
  (Finset.orderIsoOfFin support.1 (smallFactorSupport_card support)).toEquiv

def LargeFactorPermutationCompatible (support : LargeFactorSupport)
    (largePerm : Equiv.Perm (Fin 5)) : Prop :=
  ∀ left right : Fin 5, left ≠ right →
    k15Template true (largeLabelOrder left).1
        (largeLabelOrder right).1 =
      twistedRoot4LargePhysicalColoring
        (largeFactorOrder support (largePerm left)).1
        (largeFactorOrder support (largePerm right)).1

def SmallFactorPermutationCompatible (support : SmallFactorSupport)
    (smallPerm : Equiv.Perm (Fin 4)) : Prop :=
  ∀ left right : Fin 4, left ≠ right →
    k15Template true (smallLabelOrder left).1
        (smallLabelOrder right).1 =
      twistedRoot4SmallPhysicalColoring
        (smallFactorOrder support (smallPerm left)).1
        (smallFactorOrder support (smallPerm right)).1

instance (support : LargeFactorSupport) (largePerm : Equiv.Perm (Fin 5)) :
    Decidable (LargeFactorPermutationCompatible support largePerm) := by
  unfold LargeFactorPermutationCompatible
  infer_instance

instance (support : SmallFactorSupport) (smallPerm : Equiv.Perm (Fin 4)) :
    Decidable (SmallFactorPermutationCompatible support smallPerm) := by
  unfold SmallFactorPermutationCompatible
  infer_instance

structure LargeFactorChoice where
  support : LargeFactorSupport
  perm : Equiv.Perm (Fin 5)
  compatible : LargeFactorPermutationCompatible support perm
deriving DecidableEq

structure SmallFactorChoice where
  support : SmallFactorSupport
  perm : Equiv.Perm (Fin 4)
  compatible : SmallFactorPermutationCompatible support perm
deriving DecidableEq

def FreeFactorChoice.label (choice : FreeFactorChoice)
    (free : FiveVertex) : Fin 15 :=
  (freeLabelOrder (choice.1 free)).1

def LargeFactorChoice.label (_choice : LargeFactorChoice)
    (large : Fin 5) : Fin 15 :=
  (largeLabelOrder large).1

def LargeFactorChoice.physical (choice : LargeFactorChoice)
    (large : Fin 5) : Fin 15 :=
  (largeFactorOrder choice.support (choice.perm large)).1

def SmallFactorChoice.label (_choice : SmallFactorChoice)
    (small : Fin 4) : Fin 15 :=
  (smallLabelOrder small).1

def SmallFactorChoice.physical (choice : SmallFactorChoice)
    (small : Fin 4) : Fin 15 :=
  (smallFactorOrder choice.support (choice.perm small)).1

def supportOfMask (mask : Nat) : Finset (Fin 15) :=
  Finset.univ.filter fun position => mask.testBit position.val

def indexedLargeMask : Fin 11 → Nat :=
  ![9223, 6155, 3457, 16910, 3650, 28738, 1828, 2840, 17008, 6352, 9440]

def indexedSmallMask : Fin 60 → Nat :=
  ![1031, 8199, 2059, 4107, 9219, 6147, 269, 9221, 6153, 1409,
    2433, 3201, 12417, 3329, 526, 16398, 16902, 9222, 16906, 6154,
    1602, 2626, 3138, 12354, 20546, 24642, 3586, 28674, 16908, 804,
    1316, 1572, 24612, 1796, 792, 2328, 2584, 20504, 2824, 624,
    16496, 432, 16944, 2256, 4304, 16976, 6224, 6288, 2832, 1248,
    8416, 16992, 9312, 9376, 1824, 9408, 6336, 3648, 28736, 3456]

theorem indexedLargeMask_mem (index : Fin 11) :
    supportOfMask (indexedLargeMask index) ∈
      twistedRoot4LargeSupportCandidates := by
  fin_cases index <;> decide

theorem indexedSmallMask_mem (index : Fin 60) :
    supportOfMask (indexedSmallMask index) ∈
      twistedRoot4CompatibleSmallSupportCandidates := by
  fin_cases index <;> decide

def indexedLargeSupport (index : Fin 11) : LargeFactorSupport :=
  ⟨supportOfMask (indexedLargeMask index), indexedLargeMask_mem index⟩

def indexedSmallSupport (index : Fin 60) : SmallFactorSupport :=
  ⟨supportOfMask (indexedSmallMask index), indexedSmallMask_mem index⟩

theorem indexedLargeSupport_injective :
    Function.Injective indexedLargeSupport := by
  decide

theorem indexedSmallSupport_injective :
    Function.Injective indexedSmallSupport := by
  decide

theorem indexedLargeSupport_surjective :
    Function.Surjective indexedLargeSupport := by
  exact ((Fintype.bijective_iff_injective_and_card
    indexedLargeSupport).2 ⟨indexedLargeSupport_injective, by
      simp [LargeFactorSupport, twistedRoot4LargeSupportCandidates_card]⟩).2

theorem indexedSmallSupport_surjective :
    Function.Surjective indexedSmallSupport := by
  exact ((Fintype.bijective_iff_injective_and_card
    indexedSmallSupport).2 ⟨indexedSmallSupport_injective, by
      simp [SmallFactorSupport,
        twistedRoot4CompatibleSmallSupportCandidates_card]⟩).2

def largeFactorSupports : List LargeFactorSupport :=
  (List.finRange 11).map indexedLargeSupport

def smallFactorSupports : List SmallFactorSupport :=
  (List.finRange 60).map indexedSmallSupport

def compatibleLargeFactorPermutations (support : LargeFactorSupport) :
    List {largePerm : Equiv.Perm (Fin 5) //
      LargeFactorPermutationCompatible support largePerm} :=
  fiveVertexPermutations.filterMap fun largePerm =>
    if h : LargeFactorPermutationCompatible support largePerm then
      some ⟨largePerm, h⟩
    else none

def compatibleSmallFactorPermutations (support : SmallFactorSupport) :
    List {smallPerm : Equiv.Perm (Fin 4) //
      SmallFactorPermutationCompatible support smallPerm} :=
  fourVertexPermutations.filterMap fun smallPerm =>
    if h : SmallFactorPermutationCompatible support smallPerm then
      some ⟨smallPerm, h⟩
    else none

def freeFactorChoices : List FreeFactorChoice :=
  compatibleFreePermutations

def largeFactorChoices : List LargeFactorChoice :=
  largeFactorSupports.flatMap fun support =>
    (compatibleLargeFactorPermutations support).map fun perm =>
      ⟨support, perm.1, perm.2⟩

def smallFactorChoices : List SmallFactorChoice :=
  smallFactorSupports.flatMap fun support =>
    (compatibleSmallFactorPermutations support).map fun perm =>
      ⟨support, perm.1, perm.2⟩

theorem mem_freeFactorChoices (choice : FreeFactorChoice) :
    choice ∈ freeFactorChoices := by
  rcases choice with ⟨freePerm, hfree⟩
  simp only [freeFactorChoices, compatibleFreePermutations,
    List.mem_filterMap]
  exact ⟨freePerm, mem_fiveVertexPermutations freePerm, by simp [hfree]⟩

private theorem mem_fourVertexPermutations_factor
    (smallPerm : Equiv.Perm (Fin 4)) :
    smallPerm ∈ fourVertexPermutations := by
  apply mem_permsOfList_of_mem
  intro x _
  fin_cases x <;> simp

theorem mem_largeFactorChoices (choice : LargeFactorChoice) :
    choice ∈ largeFactorChoices := by
  rcases choice with ⟨support, perm, hcompatible⟩
  simp only [largeFactorChoices, List.mem_flatMap, List.mem_map]
  obtain ⟨index, hindex⟩ := indexedLargeSupport_surjective support
  refine ⟨support, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨index, by simp, hindex⟩
  refine ⟨⟨perm, hcompatible⟩, ?_, rfl⟩
  simp only [compatibleLargeFactorPermutations, List.mem_filterMap]
  exact ⟨perm, mem_fiveVertexPermutations perm,
    by simp [hcompatible]⟩

theorem mem_smallFactorChoices (choice : SmallFactorChoice) :
    choice ∈ smallFactorChoices := by
  rcases choice with ⟨support, perm, hcompatible⟩
  simp only [smallFactorChoices, List.mem_flatMap, List.mem_map]
  obtain ⟨index, hindex⟩ := indexedSmallSupport_surjective support
  refine ⟨support, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨index, by simp, hindex⟩
  refine ⟨⟨perm, hcompatible⟩, ?_, rfl⟩
  simp only [compatibleSmallFactorPermutations, List.mem_filterMap]
  exact ⟨perm, mem_fourVertexPermutations_factor perm,
    by simp [hcompatible]⟩

/-! ## The semantic choices occur in the three catalogues -/

noncomputable def semanticFreeFactorChoice
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) : FreeFactorChoice :=
  ⟨(semanticAssignmentData realization data).freePerm,
    (semanticAssignmentData_compatible realization data).1⟩

noncomputable def semanticLargeFactorChoice
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) : LargeFactorChoice where
  support := ⟨twistedRoot4LargePhysicalSupport realization,
    TwistedRoot4Realization.largePhysicalSupport_mem_candidates realization⟩
  perm := (semanticAssignmentData realization data).largePerm
  compatible := by
    have horder :
        largeFactorOrder
            ⟨twistedRoot4LargePhysicalSupport realization,
              TwistedRoot4Realization.largePhysicalSupport_mem_candidates
                realization⟩ =
          pairLargeOrder (twistedRoot4SupportPair realization) := by
      rfl
    intro left right hlr
    have h := (semanticAssignmentData_compatible realization data).2.1
      left right hlr
    rw [horder]
    exact h

noncomputable def semanticSmallFactorChoice
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) : SmallFactorChoice where
  support := ⟨twistedRoot4SmallSupport realization,
    realization.smallSupport_mem_compatibleCandidates⟩
  perm := (semanticAssignmentData realization data).smallPerm
  compatible := by
    have horder :
        smallFactorOrder
            ⟨twistedRoot4SmallSupport realization,
              realization.smallSupport_mem_compatibleCandidates⟩ =
          pairSmallOrder (twistedRoot4SupportPair realization) := by
      rfl
    intro left right hlr
    have h := (semanticAssignmentData_compatible realization data).2.2
      left right hlr
    rw [horder]
    exact h

theorem semanticFreeFactorChoice_label
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) (free : Fin 5) :
    (semanticFreeFactorChoice realization data).label free =
      (semanticAssignment realization data).1.freeLabel free := by
  rfl

theorem semanticLargeFactorChoice_physical
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) (large : Fin 5) :
    (semanticLargeFactorChoice realization data).physical large =
      (semanticAssignment realization data).1.largePhysical
        (twistedRoot4SupportPair realization) large := by
  rfl

theorem semanticLargeFactorChoice_label
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) (large : Fin 5) :
    (semanticLargeFactorChoice realization data).label large =
      (semanticAssignment realization data).1.largeLabel large := by
  rfl

theorem semanticSmallFactorChoice_physical
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) (small : Fin 4) :
    (semanticSmallFactorChoice realization data).physical small =
      (semanticAssignment realization data).1.smallPhysical
        (twistedRoot4SupportPair realization) small := by
  rfl

theorem semanticSmallFactorChoice_label
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) (small : Fin 4) :
    (semanticSmallFactorChoice realization data).label small =
      (semanticAssignment realization data).1.smallLabel small := by
  rfl

/-! ## The factorized formula -/

def factorSelectorAtom (category index : Nat) : Nat :=
  Nat.pair selectorNamespaceTag (Nat.pair category index)

def freeFactorSelectorAtom (choice : FreeFactorChoice) : Nat :=
  factorSelectorAtom 0 (List.idxOf choice freeFactorChoices)

def largeFactorSelectorAtom (choice : LargeFactorChoice) : Nat :=
  factorSelectorAtom 1 (List.idxOf choice largeFactorChoices)

def smallFactorSelectorAtom (choice : SmallFactorChoice) : Nat :=
  factorSelectorAtom 2 (List.idxOf choice smallFactorChoices)

def freeFactorAtLeastOneClause : Sat.Clause :=
  freeFactorChoices.map fun choice =>
    Sat.Literal.pos (freeFactorSelectorAtom choice)

def largeFactorAtLeastOneClause : Sat.Clause :=
  largeFactorChoices.map fun choice =>
    Sat.Literal.pos (largeFactorSelectorAtom choice)

def smallFactorAtLeastOneClause : Sat.Clause :=
  smallFactorChoices.map fun choice =>
    Sat.Literal.pos (smallFactorSelectorAtom choice)

/-- For every `right < left < size`, forbid the two indexed selectors from
being simultaneously true. -/
def factorAtMostOneClauses (category size : Nat) : Sat.Fmla :=
  (List.range size).flatMap fun left =>
    (List.range left).map fun right =>
      [Sat.Literal.neg (factorSelectorAtom category left),
       Sat.Literal.neg (factorSelectorAtom category right)]

def guardedLargeSupportClausesWithSelector (selector : Nat)
    (choice : LargeFactorChoice) : Sat.Fmla :=
  (List.finRange 15).map fun position : Fin 15 =>
    [Sat.Literal.neg selector,
     supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        selectedVertex (physicalBlockOneVertex position) (3 : Fin 4))
      (decide (position ∈ choice.support.1))]

def guardedLargeSupportClauses (choice : LargeFactorChoice) : Sat.Fmla :=
  guardedLargeSupportClausesWithSelector
    (largeFactorSelectorAtom choice) choice

def guardedSmallSupportClausesWithSelector (selector : Nat)
    (choice : SmallFactorChoice) : Sat.Fmla :=
  (List.finRange 15).map fun position : Fin 15 =>
    [Sat.Literal.neg selector,
     supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        selectedVertex (physicalBlockZeroVertex position) (3 : Fin 4))
      (decide (position ∈ choice.support.1))]

def guardedSmallSupportClauses (choice : SmallFactorChoice) : Sat.Fmla :=
  guardedSmallSupportClausesWithSelector
    (smallFactorSelectorAtom choice) choice

def factorGuardedEdgeClause (firstSelector secondSelector : Nat)
    (left right : TotalVertex) (q : ThreeColor) : Sat.Clause :=
  [Sat.Literal.neg firstSelector, Sat.Literal.neg secondSelector,
   Sat.Literal.pos
    (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right
      (decodedNormalHostColor q))]

def factorGuardedFreeLargeClausesWithSelectors
    (freeSelector largeSelector : Nat) (free : FreeFactorChoice)
    (large : LargeFactorChoice) : Sat.Fmla :=
  (List.finRange 5).flatMap fun freeIndex : FiveVertex =>
    (List.finRange 5).map fun largeIndex : Fin 5 =>
      factorGuardedEdgeClause
        freeSelector largeSelector
        (freeVertex freeIndex)
        (physicalBlockOneVertex (large.physical largeIndex))
        (k15Template true (free.label freeIndex)
          (large.label largeIndex))

def factorGuardedFreeLargeClauses (free : FreeFactorChoice)
    (large : LargeFactorChoice) : Sat.Fmla :=
  factorGuardedFreeLargeClausesWithSelectors
    (freeFactorSelectorAtom free) (largeFactorSelectorAtom large) free large

def factorGuardedFreeSmallClausesWithSelectors
    (freeSelector smallSelector : Nat) (free : FreeFactorChoice)
    (small : SmallFactorChoice) : Sat.Fmla :=
  (List.finRange 5).flatMap fun freeIndex : FiveVertex =>
    (List.finRange 4).map fun smallIndex : Fin 4 =>
      factorGuardedEdgeClause
        freeSelector smallSelector
        (freeVertex freeIndex)
        (physicalBlockZeroVertex (small.physical smallIndex))
        (k15Template true (free.label freeIndex)
          (small.label smallIndex))

def factorGuardedFreeSmallClauses (free : FreeFactorChoice)
    (small : SmallFactorChoice) : Sat.Fmla :=
  factorGuardedFreeSmallClausesWithSelectors
    (freeFactorSelectorAtom free) (smallFactorSelectorAtom small) free small

def factorGuardedLargeSmallClausesWithSelectors
    (largeSelector smallSelector : Nat) (large : LargeFactorChoice)
    (small : SmallFactorChoice) : Sat.Fmla :=
  (List.finRange 5).flatMap fun largeIndex : Fin 5 =>
    (List.finRange 4).map fun smallIndex : Fin 4 =>
      factorGuardedEdgeClause
        largeSelector smallSelector
        (physicalBlockOneVertex (large.physical largeIndex))
        (physicalBlockZeroVertex (small.physical smallIndex))
        (k15Template true (large.label largeIndex)
          (small.label smallIndex))

def factorGuardedLargeSmallClauses (large : LargeFactorChoice)
    (small : SmallFactorChoice) : Sat.Fmla :=
  factorGuardedLargeSmallClausesWithSelectors
    (largeFactorSelectorAtom large) (smallFactorSelectorAtom small) large small

def factorSupportFmla : Sat.Fmla :=
  let largeChoices := largeFactorChoices
  let smallChoices := smallFactorChoices
  (largeChoices.flatMap fun choice =>
    guardedLargeSupportClausesWithSelector
      (factorSelectorAtom 1 (List.idxOf choice largeChoices)) choice) ++
  (smallChoices.flatMap fun choice =>
    guardedSmallSupportClausesWithSelector
      (factorSelectorAtom 2 (List.idxOf choice smallChoices)) choice)

def factorCrossFmla : Sat.Fmla :=
  let freeChoices := freeFactorChoices
  let largeChoices := largeFactorChoices
  let smallChoices := smallFactorChoices
  (freeChoices.flatMap fun free =>
      let freeSelector := factorSelectorAtom 0
        (List.idxOf free freeChoices)
      largeChoices.flatMap fun large =>
        let largeSelector := factorSelectorAtom 1
          (List.idxOf large largeChoices)
        factorGuardedFreeLargeClausesWithSelectors
          freeSelector largeSelector free large) ++
    (freeChoices.flatMap fun free =>
      let freeSelector := factorSelectorAtom 0
        (List.idxOf free freeChoices)
      smallChoices.flatMap fun small =>
        let smallSelector := factorSelectorAtom 2
          (List.idxOf small smallChoices)
        factorGuardedFreeSmallClausesWithSelectors
          freeSelector smallSelector free small) ++
    (largeChoices.flatMap fun large =>
      let largeSelector := factorSelectorAtom 1
        (List.idxOf large largeChoices)
      smallChoices.flatMap fun small =>
        let smallSelector := factorSelectorAtom 2
          (List.idxOf small smallChoices)
        factorGuardedLargeSmallClausesWithSelectors
          largeSelector smallSelector large small)

def factorSelectorFmla : Sat.Fmla :=
  [freeFactorAtLeastOneClause,
   largeFactorAtLeastOneClause,
   smallFactorAtLeastOneClause] ++
    factorAtMostOneClauses 0 freeFactorChoices.length ++
    factorAtMostOneClauses 1 largeFactorChoices.length ++
    factorAtMostOneClauses 2 smallFactorChoices.length ++
    factorSupportFmla ++ factorCrossFmla

def factorFmla : Sat.Fmla :=
  fmla .uut 2 (Fin.last 15) ++ factorSelectorFmla

theorem guardedLargeSupportClauses_length (choice : LargeFactorChoice) :
    (guardedLargeSupportClauses choice).length = 15 := by
  simp [guardedLargeSupportClauses,
    guardedLargeSupportClausesWithSelector]

theorem guardedSmallSupportClauses_length (choice : SmallFactorChoice) :
    (guardedSmallSupportClauses choice).length = 15 := by
  simp [guardedSmallSupportClauses,
    guardedSmallSupportClausesWithSelector]

theorem factorGuardedFreeLargeClauses_length
    (free : FreeFactorChoice) (large : LargeFactorChoice) :
    (factorGuardedFreeLargeClauses free large).length = 25 := by
  simp [factorGuardedFreeLargeClauses,
    factorGuardedFreeLargeClausesWithSelectors]

theorem factorGuardedFreeSmallClauses_length
    (free : FreeFactorChoice) (small : SmallFactorChoice) :
    (factorGuardedFreeSmallClauses free small).length = 20 := by
  simp [factorGuardedFreeSmallClauses,
    factorGuardedFreeSmallClausesWithSelectors]

theorem factorGuardedLargeSmallClauses_length
    (large : LargeFactorChoice) (small : SmallFactorChoice) :
    (factorGuardedLargeSmallClauses large small).length = 20 := by
  simp [factorGuardedLargeSmallClauses,
    factorGuardedLargeSmallClausesWithSelectors]

/-! ## A selector valuation with exactly one choice in each category -/

noncomputable def factorExtendedValuation
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice)
    (base : Sat.Valuation) : Sat.Valuation :=
  fun atom =>
    @ite Prop (InSequentialNamespace selectorNamespaceTag atom)
      (Classical.propDecidable _)
      (let payload := (Nat.unpair atom).2
       let categoryAndIndex := Nat.unpair payload
       (categoryAndIndex.1 = 0 ∧
          categoryAndIndex.2 =
            List.idxOf selectedFree freeFactorChoices) ∨
       (categoryAndIndex.1 = 1 ∧
          categoryAndIndex.2 =
            List.idxOf selectedLarge largeFactorChoices) ∨
       (categoryAndIndex.1 = 2 ∧
          categoryAndIndex.2 =
            List.idxOf selectedSmall smallFactorChoices))
      (base atom)

theorem factorExtendedValuation_eq_of_outside
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice)
    (base : Sat.Valuation) (atom : Nat)
    (houtside : ¬InSequentialNamespace selectorNamespaceTag atom) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base atom ↔
      base atom := by
  simp [factorExtendedValuation, houtside]

@[simp] theorem factorExtendedValuation_freeSelectorAtom
    (selectedFree assignment : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice) (base : Sat.Valuation) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base
        (freeFactorSelectorAtom assignment) ↔
      assignment = selectedFree := by
  simpa [factorExtendedValuation, freeFactorSelectorAtom,
    factorSelectorAtom, InSequentialNamespace] using
      (List.idxOf_inj (mem_freeFactorChoices assignment))

@[simp] theorem factorExtendedValuation_largeSelectorAtom
    (selectedFree : FreeFactorChoice)
    (selectedLarge assignment : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice) (base : Sat.Valuation) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base
        (largeFactorSelectorAtom assignment) ↔
      assignment = selectedLarge := by
  simpa [factorExtendedValuation, largeFactorSelectorAtom,
    factorSelectorAtom, InSequentialNamespace] using
      (List.idxOf_inj (mem_largeFactorChoices assignment))

@[simp] theorem factorExtendedValuation_smallSelectorAtom
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall assignment : SmallFactorChoice)
    (base : Sat.Valuation) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base
        (smallFactorSelectorAtom assignment) ↔
      assignment = selectedSmall := by
  simpa [factorExtendedValuation, smallFactorSelectorAtom,
    factorSelectorAtom, InSequentialNamespace] using
      (List.idxOf_inj (mem_smallFactorChoices assignment))

@[simp] theorem factorExtendedValuation_freeIndex
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice) (base : Sat.Valuation)
    (index : Nat) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base
        (factorSelectorAtom 0 index) ↔
      index = List.idxOf selectedFree freeFactorChoices := by
  simp [factorExtendedValuation, factorSelectorAtom, InSequentialNamespace]

@[simp] theorem factorExtendedValuation_largeIndex
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice) (base : Sat.Valuation)
    (index : Nat) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base
        (factorSelectorAtom 1 index) ↔
      index = List.idxOf selectedLarge largeFactorChoices := by
  simp [factorExtendedValuation, factorSelectorAtom, InSequentialNamespace]

@[simp] theorem factorExtendedValuation_smallIndex
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice) (base : Sat.Valuation)
    (index : Nat) :
    factorExtendedValuation selectedFree selectedLarge selectedSmall base
        (factorSelectorAtom 2 index) ↔
      index = List.idxOf selectedSmall smallFactorChoices := by
  simp [factorExtendedValuation, factorSelectorAtom, InSequentialNamespace]

private theorem factor_neg_iff_of_atom_iff
    (literal : Sat.Literal) (left right : Sat.Valuation)
    (h : left (literalAtom literal) ↔ right (literalAtom literal)) :
    left.neg literal ↔ right.neg literal := by
  cases literal <;> simp only [literalAtom, Sat.Valuation.neg] at h ⊢
  · exact not_congr h
  · exact h

private theorem factor_satisfies_of_agrees_on_clause
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
        exact (factor_neg_iff_of_atom_iff literal left right
          (hagrees literal (List.Mem.head tail))).mp hneg

theorem factorExtendedValuation_satisfies_strongFmla
    (selectedFree : FreeFactorChoice)
    (selectedLarge : LargeFactorChoice)
    (selectedSmall : SmallFactorChoice)
    (branch : CanonicalBranch .uut 2 (Fin.last 15)) :
    (factorExtendedValuation selectedFree selectedLarge selectedSmall
      (finalValuation branch)).satisfies_fmla
        (fmla .uut 2 (Fin.last 15)) := by
  have hbase := canonicalBranch_satisfies_fmla branch
  constructor
  intro clause hclause
  apply factor_satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact factorExtendedValuation_eq_of_outside
      selectedFree selectedLarge selectedSmall _ _
      (twistedRoot4Fmla_outside_selectorNamespace
        clause hclause literal hliteral)
  · exact hbase.prop clause hclause

noncomputable def twistedRoot4FactorFinalValuation
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) : Sat.Valuation :=
  factorExtendedValuation
    (semanticFreeFactorChoice realization data)
    (semanticLargeFactorChoice realization data)
    (semanticSmallFactorChoice realization data)
    (finalValuation data.branch)

theorem twistedRoot4FactorFinalValuation_ordinaryEdgeAtom
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization)
    (left right : TotalVertex) (hne : left ≠ right) (q : Fin 4) :
    twistedRoot4FactorFinalValuation realization data
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right q) ↔
      totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        left right = q := by
  unfold twistedRoot4FactorFinalValuation
  rw [factorExtendedValuation_eq_of_outside]
  · exact ProfileDDegreeTenMatrixCNF.finalValuation_ordinaryEdgeAtom
      data.branch left right hne q
  · unfold selectorNamespaceTag
      OutsideDegreeCapCNF.outsideIncidentEdgeAtom
    apply OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    · exact lt_of_le_of_lt (Nat.min_le_left left.val right.val)
        (left.isLt.trans (by omega))
    · exact max_lt (left.isLt.trans (by omega))
        (right.isLt.trans (by omega))

theorem twistedRoot4FactorFinalValuation_satisfies_atLeastOne
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      [freeFactorAtLeastOneClause,
       largeFactorAtLeastOneClause,
       smallFactorAtLeastOneClause] := by
  constructor
  intro clause hclause
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with rfl | rfl | rfl
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.pos (freeFactorSelectorAtom
        (semanticFreeFactorChoice realization data)))
    · exact List.mem_map.mpr ⟨_,
        mem_freeFactorChoices _, rfl⟩
    · change factorExtendedValuation _ _ _ _ _
      exact (factorExtendedValuation_freeSelectorAtom _ _ _ _ _).2 rfl
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.pos (largeFactorSelectorAtom
        (semanticLargeFactorChoice realization data)))
    · exact List.mem_map.mpr ⟨_,
        mem_largeFactorChoices _, rfl⟩
    · change factorExtendedValuation _ _ _ _ _
      exact (factorExtendedValuation_largeSelectorAtom _ _ _ _ _).2 rfl
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.pos (smallFactorSelectorAtom
        (semanticSmallFactorChoice realization data)))
    · exact List.mem_map.mpr ⟨_,
        mem_smallFactorChoices _, rfl⟩
    · change factorExtendedValuation _ _ _ _ _
      exact (factorExtendedValuation_smallSelectorAtom _ _ _ _ _).2 rfl

theorem twistedRoot4FactorFinalValuation_satisfies_freeAtMostOne
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      (factorAtMostOneClauses 0 freeFactorChoices.length) := by
  constructor
  intro clause hclause
  obtain ⟨left, hleft, hrightClause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨right, hright, rfl⟩ := List.mem_map.mp hrightClause
  have hlt : right < left := List.mem_range.mp hright
  by_cases hselected : left = List.idxOf
      (semanticFreeFactorChoice realization data) freeFactorChoices
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg (factorSelectorAtom 0 right))
    · exact List.Mem.tail _ (List.Mem.head _)
    · change ¬twistedRoot4FactorFinalValuation realization data
        (factorSelectorAtom 0 right)
      rw [show twistedRoot4FactorFinalValuation realization data =
          factorExtendedValuation _ _ _ _ from rfl,
        factorExtendedValuation_freeIndex]
      omega
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg (factorSelectorAtom 0 left))
    · exact List.Mem.head _
    · change ¬twistedRoot4FactorFinalValuation realization data
        (factorSelectorAtom 0 left)
      rw [show twistedRoot4FactorFinalValuation realization data =
          factorExtendedValuation _ _ _ _ from rfl,
        factorExtendedValuation_freeIndex]
      exact hselected

theorem twistedRoot4FactorFinalValuation_satisfies_largeAtMostOne
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      (factorAtMostOneClauses 1 largeFactorChoices.length) := by
  constructor
  intro clause hclause
  obtain ⟨left, hleft, hrightClause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨right, hright, rfl⟩ := List.mem_map.mp hrightClause
  have hlt : right < left := List.mem_range.mp hright
  by_cases hselected : left = List.idxOf
      (semanticLargeFactorChoice realization data) largeFactorChoices
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg (factorSelectorAtom 1 right))
    · exact List.Mem.tail _ (List.Mem.head _)
    · change ¬twistedRoot4FactorFinalValuation realization data
        (factorSelectorAtom 1 right)
      rw [show twistedRoot4FactorFinalValuation realization data =
          factorExtendedValuation _ _ _ _ from rfl,
        factorExtendedValuation_largeIndex]
      omega
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg (factorSelectorAtom 1 left))
    · exact List.Mem.head _
    · change ¬twistedRoot4FactorFinalValuation realization data
        (factorSelectorAtom 1 left)
      rw [show twistedRoot4FactorFinalValuation realization data =
          factorExtendedValuation _ _ _ _ from rfl,
        factorExtendedValuation_largeIndex]
      exact hselected

theorem twistedRoot4FactorFinalValuation_satisfies_smallAtMostOne
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      (factorAtMostOneClauses 2 smallFactorChoices.length) := by
  constructor
  intro clause hclause
  obtain ⟨left, hleft, hrightClause⟩ := List.mem_flatMap.mp hclause
  obtain ⟨right, hright, rfl⟩ := List.mem_map.mp hrightClause
  have hlt : right < left := List.mem_range.mp hright
  by_cases hselected : left = List.idxOf
      (semanticSmallFactorChoice realization data) smallFactorChoices
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg (factorSelectorAtom 2 right))
    · exact List.Mem.tail _ (List.Mem.head _)
    · change ¬twistedRoot4FactorFinalValuation realization data
        (factorSelectorAtom 2 right)
      rw [show twistedRoot4FactorFinalValuation realization data =
          factorExtendedValuation _ _ _ _ from rfl,
        factorExtendedValuation_smallIndex]
      omega
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg (factorSelectorAtom 2 left))
    · exact List.Mem.head _
    · change ¬twistedRoot4FactorFinalValuation realization data
        (factorSelectorAtom 2 left)
      rw [show twistedRoot4FactorFinalValuation realization data =
          factorExtendedValuation _ _ _ _ from rfl,
        factorExtendedValuation_smallIndex]
      exact hselected

private theorem factor_selected_ne_blockZero (position : Fin 15) :
    selectedVertex ≠ physicalBlockZeroVertex position := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 2 0 (by decide)
      (Fin.last 15).isLt position.isLt)

private theorem factor_selected_ne_blockOne (position : Fin 15) :
    selectedVertex ≠ physicalBlockOneVertex position := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 2 1 (by decide)
      (Fin.last 15).isLt position.isLt)

private theorem factor_satisfies_guarded_support_selected
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization)
    (selector : Nat) (target : TotalVertex)
    (hne : selectedVertex ≠ target) (member : Bool)
    (htruth :
      (totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex target = (3 : Fin 4)) ↔ member = true) :
    (twistedRoot4FactorFinalValuation realization data).satisfies
      [Sat.Literal.neg selector,
       supportLiteral
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)) member] := by
  cases hmember : member
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)))
    · simpa [supportLiteral, hmember] using
        (List.Mem.tail (Sat.Literal.neg selector)
          (List.Mem.head ([] : List Sat.Literal)))
    · change ¬twistedRoot4FactorFinalValuation realization data
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4))
      rw [twistedRoot4FactorFinalValuation_ordinaryEdgeAtom realization data
        selectedVertex target hne (3 : Fin 4)]
      intro hcolor
      have := htruth.mp hcolor
      simp [hmember] at this
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.pos
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)))
    · simpa [supportLiteral, hmember] using
        (List.Mem.tail (Sat.Literal.neg selector)
          (List.Mem.head ([] : List Sat.Literal)))
    · change twistedRoot4FactorFinalValuation realization data
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4))
      rw [twistedRoot4FactorFinalValuation_ordinaryEdgeAtom realization data
        selectedVertex target hne (3 : Fin 4)]
      exact htruth.mpr (by simp [hmember])

theorem twistedRoot4FactorFinalValuation_satisfies_supportFmla
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      factorSupportFmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hlarge | hsmall
  · obtain ⟨choice, _hchoice, hpositionClause⟩ :=
      List.mem_flatMap.mp hlarge
    obtain ⟨position, _hposition, rfl⟩ :=
      List.mem_map.mp hpositionClause
    by_cases hselected : choice =
        semanticLargeFactorChoice realization data
    · subst choice
      apply factor_satisfies_guarded_support_selected realization data
        (largeFactorSelectorAtom
          (semanticLargeFactorChoice realization data))
        (physicalBlockOneVertex position)
        (factor_selected_ne_blockOne position)
      simpa [semanticLargeFactorChoice, twistedRoot4SupportPair] using
        data.blockOne_support_iff position
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg (largeFactorSelectorAtom choice))
      · exact List.Mem.head _
      · change ¬twistedRoot4FactorFinalValuation realization data
          (largeFactorSelectorAtom choice)
        rw [show twistedRoot4FactorFinalValuation realization data =
            factorExtendedValuation _ _ _ _ from rfl,
          factorExtendedValuation_largeSelectorAtom]
        exact hselected
  · obtain ⟨choice, _hchoice, hpositionClause⟩ :=
      List.mem_flatMap.mp hsmall
    obtain ⟨position, _hposition, rfl⟩ :=
      List.mem_map.mp hpositionClause
    by_cases hselected : choice =
        semanticSmallFactorChoice realization data
    · subst choice
      apply factor_satisfies_guarded_support_selected realization data
        (smallFactorSelectorAtom
          (semanticSmallFactorChoice realization data))
        (physicalBlockZeroVertex position)
        (factor_selected_ne_blockZero position)
      simpa [semanticSmallFactorChoice, twistedRoot4SupportPair] using
        data.blockZero_support_iff position
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg (smallFactorSelectorAtom choice))
      · exact List.Mem.head _
      · change ¬twistedRoot4FactorFinalValuation realization data
          (smallFactorSelectorAtom choice)
        rw [show twistedRoot4FactorFinalValuation realization data =
            factorExtendedValuation _ _ _ _ from rfl,
          factorExtendedValuation_smallSelectorAtom]
        exact hselected

private theorem factor_free_ne_blockOne
    (free : Fin 5) (position : Fin 15) :
    freeVertex free ≠ physicalBlockOneVertex position := by
  intro h
  have hval := congrArg Fin.val h
  simp [freeVertex, physicalBlockOneVertex, tailVertex] at hval
  omega

private theorem factor_free_ne_blockZero
    (free : Fin 5) (position : Fin 15) :
    freeVertex free ≠ physicalBlockZeroVertex position := by
  intro h
  have hval := congrArg Fin.val h
  simp [freeVertex, physicalBlockZeroVertex, tailVertex] at hval
  omega

private theorem factor_blockOne_ne_blockZero
    (large small : Fin 15) :
    physicalBlockOneVertex large ≠ physicalBlockZeroVertex small := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 1 0 (by decide) large.isLt small.isLt)

private theorem factor_satisfies_guarded_edge_selected
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization)
    (firstSelector secondSelector : Nat)
    (left right : TotalVertex) (hne : left ≠ right) (q : ThreeColor)
    (hedge :
      totalColoring data.branch.toDegreeFlooredFiveExtension.toFiveExtension
        left right = decodedNormalHostColor q) :
    (twistedRoot4FactorFinalValuation realization data).satisfies
      (factorGuardedEdgeClause firstSelector secondSelector left right q) := by
  apply satisfies_of_mem_holds
    (l := Sat.Literal.pos
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right
        (decodedNormalHostColor q)))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · change twistedRoot4FactorFinalValuation realization data
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right
        (decodedNormalHostColor q))
    rw [twistedRoot4FactorFinalValuation_ordinaryEdgeAtom realization data
      left right hne (decodedNormalHostColor q)]
    exact hedge

theorem twistedRoot4FactorFinalValuation_satisfies_crossFmla
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      factorCrossFmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hfirstTwo | hlargeSmall
  · rcases List.mem_append.mp hfirstTwo with hfreeLarge | hfreeSmall
    · obtain ⟨free, _hfree, hlargeOuter⟩ :=
        List.mem_flatMap.mp hfreeLarge
      obtain ⟨large, _hlarge, hfreeIndexOuter⟩ :=
        List.mem_flatMap.mp hlargeOuter
      obtain ⟨freeIndex, _hfreeIndex, hlargeIndexClause⟩ :=
        List.mem_flatMap.mp hfreeIndexOuter
      obtain ⟨largeIndex, _hlargeIndex, rfl⟩ :=
        List.mem_map.mp hlargeIndexClause
      by_cases hfreeSelected : free =
          semanticFreeFactorChoice realization data
      · subst free
        by_cases hlargeSelected : large =
            semanticLargeFactorChoice realization data
        · subst large
          apply factor_satisfies_guarded_edge_selected realization data
            (freeFactorSelectorAtom
              (semanticFreeFactorChoice realization data))
            (largeFactorSelectorAtom
              (semanticLargeFactorChoice realization data))
            (freeVertex freeIndex)
            (physicalBlockOneVertex
              ((semanticLargeFactorChoice realization data).physical
                largeIndex))
            (factor_free_ne_blockOne freeIndex _) _
          simpa [semanticFreeFactorChoice_label,
            semanticLargeFactorChoice_physical,
            semanticLargeFactorChoice_label] using
              semanticAssignment_freeLarge_edge realization data
                freeIndex largeIndex
        · apply satisfies_of_mem_holds
            (l := Sat.Literal.neg (largeFactorSelectorAtom large))
          · exact List.Mem.tail _ (List.Mem.head _)
          · change ¬twistedRoot4FactorFinalValuation realization data
              (largeFactorSelectorAtom large)
            rw [show twistedRoot4FactorFinalValuation realization data =
                factorExtendedValuation _ _ _ _ from rfl,
              factorExtendedValuation_largeSelectorAtom]
            exact hlargeSelected
      · apply satisfies_of_mem_holds
          (l := Sat.Literal.neg (freeFactorSelectorAtom free))
        · exact List.Mem.head _
        · change ¬twistedRoot4FactorFinalValuation realization data
            (freeFactorSelectorAtom free)
          rw [show twistedRoot4FactorFinalValuation realization data =
              factorExtendedValuation _ _ _ _ from rfl,
            factorExtendedValuation_freeSelectorAtom]
          exact hfreeSelected
    · obtain ⟨free, _hfree, hsmallOuter⟩ :=
        List.mem_flatMap.mp hfreeSmall
      obtain ⟨small, _hsmall, hfreeIndexOuter⟩ :=
        List.mem_flatMap.mp hsmallOuter
      obtain ⟨freeIndex, _hfreeIndex, hsmallIndexClause⟩ :=
        List.mem_flatMap.mp hfreeIndexOuter
      obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
        List.mem_map.mp hsmallIndexClause
      by_cases hfreeSelected : free =
          semanticFreeFactorChoice realization data
      · subst free
        by_cases hsmallSelected : small =
            semanticSmallFactorChoice realization data
        · subst small
          apply factor_satisfies_guarded_edge_selected realization data
            (freeFactorSelectorAtom
              (semanticFreeFactorChoice realization data))
            (smallFactorSelectorAtom
              (semanticSmallFactorChoice realization data))
            (freeVertex freeIndex)
            (physicalBlockZeroVertex
              ((semanticSmallFactorChoice realization data).physical
                smallIndex))
            (factor_free_ne_blockZero freeIndex _) _
          simpa [semanticFreeFactorChoice_label,
            semanticSmallFactorChoice_physical,
            semanticSmallFactorChoice_label] using
              semanticAssignment_freeSmall_edge realization data
                freeIndex smallIndex
        · apply satisfies_of_mem_holds
            (l := Sat.Literal.neg (smallFactorSelectorAtom small))
          · exact List.Mem.tail _ (List.Mem.head _)
          · change ¬twistedRoot4FactorFinalValuation realization data
              (smallFactorSelectorAtom small)
            rw [show twistedRoot4FactorFinalValuation realization data =
                factorExtendedValuation _ _ _ _ from rfl,
              factorExtendedValuation_smallSelectorAtom]
            exact hsmallSelected
      · apply satisfies_of_mem_holds
          (l := Sat.Literal.neg (freeFactorSelectorAtom free))
        · exact List.Mem.head _
        · change ¬twistedRoot4FactorFinalValuation realization data
            (freeFactorSelectorAtom free)
          rw [show twistedRoot4FactorFinalValuation realization data =
              factorExtendedValuation _ _ _ _ from rfl,
            factorExtendedValuation_freeSelectorAtom]
          exact hfreeSelected
  · obtain ⟨large, _hlarge, hsmallOuter⟩ :=
      List.mem_flatMap.mp hlargeSmall
    obtain ⟨small, _hsmall, hlargeIndexOuter⟩ :=
      List.mem_flatMap.mp hsmallOuter
    obtain ⟨largeIndex, _hlargeIndex, hsmallIndexClause⟩ :=
      List.mem_flatMap.mp hlargeIndexOuter
    obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
      List.mem_map.mp hsmallIndexClause
    by_cases hlargeSelected : large =
        semanticLargeFactorChoice realization data
    · subst large
      by_cases hsmallSelected : small =
          semanticSmallFactorChoice realization data
      · subst small
        apply factor_satisfies_guarded_edge_selected realization data
          (largeFactorSelectorAtom
            (semanticLargeFactorChoice realization data))
          (smallFactorSelectorAtom
            (semanticSmallFactorChoice realization data))
          (physicalBlockOneVertex
            ((semanticLargeFactorChoice realization data).physical
              largeIndex))
          (physicalBlockZeroVertex
            ((semanticSmallFactorChoice realization data).physical
              smallIndex))
          (factor_blockOne_ne_blockZero _ _) _
        simpa [semanticLargeFactorChoice_physical,
          semanticSmallFactorChoice_physical,
          semanticLargeFactorChoice_label,
          semanticSmallFactorChoice_label] using
            semanticAssignment_largeSmall_edge realization data
              largeIndex smallIndex
      · apply satisfies_of_mem_holds
          (l := Sat.Literal.neg (smallFactorSelectorAtom small))
        · exact List.Mem.tail _ (List.Mem.head _)
        · change ¬twistedRoot4FactorFinalValuation realization data
            (smallFactorSelectorAtom small)
          rw [show twistedRoot4FactorFinalValuation realization data =
              factorExtendedValuation _ _ _ _ from rfl,
            factorExtendedValuation_smallSelectorAtom]
          exact hsmallSelected
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg (largeFactorSelectorAtom large))
      · exact List.Mem.head _
      · change ¬twistedRoot4FactorFinalValuation realization data
          (largeFactorSelectorAtom large)
        rw [show twistedRoot4FactorFinalValuation realization data =
            factorExtendedValuation _ _ _ _ from rfl,
          factorExtendedValuation_largeSelectorAtom]
        exact hlargeSelected

theorem twistedRoot4FactorFinalValuation_satisfies_selectorFmla
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      factorSelectorFmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hthroughSupport | hcross
  · rcases List.mem_append.mp hthroughSupport with hthroughSmallAmo | hsupport
    · rcases List.mem_append.mp hthroughSmallAmo with hthroughLargeAmo | hsmallAmo
      · rcases List.mem_append.mp hthroughLargeAmo with hthroughFreeAmo | hlargeAmo
        · rcases List.mem_append.mp hthroughFreeAmo with hatLeast | hfreeAmo
          · exact (twistedRoot4FactorFinalValuation_satisfies_atLeastOne
              realization data).prop clause hatLeast
          · exact (twistedRoot4FactorFinalValuation_satisfies_freeAtMostOne
              realization data).prop clause hfreeAmo
        · exact (twistedRoot4FactorFinalValuation_satisfies_largeAtMostOne
            realization data).prop clause hlargeAmo
      · exact (twistedRoot4FactorFinalValuation_satisfies_smallAtMostOne
          realization data).prop clause hsmallAmo
    · exact (twistedRoot4FactorFinalValuation_satisfies_supportFmla
        realization data).prop clause hsupport
  · exact (twistedRoot4FactorFinalValuation_satisfies_crossFmla
      realization data).prop clause hcross

theorem twistedRoot4Realization_satisfies_factorFmla
    (realization : TwistedRoot4Realization)
    (data : CanonicalStrongData realization) :
    (twistedRoot4FactorFinalValuation realization data).satisfies_fmla
      factorFmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hbase | hfactor
  · exact (factorExtendedValuation_satisfies_strongFmla
      (semanticFreeFactorChoice realization data)
      (semanticLargeFactorChoice realization data)
      (semanticSmallFactorChoice realization data)
      data.branch).prop clause hbase
  · exact (twistedRoot4FactorFinalValuation_satisfies_selectorFmla
      realization data).prop clause hfactor

theorem twistedRoot4Realization_yields_satisfying_factorFmla
    (realization : TwistedRoot4Realization) :
    ∃ valuation : Sat.Valuation, valuation.satisfies_fmla factorFmla := by
  obtain ⟨data⟩ := exists_canonicalStrongData realization
  exact ⟨twistedRoot4FactorFinalValuation realization data,
    twistedRoot4Realization_satisfies_factorFmla realization data⟩

def FactorLRATRefutation : Prop :=
  factorFmla.proof Sat.Clause.nil

theorem noStrongRealization_of_factor_lrat
    (hunsat : FactorLRATRefutation) :
    ¬Nonempty TwistedRoot4Realization := by
  rintro ⟨realization⟩
  obtain ⟨valuation, hsatisfies⟩ :=
    twistedRoot4Realization_yields_satisfying_factorFmla realization
  exact hunsat valuation hsatisfies

#print axioms indexedLargeMask_mem
#print axioms indexedSmallMask_mem
#print axioms indexedLargeSupport_surjective
#print axioms indexedSmallSupport_surjective
#print axioms twistedRoot4Realization_satisfies_factorFmla
#print axioms noStrongRealization_of_factor_lrat

end UUTD9Root4Factor
end R4333
