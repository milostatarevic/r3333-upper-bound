import R4333Lean.ClauseCore
import R4333Lean.ContinuationDegreeNineTwistedRoot1QuotientFormula61

/-! Continuation-authored (locks/duuu), 2026-08-05.
Twisted case (slot 3, root 1) quotient-semantic clone of
ProfileDUUUDegreeNineQuotientSemantic61.  This is the per-case endpoint: it
ties the root-1 quotient formula back to
`DegreeNineCaseObstruction twistedRoot1Case`.  The proof text is verbatim
from the archive original up to renames: the strongCase companion
namespaces become their root-1 clones, `StrongRealization` becomes
`TwistedRoot1Realization`, `strongCase` becomes `twistedRoot1Case`,
`strongRealization_reduces_to_72` becomes
`twistedRoot1Realization_reduces_to_132`, and
`strongFmla_outside_selectorNamespace` becomes
`twistedRoot1Fmla_outside_selectorNamespace`.  Unlike the root-12 clone,
root 1 has a trivial root stabilizer: there is no RootStabilizer module to
open, the representative count is the full `Fin 132` product (11 × 12), and
every `Fin 72` in the original becomes `Fin 132`.  One extra root-1-only
change: the free representative permutation is the involution
`freeRepresentativeEquiv` (not the identity), so
`quotientRepresentativeFree_label` evaluates `explicitFreeLabelOrder_eq` at
the permuted position `freeRepresentativeEquiv position`.  No k15Template
occurs here and no data tables live here; the module is LRAT-trace-free by
construction (imports only ClauseCore and the root-1 quotient formula
module). -/

/-!
# Semantic soundness of the exact 132-representative root-1 quotient

The companion formula module fixes the clause/index data.  This module proves
that every `TwistedRoot1Realization` produces a satisfying valuation of that
exact formula.  Consequently a kernel-checked LRAT refutation of the single
quotient formula rules out the twisted root-1 degree-nine case.
-/

namespace R4333
namespace ContinuationDegreeNineTwistedRoot1QuotientSemantic61

open ColoringJoinRows FiniteColorCNF
open SequentialAtMostCNF SequentialAtMostManyCNF
open SingleRootStarCNF
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open ProfileDUUUDegreeNineCaseRealization61
open ContinuationDegreeNineTwistedRoot1Case61
open ContinuationDegreeNineTwistedRoot1CaseCNF61
open ContinuationDegreeNineTwistedRoot1CaseFactorCNF61
open ContinuationDegreeNineTwistedRoot1PhysicalSymmetry61
open ContinuationDegreeNineTwistedRoot1FactorOrbitCoverage61
open ContinuationDegreeNineTwistedRoot1QuotientFormula61
open ProfileDDegreeTenMatrixCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex

/-! ## The exact one-selector valuation -/

noncomputable def quotientExtendedValuation (selected : Fin 132)
    (base : Sat.Valuation) : Sat.Valuation :=
  fun atom =>
    @ite Prop (InSequentialNamespace selectorNamespaceTag atom)
      (Classical.propDecidable _)
      ((Nat.unpair atom).2 = selected.val)
      (base atom)

theorem quotientExtendedValuation_eq_of_outside (selected : Fin 132)
    (base : Sat.Valuation) (atom : Nat)
    (houtside : ¬InSequentialNamespace selectorNamespaceTag atom) :
    quotientExtendedValuation selected base atom ↔ base atom := by
  simp [quotientExtendedValuation, houtside]

@[simp] theorem quotientExtendedValuation_selectorAtom
    (selected assignment : Fin 132) (base : Sat.Valuation) :
    quotientExtendedValuation selected base
        (quotientSelectorAtom assignment) ↔
      assignment = selected := by
  simp [quotientExtendedValuation, quotientSelectorAtom,
    InSequentialNamespace, Fin.ext_iff]

private theorem quotient_neg_iff_of_atom_iff
    (literal : Sat.Literal) (left right : Sat.Valuation)
    (h : left (literalAtom literal) ↔ right (literalAtom literal)) :
    left.neg literal ↔ right.neg literal := by
  cases literal <;> simp only [literalAtom, Sat.Valuation.neg] at h ⊢
  · exact not_congr h
  · exact h

private theorem quotient_satisfies_of_agrees_on_clause
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
        exact (quotient_neg_iff_of_atom_iff literal left right
          (hagrees literal (List.Mem.head tail))).mp hneg

theorem quotientExtendedValuation_satisfies_strongFmla
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15)) :
    (quotientExtendedValuation selected
      (finalValuation branch)).satisfies_fmla
        (fmla .uuu 2 (Fin.last 15)) := by
  have hbase := canonicalBranch_satisfies_fmla branch
  constructor
  intro clause hclause
  apply quotient_satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact quotientExtendedValuation_eq_of_outside selected _ _
      (twistedRoot1Fmla_outside_selectorNamespace
        clause hclause literal hliteral)
  · exact hbase.prop clause hclause

noncomputable def quotientFinalValuation (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15)) : Sat.Valuation :=
  quotientExtendedValuation selected (finalValuation branch)

theorem quotientFinalValuation_ordinaryEdgeAtom
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (left right : TotalVertex) (hne : left ≠ right) (q : Fin 4) :
    quotientFinalValuation selected branch
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right q) ↔
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        left right = q := by
  unfold quotientFinalValuation
  rw [quotientExtendedValuation_eq_of_outside]
  · exact ProfileDDegreeTenMatrixCNF.finalValuation_ordinaryEdgeAtom
      branch left right hne q
  · unfold selectorNamespaceTag
      OutsideDegreeCapCNF.outsideIncidentEdgeAtom
    apply OutsideDegreeCapCNF.edgeAtom_outside_counterNamespace
    · exact lt_of_le_of_lt (Nat.min_le_left left.val right.val)
        (left.isLt.trans (by omega))
    · exact max_lt (left.isLt.trans (by omega))
        (right.isLt.trans (by omega))

/-! ## Small semantic helpers for selected representative clauses -/

private theorem quotient_selected_ne_blockZero (position : Fin 15) :
    selectedVertex ≠ physicalBlockZeroVertex position := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 2 0 (by decide)
      (Fin.last 15).isLt position.isLt)

private theorem quotient_selected_ne_blockOne (position : Fin 15) :
    selectedVertex ≠ physicalBlockOneVertex position := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 2 1 (by decide)
      (Fin.last 15).isLt position.isLt)

private theorem quotient_free_ne_blockOne
    (free : Fin 5) (position : Fin 15) :
    freeVertex free ≠ physicalBlockOneVertex position := by
  intro h
  have hval := congrArg Fin.val h
  simp [freeVertex, physicalBlockOneVertex, tailVertex] at hval
  omega

private theorem quotient_free_ne_blockZero
    (free : Fin 5) (position : Fin 15) :
    freeVertex free ≠ physicalBlockZeroVertex position := by
  intro h
  have hval := congrArg Fin.val h
  simp [freeVertex, physicalBlockZeroVertex, tailVertex] at hval
  omega

private theorem quotient_blockOne_ne_blockZero
    (large small : Fin 15) :
    physicalBlockOneVertex large ≠ physicalBlockZeroVertex small := by
  exact tailVertex_injective.ne
    (blockVertex_ne_of_block_ne 1 0 (by decide) large.isLt small.isLt)

private theorem quotient_satisfies_guarded_support_selected
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (selector : Nat) (target : TotalVertex)
    (hne : selectedVertex ≠ target) (member : Bool)
    (htruth :
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        selectedVertex target = (3 : Fin 4)) ↔ member = true) :
    (quotientFinalValuation selected branch).satisfies
      [Sat.Literal.neg selector,
       ContinuationDegreeNineTwistedRoot1CaseCNF61.supportLiteral
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)) member] := by
  cases hmember : member
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.neg
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)))
    · simpa [ContinuationDegreeNineTwistedRoot1CaseCNF61.supportLiteral,
        hmember] using
        (List.Mem.tail (Sat.Literal.neg selector)
          (List.Mem.head ([] : List Sat.Literal)))
    · change ¬quotientFinalValuation selected branch
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4))
      rw [quotientFinalValuation_ordinaryEdgeAtom selected branch
        selectedVertex target hne (3 : Fin 4)]
      intro hcolor
      have := htruth.mp hcolor
      simp [hmember] at this
  · apply satisfies_of_mem_holds
      (l := Sat.Literal.pos
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4)))
    · simpa [ContinuationDegreeNineTwistedRoot1CaseCNF61.supportLiteral,
        hmember] using
        (List.Mem.tail (Sat.Literal.neg selector)
          (List.Mem.head ([] : List Sat.Literal)))
    · change quotientFinalValuation selected branch
        (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
          selectedVertex target (3 : Fin 4))
      rw [quotientFinalValuation_ordinaryEdgeAtom selected branch
        selectedVertex target hne (3 : Fin 4)]
      exact htruth.mpr (by simp [hmember])

private theorem quotient_satisfies_guarded_edge_selected
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (selector : Nat) (left right : TotalVertex) (hne : left ≠ right)
    (q : ThreeColor)
    (hedge :
      totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension
        left right = decodedNormalHostColor q) :
    (quotientFinalValuation selected branch).satisfies
      (quotientGuardedEdgeClause selector left right q) := by
  apply satisfies_of_mem_holds
    (l := Sat.Literal.pos
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right
        (decodedNormalHostColor q)))
  · exact List.Mem.tail _ (List.Mem.head _)
  · change quotientFinalValuation selected branch
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right
        (decodedNormalHostColor q))
    rw [quotientFinalValuation_ordinaryEdgeAtom selected branch
      left right hne (decodedNormalHostColor q)]
    exact hedge

private theorem satisfies_fmla_append {valuation : Sat.Valuation}
    {first second : Sat.Fmla}
    (hfirst : valuation.satisfies_fmla first)
    (hsecond : valuation.satisfies_fmla second) :
    valuation.satisfies_fmla (first ++ second) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · exact hfirst.prop clause hclause
  · exact hsecond.prop clause hclause

/-! ## Structure representatives agree with the executable formula data -/

theorem quotientRepresentativeLarge_support (representative : Fin 132) :
    (quotientRepresentativeLarge representative).support =
      quotientLargeSupport representative := by
  rfl

theorem quotientRepresentativeSmall_support (representative : Fin 132) :
    (quotientRepresentativeSmall representative).support =
      quotientSmallSupport representative := by
  rfl

theorem quotientRepresentativeLarge_physical
    (representative : Fin 132) (position : Fin 5) :
    (quotientRepresentativeLarge representative).physical position =
      quotientLargePhysical representative position := by
  unfold quotientRepresentativeLarge largePhysicalRepresentative
  rw [largeCatalogueChoice_physical]
  exact (quotientLargePhysicalTable_eq_catalogue
    (quotientRepresentativePair representative).1 position).symm

theorem quotientRepresentativeSmall_physical
    (representative : Fin 132) (position : Fin 4) :
    (quotientRepresentativeSmall representative).physical position =
      quotientSmallPhysical representative position := by
  unfold quotientRepresentativeSmall smallPhysicalRepresentative
  rw [smallCatalogueChoice_physical]
  exact (quotientSmallPhysicalTable_eq_catalogue
    (quotientRepresentativePair representative).2 position).symm

/-- Root-1 specific: the free representative carries the involution
`freeRepresentativeEquiv`, so both sides evaluate the label order at the
permuted position. -/
theorem quotientRepresentativeFree_label
    (representative : Fin 132) (position : Fin 5) :
    (quotientRepresentativeFree representative).label position =
      quotientFreeLabel representative position := by
  exact (explicitFreeLabelOrder_eq (freeRepresentativeEquiv position)).symm

theorem quotientRepresentativeLarge_label
    (representative : Fin 132) (position : Fin 5) :
    (quotientRepresentativeLarge representative).label position =
      quotientLargeLabel representative position := by
  exact (explicitLargeLabelOrder_eq position).symm

theorem quotientRepresentativeSmall_label
    (representative : Fin 132) (position : Fin 4) :
    (quotientRepresentativeSmall representative).label position =
      quotientSmallLabel representative position := by
  exact (explicitSmallLabelOrder_eq position).symm

/-! ## Satisfaction of the selected representative -/

theorem quotientFinalValuation_satisfies_selectedLargeSupport
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientLargeSupportClauses selected) := by
  constructor
  intro clause hclause
  obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hclause
  apply quotient_satisfies_guarded_support_selected selected branch
    (quotientSelectorAtom selected)
    (physicalBlockOneVertex position)
    (quotient_selected_ne_blockOne position)
  simpa [quotientRepresentativeLarge_support] using
    realization.largeSupport position

theorem quotientFinalValuation_satisfies_selectedSmallSupport
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientSmallSupportClauses selected) := by
  constructor
  intro clause hclause
  obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hclause
  apply quotient_satisfies_guarded_support_selected selected branch
    (quotientSelectorAtom selected)
    (physicalBlockZeroVertex position)
    (quotient_selected_ne_blockZero position)
  simpa [quotientRepresentativeSmall_support] using
    realization.smallSupport position

theorem quotientFinalValuation_satisfies_selectedFreeLarge
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientFreeLargeClauses selected) := by
  constructor
  intro clause hclause
  obtain ⟨freeIndex, _hfreeIndex, hlargeIndexClause⟩ :=
    List.mem_flatMap.mp hclause
  obtain ⟨largeIndex, _hlargeIndex, rfl⟩ :=
    List.mem_map.mp hlargeIndexClause
  apply quotient_satisfies_guarded_edge_selected selected branch
    (quotientSelectorAtom selected)
    (freeVertex freeIndex)
    (physicalBlockOneVertex
      (quotientLargePhysical selected largeIndex))
    (quotient_free_ne_blockOne freeIndex _) _
  simpa [quotientRepresentativeFree_label,
    quotientRepresentativeLarge_label,
    quotientRepresentativeLarge_physical] using
      realization.freeLarge freeIndex largeIndex

theorem quotientFinalValuation_satisfies_selectedFreeSmall
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientFreeSmallClauses selected) := by
  constructor
  intro clause hclause
  obtain ⟨freeIndex, _hfreeIndex, hsmallIndexClause⟩ :=
    List.mem_flatMap.mp hclause
  obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
    List.mem_map.mp hsmallIndexClause
  apply quotient_satisfies_guarded_edge_selected selected branch
    (quotientSelectorAtom selected)
    (freeVertex freeIndex)
    (physicalBlockZeroVertex
      (quotientSmallPhysical selected smallIndex))
    (quotient_free_ne_blockZero freeIndex _) _
  simpa [quotientRepresentativeFree_label,
    quotientRepresentativeSmall_label,
    quotientRepresentativeSmall_physical] using
      realization.freeSmall freeIndex smallIndex

theorem quotientFinalValuation_satisfies_selectedLargeSmall
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientLargeSmallClauses selected) := by
  constructor
  intro clause hclause
  obtain ⟨largeIndex, _hlargeIndex, hsmallIndexClause⟩ :=
    List.mem_flatMap.mp hclause
  obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
    List.mem_map.mp hsmallIndexClause
  apply quotient_satisfies_guarded_edge_selected selected branch
    (quotientSelectorAtom selected)
    (physicalBlockOneVertex
      (quotientLargePhysical selected largeIndex))
    (physicalBlockZeroVertex
      (quotientSmallPhysical selected smallIndex))
    (quotient_blockOne_ne_blockZero _ _) _
  simpa [quotientRepresentativeLarge_label,
    quotientRepresentativeSmall_label,
    quotientRepresentativeLarge_physical,
    quotientRepresentativeSmall_physical] using
      realization.largeSmall largeIndex smallIndex

theorem quotientFinalValuation_satisfies_selectedRepresentative
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientRepresentativeClauses selected) := by
  unfold quotientRepresentativeClauses
  have hlarge := quotientFinalValuation_satisfies_selectedLargeSupport
    selected branch realization
  have hsmall := quotientFinalValuation_satisfies_selectedSmallSupport
    selected branch realization
  have hfreeLarge := quotientFinalValuation_satisfies_selectedFreeLarge
    selected branch realization
  have hfreeSmall := quotientFinalValuation_satisfies_selectedFreeSmall
    selected branch realization
  have hlargeSmall := quotientFinalValuation_satisfies_selectedLargeSmall
    selected branch realization
  exact satisfies_fmla_append
    (satisfies_fmla_append
      (satisfies_fmla_append
        (satisfies_fmla_append hlarge hsmall)
        hfreeLarge)
    hfreeSmall)
    hlargeSmall

/-- The selected representative also satisfies the 95 unguarded payload
units.  The proof uses both ingredients required for sound unguarding:
the exact guard-head equation and truth of the selected selector. -/
theorem quotientFinalValuation_satisfies_selectedRepresentativeUnits
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientRepresentativeUnitClauses selected) := by
  constructor
  intro unit hunit
  have hguardedMem :
      Sat.Literal.neg (quotientSelectorAtom selected) :: unit ∈
        quotientRepresentativeClauses selected := by
    rw [quotientRepresentativeClauses_eq_guarded_units]
    exact List.mem_map.mpr ⟨unit, hunit, rfl⟩
  have hguarded :=
    (quotientFinalValuation_satisfies_selectedRepresentative
      selected branch realization).prop _ hguardedMem
  apply hguarded
  change quotientExtendedValuation selected (finalValuation branch)
    (quotientSelectorAtom selected)
  exact (quotientExtendedValuation_selectorAtom
    selected selected (finalValuation branch)).2 rfl

/-! ## Every unselected representative is disabled by its selector -/

theorem quotientSelector_mem_representativeClause
    (representative : Fin 132) (clause : Sat.Clause)
    (hclause : clause ∈ quotientRepresentativeClauses representative) :
    List.Mem (Sat.Literal.neg (quotientSelectorAtom representative))
      clause := by
  unfold quotientRepresentativeClauses at hclause
  rcases List.mem_append.mp hclause with hthroughFreeSmall | hlargeSmall
  · rcases List.mem_append.mp hthroughFreeSmall with
      hthroughFreeLarge | hfreeSmall
    · rcases List.mem_append.mp hthroughFreeLarge with
        hthroughSmall | hfreeLarge
      · rcases List.mem_append.mp hthroughSmall with hlarge | hsmall
        · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hlarge
          exact List.Mem.head _
        · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hsmall
          exact List.Mem.head _
      · obtain ⟨freeIndex, _hfreeIndex, hlargeIndexClause⟩ :=
          List.mem_flatMap.mp hfreeLarge
        obtain ⟨largeIndex, _hlargeIndex, rfl⟩ :=
          List.mem_map.mp hlargeIndexClause
        exact List.Mem.head _
    · obtain ⟨freeIndex, _hfreeIndex, hsmallIndexClause⟩ :=
        List.mem_flatMap.mp hfreeSmall
      obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
        List.mem_map.mp hsmallIndexClause
      exact List.Mem.head _
  · obtain ⟨largeIndex, _hlargeIndex, hsmallIndexClause⟩ :=
      List.mem_flatMap.mp hlargeSmall
    obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
      List.mem_map.mp hsmallIndexClause
    exact List.Mem.head _

theorem quotientFinalValuation_satisfies_atLeastOne
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15)) :
    (quotientFinalValuation selected branch).satisfies
      quotientAtLeastOneClause := by
  apply satisfies_of_mem_holds
    (l := Sat.Literal.pos (quotientSelectorAtom selected))
  · exact List.mem_map.mpr ⟨selected, by simp, rfl⟩
  · change quotientExtendedValuation selected (finalValuation branch)
      (quotientSelectorAtom selected)
    exact (quotientExtendedValuation_selectorAtom
      selected selected (finalValuation branch)).2 rfl

theorem quotientFinalValuation_satisfies_selectorFmla
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      quotientSelectorFmla := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hatLeast | hrepresentative
  · simp only [List.mem_singleton] at hatLeast
    subst clause
    exact quotientFinalValuation_satisfies_atLeastOne selected branch
  · obtain ⟨assignment, _hassignment, hassignmentClause⟩ :=
      List.mem_flatMap.mp hrepresentative
    by_cases hselected : assignment = selected
    · subst assignment
      exact (quotientFinalValuation_satisfies_selectedRepresentative
        selected branch realization).prop clause hassignmentClause
    · apply satisfies_of_mem_holds
        (l := Sat.Literal.neg (quotientSelectorAtom assignment))
      · exact quotientSelector_mem_representativeClause
          assignment clause hassignmentClause
      · change ¬quotientExtendedValuation selected (finalValuation branch)
          (quotientSelectorAtom assignment)
        rw [quotientExtendedValuation_selectorAtom]
        exact hselected

theorem factorAssignmentRealization_satisfies_quotientFmla
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      quotientFmla := by
  exact satisfies_fmla_append
    (quotientExtendedValuation_satisfies_strongFmla selected branch)
    (quotientFinalValuation_satisfies_selectorFmla
      selected branch realization)

/-! ## Independent leaf-certificate interface

This is the reusable endpoint for per-representative LRAT certificates.  It
does not assume that any such certificate exists; it states exactly what a
complete family of 132 checked leaves would prove.
-/

theorem factorAssignmentRealization_satisfies_quotientLeafFmla
    (selected : Fin 132)
    (branch : CanonicalBranch .uuu 2 (Fin.last 15))
    (realization : FactorAssignmentRealization branch
      (quotientRepresentativeFree selected)
      (quotientRepresentativeLarge selected)
      (quotientRepresentativeSmall selected)) :
    (quotientFinalValuation selected branch).satisfies_fmla
      (quotientLeafFmla selected) := by
  exact satisfies_fmla_append
    (quotientExtendedValuation_satisfies_strongFmla selected branch)
    (quotientFinalValuation_satisfies_selectedRepresentativeUnits
      selected branch realization)

/-- Exact proposition to be discharged by a checked LRAT certificate for one
authoritative base-plus-95-units leaf. -/
def QuotientLeafLRATRefutation (representative : Fin 132) : Prop :=
  (quotientLeafFmla representative).proof Sat.Clause.nil

/-- Generic split-core formula for a trimmed leaf certificate.  Base and unit
indices are encoded independently as gaps, so certificate modules never have
to reduce the unused tail of the 343,368-clause base. -/
def quotientLeafCoreFmla (representative : Fin 132)
    (baseGaps unitGaps : List Nat) : Sat.Fmla :=
  ClauseCore.selectGaps strongBase baseGaps ++
    ClauseCore.selectGaps
      (quotientRepresentativeUnitClauses representative) unitGaps

/-- Any model of a full leaf models every independently selected split core. -/
theorem satisfies_quotientLeafCoreFmla
    (representative : Fin 132) (baseGaps unitGaps : List Nat)
    (valuation : Sat.Valuation)
    (hvaluation : valuation.satisfies_fmla
      (quotientLeafFmla representative)) :
    valuation.satisfies_fmla
      (quotientLeafCoreFmla representative baseGaps unitGaps) := by
  have hbase : valuation.satisfies_fmla strongBase := by
    constructor
    intro clause hclause
    exact hvaluation.prop clause
      (List.mem_append.mpr (Or.inl hclause))
  have hunits : valuation.satisfies_fmla
      (quotientRepresentativeUnitClauses representative) := by
    constructor
    intro clause hclause
    exact hvaluation.prop clause
      (List.mem_append.mpr (Or.inr hclause))
  exact ClauseCore.satisfies_append valuation _ _
    (ClauseCore.satisfies_selectGaps valuation strongBase baseGaps hbase)
    (ClauseCore.satisfies_selectGaps valuation
      (quotientRepresentativeUnitClauses representative) unitGaps hunits)

/-- Conditional semantic closure: a checked refutation for each of the 132
explicit leaves fills the existing twisted root-1 degree-nine obstruction
slot. -/
theorem twistedRoot1CaseObstruction_of_quotient_leaf_lrats
    (hunsat : ∀ representative : Fin 132,
      QuotientLeafLRATRefutation representative) :
    DegreeNineCaseObstruction twistedRoot1Case := by
  intro realization
  obtain ⟨representative, normalized, hnormalized⟩ :=
    twistedRoot1Realization_reduces_to_132 realization
  apply hunsat representative
    (quotientFinalValuation representative normalized)
  apply factorAssignmentRealization_satisfies_quotientLeafFmla
    representative normalized
  simpa [quotientRepresentativeFree, quotientRepresentativeLarge,
    quotientRepresentativeSmall] using hnormalized

/-! ## The single remaining certificate obligation -/

theorem twistedRoot1Realization_yields_satisfying_quotientFmla
    (realization : TwistedRoot1Realization) :
    ∃ valuation : Sat.Valuation,
      valuation.satisfies_fmla quotientFmla := by
  obtain ⟨representative, normalized, hnormalized⟩ :=
    twistedRoot1Realization_reduces_to_132 realization
  refine ⟨quotientFinalValuation representative normalized, ?_⟩
  apply factorAssignmentRealization_satisfies_quotientFmla
    representative normalized
  simpa [quotientRepresentativeFree, quotientRepresentativeLarge,
    quotientRepresentativeSmall] using hnormalized

/-- Exact proposition to be discharged by replaying one LRAT certificate for
the explicit 132-selector quotient formula. -/
def QuotientLRATRefutation : Prop :=
  quotientFmla.proof Sat.Clause.nil

theorem noStrongRealization_of_quotient_lrat
    (hunsat : QuotientLRATRefutation) :
    ¬Nonempty TwistedRoot1Realization := by
  rintro ⟨realization⟩
  obtain ⟨valuation, hsatisfies⟩ :=
    twistedRoot1Realization_yields_satisfying_quotientFmla realization
  exact hunsat valuation hsatisfies

/-- The quotient certificate fills the existing semantic obstruction slot for
the twisted root-1 degree-nine label. -/
theorem twistedRoot1CaseObstruction_of_quotient_lrat
    (hunsat : QuotientLRATRefutation) :
    DegreeNineCaseObstruction twistedRoot1Case := by
  intro realization
  exact noStrongRealization_of_quotient_lrat hunsat ⟨realization⟩

#print axioms quotientExtendedValuation_selectorAtom
#print axioms quotientExtendedValuation_satisfies_strongFmla
#print axioms quotientSelector_mem_representativeClause
#print axioms quotientFinalValuation_satisfies_selectedRepresentative
#print axioms quotientFinalValuation_satisfies_selectedRepresentativeUnits
#print axioms factorAssignmentRealization_satisfies_quotientFmla
#print axioms factorAssignmentRealization_satisfies_quotientLeafFmla
#print axioms satisfies_quotientLeafCoreFmla
#print axioms twistedRoot1CaseObstruction_of_quotient_leaf_lrats
#print axioms twistedRoot1Realization_yields_satisfying_quotientFmla
#print axioms noStrongRealization_of_quotient_lrat
#print axioms twistedRoot1CaseObstruction_of_quotient_lrat

end ContinuationDegreeNineTwistedRoot1QuotientSemantic61
end R4333
