import PricingG.UUTD9Root1Orbit

/-! Continuation-authored (locks/duuu), 2026-08-05.
Twisted case (slot 3, root 1) quotient-formula clone of
ProfileDUUUDegreeNineQuotientFormula61.  Root 1 has a TRIVIAL root
stabilizer, so there is no diagonal halving: the selector count is the full
`11 x 12 = 132` product (`1 + 132 * 95 = 12541` suffix clauses, matching
twisted_root1_quotient.cnf).  The pre-reduced physical tables are
regenerated from the root-1 catalogue data; the three label-side
k15Template sites flip false -> true (the binders feed
explicit{Free,Large,Small}LabelOrder, i.e. label-set vertices); the
physical-side machinery is identical to strongCase.  The explicit label
orders come from the FactorOrbitCoverage module (inlined there because
root 1 has no RootStabilizer module). -/

/-!
# Exact 132-representative quotient formula for the twisted root-1 case

This file contains only formula and index data.  The semantic reason that the
132 representatives are complete lives in
`UUTD9Root1Orbit`; satisfaction and
the final LRAT interface live in the companion semantic module.

For each representative, one fresh selector guards exactly 95 facts:

* 15 large-support literals;
* 15 small-support literals;
* 25 free--large edge colors;
* 20 free--small edge colors;
* 20 large--small edge colors.

Together with one at-least-one clause, the quotient suffix therefore has
`1 + 132 * 95 = 12541` clauses.
-/

namespace R4333
namespace UUTD9Root1Formula

open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open UUTD9Root1Case
open UUTD9Root1CNF
open UUTD9Root1Factor
open UUTD9Root1Physical
open UUTD9Root1Orbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex
abbrev TotalVertex := ProfileDHighOwnFiveSupportC5CNF.TotalVertex

/-! ## Exact representative data -/

/-- Raw labelled-catalogue indices behind the compact `11 x 12` quotient. -/
def quotientLargeCatalogueIndex (representative : Fin 132) : Fin 110 :=
  largeRepresentativeRawIndex
    (quotientRepresentativePair representative).1

def quotientSmallCatalogueIndex (representative : Fin 132) : Fin 120 :=
  smallRepresentativeRawIndex
    (quotientRepresentativePair representative).2

/-- Fully computable support and coordinate data used by the CNF. -/
def quotientLargeSupport (representative : Fin 132) : LargeFactorSupport :=
  indexedLargeSupport
    (largeCatalogueSupportIndex
      (quotientLargeCatalogueIndex representative))

def quotientSmallSupport (representative : Fin 132) : SmallFactorSupport :=
  indexedSmallSupport
    (smallCatalogueSupportIndex
      (quotientSmallCatalogueIndex representative))

/-- Pre-reduced physical-coordinate tables.  Keeping these literal makes the
authoritative formula fast to execute and serialize; the two equations below
kernel-check them against the catalogue definitions used by the orbit proof. -/
def quotientLargePhysicalTable : Fin 11 → Fin 5 → Fin 15 :=
  ![![0, 2, 13, 1, 10], ![1, 2, 10, 0, 13],
    ![1, 10, 2, 13, 0], ![2, 1, 0, 10, 13],
    ![2, 0, 1, 13, 10], ![0, 3, 11, 1, 12],
    ![0, 11, 3, 12, 1], ![1, 3, 12, 0, 11],
    ![1, 12, 3, 11, 0], ![12, 1, 11, 3, 0],
    ![1, 6, 10, 11, 9]]

def quotientSmallPhysicalTable : Fin 12 → Fin 4 → Fin 15 :=
  ![![0, 1, 2, 10], ![10, 2, 1, 0],
    ![1, 0, 2, 13], ![13, 2, 0, 1],
    ![1, 0, 3, 11], ![0, 1, 3, 12],
    ![12, 3, 1, 0], ![0, 12, 11, 1],
    ![1, 11, 12, 0], ![2, 3, 0, 8],
    ![2, 10, 1, 13], ![6, 10, 1, 9]]

def quotientLargePhysical (representative : Fin 132)
    (position : Fin 5) : Fin 15 :=
  quotientLargePhysicalTable
    (quotientRepresentativePair representative).1 position

def quotientSmallPhysical (representative : Fin 132)
    (position : Fin 4) : Fin 15 :=
  quotientSmallPhysicalTable
    (quotientRepresentativePair representative).2 position

theorem quotientLargePhysicalTable_eq_catalogue :
    ∀ index : Fin 11, ∀ position : Fin 5,
      quotientLargePhysicalTable index position =
        largeCataloguePhysical (largeRepresentativeRawIndex index)
          position := by
  decide

theorem quotientSmallPhysicalTable_eq_catalogue :
    ∀ index : Fin 12, ∀ position : Fin 4,
      quotientSmallPhysicalTable index position =
        smallCataloguePhysical (smallRepresentativeRawIndex index)
          position := by
  decide

/-- Root 1 is the one case whose free representative permutation is NOT the
identity: the identity free permutation is incompatible with the twisted
root-1 template, and `freePhysicalRepresentative` carries the involution
`freeRepresentativeEquiv = ![0, 2, 1, 4, 3]`.  The label attached at free
position `i` is therefore `explicitFreeLabelOrder (involution i)`
(= `![0, 11, 9, 14, 13]`), exactly matching the exported
`twisted_root1_quotient.cnf` whose leaf colors were generated from free
choice 0 (the first Lean-order compatible permutation). -/
def quotientFreeLabel (_representative : Fin 132)
    (position : Fin 5) : Fin 15 :=
  explicitFreeLabelOrder (freeRepresentativeEquiv position)

def quotientLargeLabel (_representative : Fin 132)
    (position : Fin 5) : Fin 15 :=
  explicitLargeLabelOrder position

def quotientSmallLabel (_representative : Fin 132)
    (position : Fin 4) : Fin 15 :=
  explicitSmallLabelOrder position

/-! These structure-valued representatives are used only by the semantic
bridge.  The formula below depends exclusively on the computable data above. -/

def quotientRepresentativeFree (_representative : Fin 132) :
    FreeFactorChoice :=
  freePhysicalRepresentative

noncomputable def quotientRepresentativeLarge (representative : Fin 132) :
    LargeFactorChoice :=
  largePhysicalRepresentative
    (quotientRepresentativePair representative).1

noncomputable def quotientRepresentativeSmall (representative : Fin 132) :
    SmallFactorChoice :=
  smallPhysicalRepresentative
    (quotientRepresentativePair representative).2

/-! ## One direct selector namespace -/

/-- The selector at index `representative`.  The payload is direct: unlike
the older factor formula, there is no nested category/index pair. -/
def quotientSelectorAtom (representative : Fin 132) : Nat :=
  Nat.pair selectorNamespaceTag representative.val

def quotientAtLeastOneClause : Sat.Clause :=
  (List.finRange 132).map fun representative : Fin 132 =>
    Sat.Literal.pos (quotientSelectorAtom representative)

/-! ## One-selector guarded representative facts -/

def quotientGuardedEdgeClause (selector : Nat)
    (left right : TotalVertex) (q : ThreeColor) : Sat.Clause :=
  [Sat.Literal.neg selector,
   Sat.Literal.pos
    (OutsideDegreeCapCNF.outsideIncidentEdgeAtom left right
      (decodedNormalHostColor q))]

def quotientLargeSupportClauses (representative : Fin 132) : Sat.Fmla :=
  (List.finRange 15).map fun position : Fin 15 =>
    [Sat.Literal.neg (quotientSelectorAtom representative),
     UUTD9Root1CNF.supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        selectedVertex (physicalBlockOneVertex position) (3 : Fin 4))
      (decide (position ∈ (quotientLargeSupport representative).1))]

def quotientSmallSupportClauses (representative : Fin 132) : Sat.Fmla :=
  (List.finRange 15).map fun position : Fin 15 =>
    [Sat.Literal.neg (quotientSelectorAtom representative),
     UUTD9Root1CNF.supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
        selectedVertex (physicalBlockZeroVertex position) (3 : Fin 4))
      (decide (position ∈ (quotientSmallSupport representative).1))]

def quotientFreeLargeClauses (representative : Fin 132) : Sat.Fmla :=
  (List.finRange 5).flatMap fun freeIndex : FiveVertex =>
    (List.finRange 5).map fun largeIndex : Fin 5 =>
      quotientGuardedEdgeClause (quotientSelectorAtom representative)
        (freeVertex freeIndex)
        (physicalBlockOneVertex
          (quotientLargePhysical representative largeIndex))
        (k15Template true
          (quotientFreeLabel representative freeIndex)
          (quotientLargeLabel representative largeIndex))

def quotientFreeSmallClauses (representative : Fin 132) : Sat.Fmla :=
  (List.finRange 5).flatMap fun freeIndex : FiveVertex =>
    (List.finRange 4).map fun smallIndex : Fin 4 =>
      quotientGuardedEdgeClause (quotientSelectorAtom representative)
        (freeVertex freeIndex)
        (physicalBlockZeroVertex
          (quotientSmallPhysical representative smallIndex))
        (k15Template true
          (quotientFreeLabel representative freeIndex)
          (quotientSmallLabel representative smallIndex))

def quotientLargeSmallClauses (representative : Fin 132) : Sat.Fmla :=
  (List.finRange 5).flatMap fun largeIndex : Fin 5 =>
    (List.finRange 4).map fun smallIndex : Fin 4 =>
      quotientGuardedEdgeClause (quotientSelectorAtom representative)
        (physicalBlockOneVertex
          (quotientLargePhysical representative largeIndex))
        (physicalBlockZeroVertex
          (quotientSmallPhysical representative smallIndex))
        (k15Template true
          (quotientLargeLabel representative largeIndex)
          (quotientSmallLabel representative smallIndex))

def quotientRepresentativeClauses
    (representative : Fin 132) : Sat.Fmla :=
  quotientLargeSupportClauses representative ++
    quotientSmallSupportClauses representative ++
    quotientFreeLargeClauses representative ++
    quotientFreeSmallClauses representative ++
    quotientLargeSmallClauses representative

/-! ## Per-representative unguarded leaf formulas

The discovery quotient guards every representative fact by one selector.
For proof production it is substantially cheaper to split the quotient into
132 independent leaves.  The following definitions do that inside Lean: the
base is the exact UUU block-2/position-15 formula required by the twisted
root-1 case, and each leaf appends the 95 payload units obtained by removing
the selector head from that representative's guarded clauses.
-/

/-- The authoritative base formula for the twisted root-1 case (physically
identical to the strongCase base). -/
abbrev strongBase : Sat.Fmla :=
  ProfileDHighOwnFiveSupportC5Formula.fmla .uut 2 (Fin.last 15)

/-- The 95 unguarded facts belonging to one quotient representative. -/
def quotientRepresentativeUnitClauses
    (representative : Fin 132) : Sat.Fmla :=
  (quotientRepresentativeClauses representative).map
    (fun clause : Sat.Clause => clause.tail)

/-- One independent proof leaf: the authoritative base plus 95 units. -/
def quotientLeafFmla (representative : Fin 132) : Sat.Fmla :=
  strongBase ++ quotientRepresentativeUnitClauses representative

/-- Every representative clause has the selected guard as its literal head.
This stronger ordered statement is what licenses taking `List.tail`. -/
theorem quotientRepresentativeClause_eq_guarded_tail
    (representative : Fin 132) (clause : Sat.Clause)
    (hclause : clause ∈ quotientRepresentativeClauses representative) :
    clause = Sat.Literal.neg (quotientSelectorAtom representative) ::
      clause.tail := by
  unfold quotientRepresentativeClauses at hclause
  rcases List.mem_append.mp hclause with hthroughFreeSmall | hlargeSmall
  · rcases List.mem_append.mp hthroughFreeSmall with
      hthroughFreeLarge | hfreeSmall
    · rcases List.mem_append.mp hthroughFreeLarge with
        hthroughSmall | hfreeLarge
      · rcases List.mem_append.mp hthroughSmall with hlarge | hsmall
        · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hlarge
          rfl
        · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hsmall
          rfl
      · obtain ⟨freeIndex, _hfreeIndex, hlargeIndexClause⟩ :=
          List.mem_flatMap.mp hfreeLarge
        obtain ⟨largeIndex, _hlargeIndex, rfl⟩ :=
          List.mem_map.mp hlargeIndexClause
        rfl
    · obtain ⟨freeIndex, _hfreeIndex, hsmallIndexClause⟩ :=
        List.mem_flatMap.mp hfreeSmall
      obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
        List.mem_map.mp hsmallIndexClause
      rfl
  · obtain ⟨largeIndex, _hlargeIndex, hsmallIndexClause⟩ :=
      List.mem_flatMap.mp hlargeSmall
    obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
      List.mem_map.mp hsmallIndexClause
    rfl

/-- Every guard removal above is justified by exact head equality, not merely
by the selector occurring somewhere in the clause. -/
theorem quotientRepresentativeClauses_eq_guarded_units
    (representative : Fin 132) :
    quotientRepresentativeClauses representative =
      (quotientRepresentativeUnitClauses representative).map
        (fun unit : Sat.Clause =>
          Sat.Literal.neg (quotientSelectorAtom representative) :: unit) := by
  have map_guard_tail_eq_self : ∀ formula : Sat.Fmla,
      (∀ clause ∈ formula,
        clause = Sat.Literal.neg (quotientSelectorAtom representative) ::
          clause.tail) →
      formula = formula.map (fun clause : Sat.Clause =>
        Sat.Literal.neg (quotientSelectorAtom representative) ::
          clause.tail) := by
    intro formula hshape
    induction formula with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons]
        rw [hshape head (List.Mem.head tail)]
        congr 1
        exact ih (fun clause hclause =>
          hshape clause (List.Mem.tail head hclause))
  unfold quotientRepresentativeUnitClauses
  rw [List.map_map]
  exact map_guard_tail_eq_self _
    (quotientRepresentativeClause_eq_guarded_tail representative)

def quotientSelectorFmla : Sat.Fmla :=
  [quotientAtLeastOneClause] ++
    (List.finRange 132).flatMap quotientRepresentativeClauses

def quotientFmla : Sat.Fmla :=
  strongBase ++ quotientSelectorFmla

/-! ## Formula-shape checks -/

theorem quotientFreeLargeClauses_length (representative : Fin 132) :
    (quotientFreeLargeClauses representative).length = 25 := by
  simp [quotientFreeLargeClauses]

theorem quotientFreeSmallClauses_length (representative : Fin 132) :
    (quotientFreeSmallClauses representative).length = 20 := by
  simp [quotientFreeSmallClauses]

theorem quotientLargeSmallClauses_length (representative : Fin 132) :
    (quotientLargeSmallClauses representative).length = 20 := by
  simp [quotientLargeSmallClauses]

theorem quotientRepresentativeClauses_length (representative : Fin 132) :
    (quotientRepresentativeClauses representative).length = 95 := by
  simp [quotientRepresentativeClauses,
    quotientLargeSupportClauses,
    quotientSmallSupportClauses,
    quotientFreeLargeClauses_length,
    quotientFreeSmallClauses_length,
    quotientLargeSmallClauses_length]

theorem quotientRepresentativeUnitClauses_length
    (representative : Fin 132) :
    (quotientRepresentativeUnitClauses representative).length = 95 := by
  simp [quotientRepresentativeUnitClauses,
    quotientRepresentativeClauses_length]

/-- Every unguarded payload is a genuine unit clause. -/
theorem quotientRepresentativeUnitClauses_are_units
    (representative : Fin 132) :
    ∀ unit ∈ quotientRepresentativeUnitClauses representative,
      unit.length = 1 := by
  intro unit hunit
  obtain ⟨clause, hclause, rfl⟩ := List.mem_map.mp hunit
  unfold quotientRepresentativeClauses at hclause
  rcases List.mem_append.mp hclause with hthroughFreeSmall | hlargeSmall
  · rcases List.mem_append.mp hthroughFreeSmall with
      hthroughFreeLarge | hfreeSmall
    · rcases List.mem_append.mp hthroughFreeLarge with
        hthroughSmall | hfreeLarge
      · rcases List.mem_append.mp hthroughSmall with hlarge | hsmall
        · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hlarge
          simp
        · obtain ⟨position, _hposition, rfl⟩ := List.mem_map.mp hsmall
          simp
      · obtain ⟨freeIndex, _hfreeIndex, hlargeIndexClause⟩ :=
          List.mem_flatMap.mp hfreeLarge
        obtain ⟨largeIndex, _hlargeIndex, rfl⟩ :=
          List.mem_map.mp hlargeIndexClause
        simp [quotientGuardedEdgeClause]
    · obtain ⟨freeIndex, _hfreeIndex, hsmallIndexClause⟩ :=
        List.mem_flatMap.mp hfreeSmall
      obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
        List.mem_map.mp hsmallIndexClause
      simp [quotientGuardedEdgeClause]
  · obtain ⟨largeIndex, _hlargeIndex, hsmallIndexClause⟩ :=
      List.mem_flatMap.mp hlargeSmall
    obtain ⟨smallIndex, _hsmallIndex, rfl⟩ :=
      List.mem_map.mp hsmallIndexClause
    simp [quotientGuardedEdgeClause]

theorem quotientSelectorFmla_length :
    quotientSelectorFmla.length = 12541 := by
  simp [quotientSelectorFmla, List.length_flatMap,
    quotientRepresentativeClauses_length]

#print axioms quotientRepresentativeClauses_length
#print axioms quotientRepresentativeClause_eq_guarded_tail
#print axioms quotientRepresentativeClauses_eq_guarded_units
#print axioms quotientRepresentativeUnitClauses_length
#print axioms quotientRepresentativeUnitClauses_are_units
#print axioms quotientSelectorFmla_length

end UUTD9Root1Formula
end R4333
