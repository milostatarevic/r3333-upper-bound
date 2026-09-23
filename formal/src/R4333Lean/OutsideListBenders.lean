import R4333Lean.Basic

/-!
# The semantic outside-list Benders cut

Suppose some host vertices have already been exposed and the remaining
vertices form an outside set.  If one exposed centre sends the same colour
`q` to two distinct outside vertices, their mutual outside edge cannot also
have colour `q`: that would close a monochromatic triangle.

An inner list-colouring search may assume finitely many such pair/colour
choices are forbidden.  If its UNSAT core says that no triangle-free
colouring of the outside complete graph avoids all those choices, then a
global completion cannot realize every assumed collision.  At least one
core pair/colour must be available.  This is exactly the sound outer
disjunction used by list-colouring Benders/CEGAR; no SAT checker or computed
core is trusted in this file.
-/

namespace R4333

/-! ## Exposed incidences and their semantic collision -/

/-- The exposed-to-outside incidence table.  It records only cross-edge
colours; no graph structure or triangle-freeness is built into the type. -/
abbrev ExposedIncidence (E O C : Type*) := E → O → C

/-- A pair/colour choice collides when one exposed centre sees both outside
endpoints in that colour. -/
def ExposedIncidenceCollision
    {E O C : Type*} (incidence : ExposedIncidence E O C)
    (x y : O) (q : C) : Prop :=
  ∃ center : E, incidence center x = q ∧ incidence center y = q

/-- The corresponding pair/colour choice is available precisely when no
exposed centre creates the collision. -/
def ExposedPairColorAvailable
    {E O C : Type*} (incidence : ExposedIncidence E O C)
    (x y : O) (q : C) : Prop :=
  ¬ExposedIncidenceCollision incidence x y q

theorem exposedIncidenceCollision_symm
    {E O C : Type*} (incidence : ExposedIncidence E O C)
    (x y : O) (q : C) :
    ExposedIncidenceCollision incidence x y q ↔
      ExposedIncidenceCollision incidence y x q := by
  constructor <;> rintro ⟨center, hx, hy⟩
  · exact ⟨center, hy, hx⟩
  · exact ⟨center, hy, hx⟩

/-- Cross-edge incidences extracted from a host colouring and two embedded
vertex sets. -/
def coloringExposedIncidence
    {V E O C : Type*} (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : O ↪ V) : ExposedIncidence E O C :=
  fun center x ↦ c (exposed center) (outside x)

/-- The exposed and outside embeddings have disjoint images. -/
def ExposedOutsideDisjoint
    {V E O : Type*} (exposed : E ↪ V) (outside : O ↪ V) : Prop :=
  ∀ center x, exposed center ≠ outside x

/-! ## Restricting a global colouring to the outside set -/

/-- Pull a host colouring back along an outside embedding. -/
def outsideInducedColoring
    {V O C : Type*} (c : EdgeColoring V C) (outside : O ↪ V) :
    EdgeColoring O C where
  color x y := c (outside x) (outside y)
  color_symm x y := c.color_symm (outside x) (outside y)

@[simp] theorem outsideInducedColoring_apply
    {V O C : Type*} (c : EdgeColoring V C) (outside : O ↪ V)
    (x y : O) :
    outsideInducedColoring c outside x y = c (outside x) (outside y) :=
  rfl

/-- Triangle-freeness is inherited by every embedded outside set. -/
theorem noMono_outsideInducedColoring
    {V O C : Type*} (c : EdgeColoring V C) (outside : O ↪ V)
    (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (outsideInducedColoring c outside) := by
  intro x y z hdistinct hmono
  apply hc (outside x) (outside y) (outside z)
  · exact ⟨outside.injective.ne hdistinct.1,
      outside.injective.ne hdistinct.2.1,
      outside.injective.ne hdistinct.2.2⟩
  · exact hmono

/-- The basic semantic list restriction: an actual outside edge cannot use
a colour that collides at an exposed centre. -/
theorem outside_edge_ne_of_exposedIncidenceCollision
    {V E O C : Type*} (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : O ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    {x y : O} (hxy : x ≠ y) {q : C}
    (hcollision : ExposedIncidenceCollision
      (coloringExposedIncidence c exposed outside) x y q) :
    outsideInducedColoring c outside x y ≠ q := by
  obtain ⟨center, hcenterX, hcenterY⟩ := hcollision
  intro houtside
  apply hc (exposed center) (outside x) (outside y)
  · exact ⟨hdisjoint center x, hdisjoint center y,
      outside.injective.ne hxy⟩
  · exact ⟨hcenterX.trans hcenterY.symm,
      hcenterY.trans houtside.symm⟩

/-! ## Finite assumption cores -/

/-- One inner-solver assumption forbids one colour on one distinct outside
pair.  The endpoint order is harmless because every `EdgeColoring` is
symmetric. -/
structure OutsidePairColorRestriction (O C : Type*) where
  left : O
  right : O
  left_ne_right : left ≠ right
  color : C
  deriving DecidableEq

namespace OutsidePairColorRestriction

/-- This restriction is justified by the exposed incidence table. -/
def collides
    {E O C : Type*} (incidence : ExposedIncidence E O C)
    (restriction : OutsidePairColorRestriction O C) : Prop :=
  ExposedIncidenceCollision incidence restriction.left restriction.right
    restriction.color

/-- This restriction's pair/colour choice remains available to the outside
edge. -/
def available
    {E O C : Type*} (incidence : ExposedIncidence E O C)
    (restriction : OutsidePairColorRestriction O C) : Prop :=
  ExposedPairColorAvailable incidence restriction.left restriction.right
    restriction.color

theorem available_iff_not_collides
    {E O C : Type*} (incidence : ExposedIncidence E O C)
    (restriction : OutsidePairColorRestriction O C) :
    restriction.available incidence ↔ ¬restriction.collides incidence :=
  Iff.rfl

end OutsidePairColorRestriction

/-- An outside colouring avoids a core when it uses none of the core's
forbidden pair/colour choices. -/
def OutsideColoringAvoidsCore
    {O C : Type*} [DecidableEq O] [DecidableEq C]
    (d : EdgeColoring O C)
    (core : Finset (OutsidePairColorRestriction O C)) : Prop :=
  ∀ restriction ∈ core,
    d restriction.left restriction.right ≠ restriction.color

/-- Semantic UNSAT of the inner problem represented by a finite assumption
core: no triangle-free complete-graph colouring avoids every core choice. -/
def OutsideRestrictionCoreUnsatisfiable
    {O C : Type*} [DecidableEq O] [DecidableEq C]
    (core : Finset (OutsidePairColorRestriction O C)) : Prop :=
  ¬∃ d : EdgeColoring O C,
    NoMonochromaticTriangle d ∧ OutsideColoringAvoidsCore d core

/-- Equivalent positive reading of a semantic core: every triangle-free
outside colouring hits at least one restricted pair/colour. -/
theorem outsideRestrictionCoreUnsatisfiable_iff_hits
    {O C : Type*} [DecidableEq O] [DecidableEq C]
    (core : Finset (OutsidePairColorRestriction O C)) :
    OutsideRestrictionCoreUnsatisfiable core ↔
      ∀ d : EdgeColoring O C, NoMonochromaticTriangle d →
        ∃ restriction ∈ core,
          d restriction.left restriction.right = restriction.color := by
  classical
  constructor
  · intro hunsat d hd
    by_contra hhit
    apply hunsat
    refine ⟨d, hd, ?_⟩
    intro restriction hmem heq
    exact hhit ⟨restriction, hmem, heq⟩
  · intro hhits
    rintro ⟨d, hd, havoids⟩
    obtain ⟨restriction, hmem, heq⟩ := hhits d hd
    exact havoids restriction hmem heq

/-- The learned outer clause: at least one assumption-core pair/colour is
available, i.e. has no exposed-incidence collision. -/
def OutsideListBendersClause
    {E O C : Type*} [DecidableEq O] [DecidableEq C]
    (incidence : ExposedIncidence E O C)
    (core : Finset (OutsidePairColorRestriction O C)) : Prop :=
  ∃ restriction ∈ core, restriction.available incidence

/-- If every core restriction really collides in a global colouring, its
outside restriction is a triangle-free colouring avoiding the whole core. -/
theorem outsideInducedColoring_avoidsCore_of_all_collide
    {V E O C : Type*} [DecidableEq O] [DecidableEq C]
    (c : EdgeColoring V C) (exposed : E ↪ V) (outside : O ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (core : Finset (OutsidePairColorRestriction O C))
    (hall : ∀ restriction ∈ core,
      restriction.collides
        (coloringExposedIncidence c exposed outside)) :
    OutsideColoringAvoidsCore (outsideInducedColoring c outside) core := by
  intro restriction hmem
  exact outside_edge_ne_of_exposedIncidenceCollision
    c exposed outside hdisjoint hc restriction.left_ne_right
      (hall restriction hmem)

/-- Soundness of the list-colouring Benders cut.  An inner semantic UNSAT
core forces the outer disjunction that at least one core collision is absent
in every global no-monochromatic-triangle completion. -/
theorem outsideListBendersClause_of_coreUnsatisfiable
    {V E O C : Type*} [Fintype E] [Fintype O]
    [DecidableEq O] [DecidableEq C]
    (c : EdgeColoring V C) (exposed : E ↪ V) (outside : O ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (core : Finset (OutsidePairColorRestriction O C))
    (hcore : OutsideRestrictionCoreUnsatisfiable core) :
    OutsideListBendersClause
      (coloringExposedIncidence c exposed outside) core := by
  classical
  by_contra hclause
  apply hcore
  refine ⟨outsideInducedColoring c outside,
    noMono_outsideInducedColoring c outside hc, ?_⟩
  apply outsideInducedColoring_avoidsCore_of_all_collide
    c exposed outside hdisjoint hc core
  intro restriction hmem
  by_contra hcollision
  exact hclause ⟨restriction, hmem, hcollision⟩

#print axioms R4333.noMono_outsideInducedColoring
#print axioms R4333.outside_edge_ne_of_exposedIncidenceCollision
#print axioms R4333.outsideRestrictionCoreUnsatisfiable_iff_hits
#print axioms R4333.outsideInducedColoring_avoidsCore_of_all_collide
#print axioms R4333.outsideListBendersClause_of_coreUnsatisfiable

end R4333
