import R4333Lean.ProfileDUUUDegreeNineFiniteBoundary61

/-!
# Exact semantic case interface for the UUU degree-nine branch

The finite boundary has 32 labels, but a label is not a complete graph or
cross-edge assignment.  This module therefore indexes a *semantic
realization* by each label.  A realization retains the complete positioned
five-row extension, the exact degree-nine skeleton, and the orbit-reduced
full-neighbourhood normal form.  Its equality fields connect those semantic
objects to every component of the finite case label.

Consequently, a proof attached to one case must refute every full semantic
realization of that case; it cannot refute only the small label tuple.  The
last section assembles 32 such per-case theorems into an obstruction of the
whole UUU exact-degree-nine five-support subbranch.
-/

namespace R4333
namespace ProfileDUUUDegreeNineCaseRealization61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDUUUFiveSupportPositionSymmetry
open ProfileDDegreeNineFullNeighborhoodNormalForm61
open ProfileDUUUDegreeNineFiniteBoundary61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SemanticFiveSupport :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension

abbrev PositionedFiveSupport :=
  ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport

abbrev ResidualCase := DegreeNineResidualLocalCase

abbrev caseSlot (case : ResidualCase) : Fin 4 := case.1
abbrev caseFirstLarge (case : ResidualCase) : Bool := case.2.1
abbrev caseTwisted (case : ResidualCase) : Bool := case.2.2.1
abbrev caseRoot (case : ResidualCase) : Fin 15 := case.2.2.2.1

theorem caseRoot_mem (case : ResidualCase) :
    caseRoot case ∈
      degreeNineRootRepresentativeSet (caseTwisted case)
        (residualDeficientColor (caseSlot case) (caseFirstLarge case)) :=
  case.2.2.2.2

/-! ## Full semantic realizations of finite labels -/

/-- A finite case label together with all semantic data that it represents.

In particular, `branch` retains the complete tail coloring, the five free
rows, and all cross edges.  The finite label only fixes the selected-position
orbit, physical `5+4` orientation, template bit, and root orbit. -/
structure DegreeNineCaseRealization (case : ResidualCase) : Type where
  branch : PositionedFiveSupport .uuu
    (uuuRepresentativeIndexBySlot (caseSlot case)).1
    (uuuRepresentativeIndexBySlot (caseSlot case)).2
  tailOwnDegreeNine :
    colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor
          (uuuRepresentativeIndexBySlot (caseSlot case)).1)
        (blockVertex
          (uuuRepresentativeIndexBySlot (caseSlot case)).1
          (uuuRepresentativeIndexBySlot (caseSlot case)).2.val) = 9
  skeleton : DegreeNineSkeleton branch.toSemantic
  caseFirstLarge_eq : caseFirstLarge case = skeleton.firstLarge
  normal : OrbitReducedDegreeNineFullNeighborhoodNormalForm
    branch.toSemantic skeleton
  caseTwisted_eq : caseTwisted case = normal.twisted
  caseRoot_eq : caseRoot case = normal.vertex.symm restoredRootLabel

theorem DegreeNineCaseRealization.smallDecodedColor_eq
    {case : ResidualCase} (realization : DegreeNineCaseRealization case) :
    smallDecodedColor realization.skeleton =
      residualDeficientColor (caseSlot case) (caseFirstLarge case) := by
  simp [smallDecodedColor, residualDeficientColor,
    PositionedFiveSupport.toSemantic, realization.caseFirstLarge_eq]

theorem DegreeNineCaseRealization.normalRoot_mem_caseSet
    {case : ResidualCase} (realization : DegreeNineCaseRealization case) :
    realization.normal.vertex.symm restoredRootLabel ∈
      degreeNineRootRepresentativeSet realization.normal.twisted
        (smallDecodedColor realization.skeleton) :=
  realization.normal.rootRepresentative

/-! ## Every exact semantic object reaches one realization -/

/-- Semantic completeness of the case interface.  The result retains the
whole transported branch and all normalization witnesses inside the selected
case realization. -/
theorem exists_degreeNineCaseRealization
    (ext : SemanticFiveSupport .uuu)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 9) :
    ∃ case : ResidualCase, Nonempty (DegreeNineCaseRealization case) := by
  obtain ⟨slot, branch, hbranch⟩ :=
    exists_positioned_degreeNine_indexed_representative ext hdegree
  obtain ⟨skeleton, normal, rootCase, htwisted, hroot⟩ :=
    exists_templateRootCase_for_positioned_degreeNine slot branch hbranch
  let case : ResidualCase :=
    ⟨slot, skeleton.firstLarge, rootCase⟩
  refine ⟨case, ⟨{
    branch := branch
    tailOwnDegreeNine := hbranch
    skeleton := skeleton
    caseFirstLarge_eq := rfl
    normal := normal
    caseTwisted_eq := htwisted
    caseRoot_eq := hroot
  }⟩⟩

/-! ## Exact per-case obstruction assembly -/

/-- What a certificate or a direct Lean proof for one finite label must
establish.  Its input is the full semantic realization, not merely the label.
-/
def DegreeNineCaseObstruction (case : ResidualCase) : Prop :=
  DegreeNineCaseRealization case → False

/-- One obstruction theorem for every residual semantic case. -/
structure DegreeNineResidualObstructionAssembly : Prop where
  refute : ∀ case : ResidualCase, DegreeNineCaseObstruction case

/-- The exact semantic subbranch eliminated by a complete assembly. -/
def UUUFiveSupportExactDegreeNine : Prop :=
  ∃ ext : SemanticFiveSupport .uuu,
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) = 9

theorem DegreeNineResidualObstructionAssembly.refute_semantic
    (assembly : DegreeNineResidualObstructionAssembly)
    (ext : SemanticFiveSupport .uuu) :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) ≠ 9 := by
  intro hdegree
  obtain ⟨case, ⟨realization⟩⟩ :=
    exists_degreeNineCaseRealization ext hdegree
  exact assembly.refute case realization

theorem DegreeNineResidualObstructionAssembly.no_exactDegreeNine
    (assembly : DegreeNineResidualObstructionAssembly) :
    ¬ UUUFiveSupportExactDegreeNine := by
  rintro ⟨ext, hdegree⟩
  exact assembly.refute_semantic ext hdegree

/-- A noncomputable indexing exposes the assembly as exactly 32 proof
obligations.  It does not discard the structured case label: each `Fin 32`
index is immediately decoded back to `ResidualCase`. -/
noncomputable def residualCaseEquivFin32 : ResidualCase ≃ Fin 32 :=
  Fintype.equivFinOfCardEq degreeNineResidualLocalCase_card

def DegreeNineIndexedObstructionAssembly : Prop :=
  ∀ index : Fin 32,
    DegreeNineCaseObstruction (residualCaseEquivFin32.symm index)

theorem indexedObstructionAssembly_toResidual
    (assembly : DegreeNineIndexedObstructionAssembly) :
    DegreeNineResidualObstructionAssembly := by
  refine ⟨?_⟩
  intro case
  have h := assembly (residualCaseEquivFin32 case)
  simpa using h

theorem no_exactDegreeNine_of_indexedObstructionAssembly
    (assembly : DegreeNineIndexedObstructionAssembly) :
    ¬ UUUFiveSupportExactDegreeNine :=
  (indexedObstructionAssembly_toResidual assembly).no_exactDegreeNine

#print axioms caseRoot_mem
#print axioms DegreeNineCaseRealization.smallDecodedColor_eq
#print axioms exists_degreeNineCaseRealization
#print axioms DegreeNineResidualObstructionAssembly.no_exactDegreeNine
#print axioms no_exactDegreeNine_of_indexedObstructionAssembly

end ProfileDUUUDegreeNineCaseRealization61
end R4333
