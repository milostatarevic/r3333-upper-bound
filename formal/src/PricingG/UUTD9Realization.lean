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
namespace UUTD9Realization

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
  branch : PositionedFiveSupport .uut
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

theorem exists_templateRootCase_for_positioned_degreeNine
    (slot : Fin 4)
    (branch : PositionedFiveSupport .uut
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


#print axioms DegreeNineCaseRealization.smallDecodedColor_eq
#print axioms exists_templateRootCase_for_positioned_degreeNine
end UUTD9Realization
end R4333
