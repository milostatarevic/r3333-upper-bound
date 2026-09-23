import R4333Lean.ProfileDUUUFiveSupportPositionSymmetry

/-!
# Exact finite boundary for the UUU degree-ten five-support branch

The existing selected-position quotient preserves the interval `9 ≤ d ≤ 10`.
This module records that its concrete transports preserve the exact value of
the selected tail degree, strengthens the free-row C5 normalization with an
explicit tail-preservation equation, and packages the remaining degree-ten
boundary as four exact canonical obligations.

There is no SAT or LRAT import in this module.
-/

namespace R4333
namespace ProfileDUUUDegreeTenFiniteBoundary61

open ColoringJoinRows
open SingleRootStarCNF
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDSelectedPositionTransport
open ProfileDUUUFiveSupportPositionSymmetry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SemanticFiveSupport :=
  ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension

abbrev PositionedFiveSupport :=
  ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport

abbrev FiveVertex := ProfileDHighOwnFiveRowSplit61.FiveVertex

/-! ## Exact degree is preserved by the selected-position quotient -/

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
          (ProfileDFourRowKindSymmetry.tailVertexPerm .uuu))
        ProfileDFourRowKindSymmetry.hostColorPerm)
      (blockRootColor 0)
      (blockVertex 0 (blockOneTargetPosition selected).val) = _
  rw [colorDegree_mapEdgeColors, colorDegree_relabelVertices,
    hostColorPerm_symm_blockZeroRoot,
    tailVertexPerm_uuu_blockOneTarget]

/-! ## Four explicitly indexed exact representatives -/

def representativeIndexBySlot (slot : Fin 4) : SelectedIndex :=
  ![k15Index 0, k15Index 1, k15Index 2, k16Index (Fin.last 15)] slot

theorem representativeIndexBySlot_mem (slot : Fin 4) :
    representativeIndexBySlot slot ∈ uuuRepresentatives := by
  fin_cases slot <;> decide

theorem exists_representativeSlot_of_mem
    {index : SelectedIndex} (hindex : index ∈ uuuRepresentatives) :
    ∃ slot : Fin 4, representativeIndexBySlot slot = index := by
  simp only [uuuRepresentatives, List.mem_cons, List.not_mem_nil] at hindex
  rcases hindex with hindex | hindex | hindex | hindex
  · exact ⟨0, hindex.symm⟩
  · exact ⟨1, hindex.symm⟩
  · exact ⟨2, hindex.symm⟩
  · rcases hindex with hindex | hfalse
    · exact ⟨3, hindex.symm⟩
    · contradiction

theorem exists_positioned_degreeTen_representative
    (ext : SemanticFiveSupport .uuu)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 10) :
    ∃ index : SelectedIndex,
      index ∈ uuuRepresentatives ∧
        ∃ branch : PositionedFiveSupport .uuu index.1 index.2,
          colorDegree
              branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
              (blockRootColor index.1)
              (blockVertex index.1 index.2.val) = 10 := by
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
                (blockVertex 0 (k15Representative position).val) = 10 := by
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
                  (blockOneTargetPosition position)).val) = 10 := by
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
                (blockVertex 2 (Fin.last 15).val) = 10 := by
          rw [normalizeSupportBlockTwo_tailOwnDegree]
          exact hdegree
        refine ⟨k16Index (Fin.last 15), k16Index_last_mem,
          normalized, ?_⟩
        simpa [k16Index] using hnormalized

theorem exists_positioned_degreeTen_indexed_representative
    (ext : SemanticFiveSupport .uuu)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 10) :
    ∃ slot : Fin 4,
      ∃ branch : PositionedFiveSupport .uuu
          (representativeIndexBySlot slot).1
          (representativeIndexBySlot slot).2,
        colorDegree
            branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockRootColor (representativeIndexBySlot slot).1)
            (blockVertex (representativeIndexBySlot slot).1
              (representativeIndexBySlot slot).2.val) = 10 := by
  obtain ⟨index, hindex, branch, hbranch⟩ :=
    exists_positioned_degreeTen_representative ext hdegree
  obtain ⟨slot, hslot⟩ := exists_representativeSlot_of_mem hindex
  subst index
  exact ⟨slot, branch, hbranch⟩

/-! ## Free-row canonicalization with its tail equality exposed -/

theorem exists_canonicalTransport_preserving_tail
    {kind : ProfileDTripleJoinReduction.Kind}
    (ext : SemanticFiveSupport kind) :
    ∃ branch : CanonicalBranch kind ext.block ext.position,
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail =
        ext.toDegreeFlooredFiveExtension.toFiveExtension.tail := by
  obtain ⟨σ, hσ⟩ := ext.exists_inside_cycle_relabel
  let combined : Equiv.Perm FiveVertex := cycleComplementPerm.trans σ
  let transported := transportDegreeFlooredFiveExtension combined
    ext.toDegreeFlooredFiveExtension
  refine ⟨{
    toDegreeFlooredFiveExtension := transported
    allFiveOwn := ?_
    insideCanonical := ?_
    tailOwnDegreeLower := ?_
    tailOwnDegreeUpper := ?_
  }, rfl⟩
  · intro a
    exact ext.allFiveOwn (combined a)
  · intro a b hab
    change ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
      (combined a) (combined b) = _
    calc
      ext.toDegreeFlooredFiveExtension.toFiveExtension.inside
          (combined a) (combined b) =
        decodeRemainingColor ext.block
          (canonicalCycleWord.coloring (cycleComplementPerm a)
            (cycleComplementPerm b)) := by
              simpa [combined] using hσ
                (cycleComplementPerm a) (cycleComplementPerm b)
                (cycleComplementPerm.injective.ne hab)
      _ = decodeRemainingColor ext.block
          (!canonicalCycleWord.coloring a b) := by
            rw [canonicalCycleWord_cycleComplementPerm a b hab]
  · exact ext.tailOwnDegreeLower
  · exact ext.tailOwnDegreeUpper

theorem exists_canonical_degreeTen_indexed_representative
    (ext : SemanticFiveSupport .uuu)
    (hdegree :
      colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
          (blockRootColor ext.block)
          (blockVertex ext.block ext.position.val) = 10) :
    ∃ slot : Fin 4,
      ∃ branch : CanonicalBranch .uuu
          (representativeIndexBySlot slot).1
          (representativeIndexBySlot slot).2,
        colorDegree
            branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
            (blockRootColor (representativeIndexBySlot slot).1)
            (blockVertex (representativeIndexBySlot slot).1
              (representativeIndexBySlot slot).2.val) = 10 := by
  obtain ⟨slot, positioned, hpositioned⟩ :=
    exists_positioned_degreeTen_indexed_representative ext hdegree
  obtain ⟨branch, htail⟩ :=
    exists_canonicalTransport_preserving_tail positioned.toSemantic
  refine ⟨slot, branch, ?_⟩
  rw [htail]
  simpa [PositionedFiveSupport.toSemantic] using hpositioned

/-! ## Certificate-independent four-obligation interface -/

def DegreeTenRepresentativeObstruction (slot : Fin 4) : Prop :=
  ∀ branch : CanonicalBranch .uuu
      (representativeIndexBySlot slot).1
      (representativeIndexBySlot slot).2,
    colorDegree
        branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor (representativeIndexBySlot slot).1)
        (blockVertex (representativeIndexBySlot slot).1
          (representativeIndexBySlot slot).2.val) ≠ 10

structure DegreeTenRepresentativeObstructionAssembly : Prop where
  refute : ∀ slot : Fin 4, DegreeTenRepresentativeObstruction slot

def UUUFiveSupportExactDegreeTen : Prop :=
  ∃ ext : SemanticFiveSupport .uuu,
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) = 10

theorem DegreeTenRepresentativeObstructionAssembly.refute_semantic
    (assembly : DegreeTenRepresentativeObstructionAssembly)
    (ext : SemanticFiveSupport .uuu) :
    colorDegree ext.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor ext.block)
        (blockVertex ext.block ext.position.val) ≠ 10 := by
  intro hdegree
  obtain ⟨slot, branch, hbranch⟩ :=
    exists_canonical_degreeTen_indexed_representative ext hdegree
  exact assembly.refute slot branch hbranch

theorem DegreeTenRepresentativeObstructionAssembly.no_exactDegreeTen
    (assembly : DegreeTenRepresentativeObstructionAssembly) :
    ¬ UUUFiveSupportExactDegreeTen := by
  rintro ⟨ext, hdegree⟩
  exact assembly.refute_semantic ext hdegree

#print axioms normalizeSupportBlockZero_tailOwnDegree
#print axioms swapSupportBlockOneToZero_tailOwnDegree
#print axioms exists_positioned_degreeTen_indexed_representative
#print axioms exists_canonicalTransport_preserving_tail
#print axioms exists_canonical_degreeTen_indexed_representative
#print axioms DegreeTenRepresentativeObstructionAssembly.no_exactDegreeTen

end ProfileDUUUDegreeTenFiniteBoundary61
end R4333
