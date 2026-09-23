import R4333Lean.ProfileDHighOwnFiveSupportC5AllCaps

namespace R4333
namespace ProfileDHighOwnFiveSupportC5Formula

open FiniteColorCNF SequentialAtMostManyCNF
open ProfileDTripleJoinReduction
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5CounterNamespace
open ProfileDHighOwnFiveSupportC5AllCaps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind

def fmla (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)) : Sat.Fmla :=
  manySequentialAtMostFmla (baseFmla kind block position)
    (counterSpecs block position)

noncomputable def finalValuation
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) : Sat.Valuation :=
  iteratedSequentialExtension (counterSpecs block position)
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension))

theorem canonicalBranch_satisfies_explicit
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (iteratedSequentialExtension (counterSpecs block position)
      (coloringValuation
        (totalColoring
          branch.toDegreeFlooredFiveExtension.toFiveExtension))).satisfies_fmla
      (manySequentialAtMostFmla (baseFmla kind block position)
        (counterSpecs block position)) := by
  exact iteratedExtension_satisfies_manySequentialAtMostFmla
    (baseFmla kind block position) (counterSpecs block position)
    (coloringValuation
      (totalColoring branch.toDegreeFlooredFiveExtension.toFiveExtension))
    (counterSpecs_wellFormed kind block position)
    (canonicalBranch_satisfies_baseFmla branch)
    (allCaps_of_canonicalBranch branch)

theorem canonicalBranch_satisfies_fmla
    {kind : Kind} {block : Fin 3} {position : Fin (blockSize block)}
    (branch : CanonicalBranch kind block position) :
    (finalValuation branch).satisfies_fmla (fmla kind block position) := by
  change (iteratedSequentialExtension (counterSpecs block position)
      (coloringValuation
        (totalColoring
          branch.toDegreeFlooredFiveExtension.toFiveExtension))).satisfies_fmla
    (manySequentialAtMostFmla (baseFmla kind block position)
      (counterSpecs block position))
  exact canonicalBranch_satisfies_explicit branch

theorem fiveSupport_yields_satisfying_branch {kind : Kind}
    (ext : ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension kind) :
  ∃ branch : CanonicalBranch kind ext.block ext.position,
      (finalValuation branch).satisfies_fmla
        (fmla kind ext.block ext.position) := by
  obtain ⟨branch⟩ := exists_canonicalTransport ext
  refine ⟨branch, ?_⟩
  exact canonicalBranch_satisfies_fmla
    (kind := kind) (block := ext.block) (position := ext.position) branch

end ProfileDHighOwnFiveSupportC5Formula
end R4333
