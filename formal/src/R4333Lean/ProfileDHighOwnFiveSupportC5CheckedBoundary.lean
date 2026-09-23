import R4333Lean.ProfileDHighOwnFiveSupportC5Formula

/-!
# Final trusted boundary for profile-D five-support C5 branches

The theorem `fiveSupport_yields_satisfying_branch` is the one-way semantic
completeness statement needed by a future search: every genuine semantic
five-support object, after its proved row relabeling, gives a valuation of
one exact Lean-generated formula.  Conversely, a kernel-checked LRAT proof
for every kind/block/position formula rules out every such object.

No LRAT certificate or refutation theorem is asserted in this file.
-/

namespace R4333
namespace ProfileDHighOwnFiveSupportC5CheckedBoundary

open FiniteColorCNF SequentialAtMostCNF SequentialAtMostManyCNF
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDRowSupportBounds61 ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5CounterNamespace
open ProfileDHighOwnFiveSupportC5AllCaps
open ProfileDHighOwnFiveSupportC5Formula

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Kind := ProfileDTripleJoinReduction.Kind

/-! ## All 42 mathematical caps -/

/-! ## Empty checked-certificate interfaces -/

/-- Exact proposition produced by `checked_lrat_proof` for one branch. -/
def BranchLRATRefutation (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)) : Prop :=
  (fmla kind block position).proof Sat.Clause.nil

theorem noCanonicalBranch_of_lrat
    (kind : Kind) (block : Fin 3) (position : Fin (blockSize block))
    (hunsat : BranchLRATRefutation kind block position) :
    ¬Nonempty (CanonicalBranch kind block position) := by
  rintro ⟨branch⟩
  exact hunsat (finalValuation branch)
    (canonicalBranch_satisfies_fmla branch)

/-- A future certificate package has one kernel theorem for every one of the
`8 × (15+15+16) = 368` exact branches.  This record has no inhabitant here. -/
structure AllBranchLRATRefutations : Prop where
  refutation : ∀ (kind : Kind) (block : Fin 3)
    (position : Fin (blockSize block)),
      BranchLRATRefutation kind block position

def UniversalCanonicalBranchObstruction : Prop :=
  ∀ (kind : Kind) (block : Fin 3) (position : Fin (blockSize block)),
    ¬Nonempty (CanonicalBranch kind block position)

theorem AllBranchLRATRefutations.obstruction
    (h : AllBranchLRATRefutations) :
    UniversalCanonicalBranchObstruction := by
  intro kind block position
  exact noCanonicalBranch_of_lrat kind block position
    (h.refutation kind block position)

theorem noFiveSupport_of_allBranch_lrat
    (h : AllBranchLRATRefutations) (kind : Kind) :
    ¬Nonempty
      (ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension kind) := by
  rintro ⟨ext⟩
  obtain ⟨branch⟩ := exists_canonicalTransport ext
  exact h.obstruction kind ext.block ext.position ⟨branch⟩

#print axioms R4333.ProfileDHighOwnFiveSupportC5CNF.exists_canonicalTransport
#print axioms R4333.ProfileDHighOwnFiveSupportC5CNF.mem_counterContexts
#print axioms R4333.ProfileDHighOwnFiveSupportC5CNF.trueInputCount_selectedTailOtherColorAtoms
#print axioms R4333.ProfileDHighOwnFiveSupportC5CounterNamespace.counterSpecs_wellFormed
#print axioms R4333.ProfileDHighOwnFiveSupportC5AllCaps.allCaps_of_canonicalBranch
#print axioms R4333.ProfileDHighOwnFiveSupportC5Formula.canonicalBranch_satisfies_fmla
#print axioms R4333.ProfileDHighOwnFiveSupportC5Formula.fiveSupport_yields_satisfying_branch
#print axioms R4333.ProfileDHighOwnFiveSupportC5CheckedBoundary.noCanonicalBranch_of_lrat
#print axioms R4333.ProfileDHighOwnFiveSupportC5CheckedBoundary.noFiveSupport_of_allBranch_lrat

end ProfileDHighOwnFiveSupportC5CheckedBoundary
end R4333
