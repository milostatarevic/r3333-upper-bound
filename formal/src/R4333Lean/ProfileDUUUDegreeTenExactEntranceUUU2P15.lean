import R4333Lean.ProfileDUUUDegreeTenExactEntranceGeneric61
import R4333Lean.ProfileDUUUDegreeTenEndToEndSemanticUUU2P15

/-!
# Canonical entrance for UUU / block two / position fifteen / degree ten

This instantiates the block-generic ordered-support constructor and composes
it with the 82-leaf semantic coverage theorem.  It contains no LRAT import.
-/

namespace R4333
namespace ProfileDUUUDegreeTenExactEntranceUUU2P15

open ProfileDTripleJoinReduction
open ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveSupportC5CNF
open ProfileDDegreeTenMatrixCNF

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition

theorem exists_exactDegreeTenMatrixBranch_selected
    (branch : CanonicalBranch .uuu 2 SelectedPosition)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 SelectedPosition.val) = 10) :
    ∃ coordinates : MatrixCoordinates 2,
      ∃ matrix : EdgeColoring (Fin 15) (Fin 4),
        Nonempty (ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
          coordinates matrix) :=
  ProfileDUUUDegreeTenExactEntranceGeneric61.exists_exactDegreeTenMatrixBranch_of_tailOwnDegree_ten
    branch hdegree

/-- Complete LRAT-free route from the canonical degree-ten branch to one of
the 82 authoritative exact leaves. -/
theorem exists_representativeExactBranch_of_canonical_degreeTen
    (branch : CanonicalBranch .uuu 2 SelectedPosition)
    (hdegree : colorDegree
      branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
        (blockRootColor 2) (blockVertex 2 SelectedPosition.val) = 10) :
    ∃ leaf : ProfileDDegreeTenMatrixLeafDataUUU2P15.Leaf,
      Nonempty
        (ProfileDDegreeTenMatrixLeafDataUUU2P15.RepresentativeExactBranch
          leaf) := by
  obtain ⟨coordinates, matrix, ⟨exact⟩⟩ :=
    exists_exactDegreeTenMatrixBranch_selected branch hdegree
  exact ProfileDUUUDegreeTenEndToEndSemanticUUU2P15.exists_representativeExactBranch_of_exact
    exact

#print axioms exists_exactDegreeTenMatrixBranch_selected
#print axioms exists_representativeExactBranch_of_canonical_degreeTen

end ProfileDUUUDegreeTenExactEntranceUUU2P15
end R4333
