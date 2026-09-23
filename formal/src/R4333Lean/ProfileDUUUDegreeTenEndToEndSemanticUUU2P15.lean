import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15

/-!
# End-to-end semantic coverage for UUU / block two / position fifteen

Every exact degree-ten branch at this position is transported first to one
of the nine normalized support pairs, then to a checked row of the generic
600-row catalogue, through the checked orbit normalizer for that pair, and
finally to one of the 82 authoritative literal matrices.

This file deliberately stops at the semantic representative leaves.  It
does not import or assert an UNSAT certificate for those leaves.
-/

namespace R4333
namespace ProfileDUUUDegreeTenEndToEndSemanticUUU2P15

open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUDegreeTenCatalogLeafBridgeUUU2P15
open ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
open ProfileDUUUDegreeTenCatalogSemanticEntryUUU2P15
open ProfileDUUUDegreeTenCatalogOrbitTransportUUU2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SelectedPosition :=
  ProfileDDegreeTenMatrixLeafDataUUU2P15.selectedPosition

/-- The pulled-back catalogue row advertised by a leaf is exactly its
literal matrix on every off-diagonal edge. -/
theorem blockTwoCatalogMatrix_eq_leafMatrix_of_ne
    (leaf : Leaf) (left right : Fin 15) (hne : left ≠ right) :
    blockTwoCatalogMatrix
        (pairFirst (pairIndex leaf)) (pairSecond (pairIndex leaf))
        (alignedCatalogRowIndex leaf) left right =
      matrix leaf left right := by
  rw [matrix_eq_alignedCatalog leaf left right hne]
  rfl

theorem blockTwoCatalogMatrix_eq_leafMatrix_of_cross_group
    (leaf : Leaf) (left right : Fin 15)
    (hgroups : left.val / 5 ≠ right.val / 5) :
    blockTwoCatalogMatrix
        (pairFirst (pairIndex leaf)) (pairSecond (pairIndex leaf))
        (alignedCatalogRowIndex leaf) left right =
      matrix leaf left right := by
  apply blockTwoCatalogMatrix_eq_leafMatrix_of_ne leaf left right
  intro heq
  subst right
  exact hgroups rfl

/-- Replace the normalized catalogue matrix by the independently stored
authoritative literal matrix, without changing the semantic branch. -/
noncomputable def catalogRepresentativeExactToLeaf
    (leaf : Leaf)
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      (coordinatesFor
        (pairFirst (pairIndex leaf)) (pairSecond (pairIndex leaf)))
      (blockTwoCatalogMatrix
        (pairFirst (pairIndex leaf)) (pairSecond (pairIndex leaf))
        (alignedCatalogRowIndex leaf))) :
    RepresentativeExactBranch leaf := by
  exact {
    branch := exact.branch
    tailOwnDegreeTen := exact.tailOwnDegreeTen
    firstSupportExact := exact.firstSupportExact
    secondSupportExact := exact.secondSupportExact
    matrixExact := by
      intro left right hgroups
      exact (exact.matrixExact left right hgroups).trans
        (blockTwoCatalogMatrix_eq_leafMatrix_of_cross_group
          leaf left right hgroups)
  }

/-- Complete semantic coverage of the exact branch, stopping immediately
before any per-leaf UNSAT proof: every exact branch reaches one of the 82
authoritative representative exact branches. -/
theorem exists_representativeExactBranch_of_exact
    {coordinates : MatrixCoordinates 2}
    {matrix : EdgeColoring (Fin 15) (Fin 4)}
    (exact : ExactDegreeTenMatrixBranch .uuu 2 SelectedPosition
      coordinates matrix) :
    ∃ leaf : Leaf, Nonempty (RepresentativeExactBranch leaf) := by
  obtain ⟨pair, row, ⟨catalogExact⟩⟩ :=
    exists_catalogExactBranch_of_exact exact
  obtain ⟨representative, hrepresentative, ⟨representativeExact⟩⟩ :=
    exists_representativeCatalogExactBranch pair row catalogExact
  obtain ⟨leaf, hpair, hrow⟩ :=
    exists_authoritative_leaf_of_mem hrepresentative
  subst pair
  subst representative
  exact ⟨leaf, ⟨catalogRepresentativeExactToLeaf leaf representativeExact⟩⟩

#print axioms blockTwoCatalogMatrix_eq_leafMatrix_of_cross_group
#print axioms catalogRepresentativeExactToLeaf
#print axioms exists_representativeExactBranch_of_exact

end ProfileDUUUDegreeTenEndToEndSemanticUUU2P15
end R4333
