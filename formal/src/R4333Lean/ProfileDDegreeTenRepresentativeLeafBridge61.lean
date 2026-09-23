import R4333Lean.ProfileDDegreeTenMatrixLeafTenDataUUU0

/-!
# The ten UUU degree-ten representative labels as semantic leaves

This is the deliberately small interface between the finite catalogue labels
used by the orbit computation and the ten checked matrix-leaf records.

The large catalogue stores matrices as 27 packed bytes.  We record only its
ten representative rows here and check, by ordinary kernel reduction, that
decoding each row gives the corresponding literal `Leaf.matrix` on every
ordinary edge.  Thus a catalogue bridge only has to identify one packed row;
it never has to compare two expanded `15 × 15` tables.

The final theorem is the semantic endpoint needed after transport: an exact
branch whose target coordinates and matrix are those of a representative
leaf satisfies that leaf's authoritative formula.
-/

namespace R4333
namespace ProfileDDegreeTenRepresentativeLeafBridge61

open ProfileDHighOwnFiveSupportC5CNF
open ProfileDHighOwnFiveSupportC5Formula
open ProfileDDegreeTenMatrixCNF
open ProfileDDegreeTenMatrixLeafTenDataUUU0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Leaf := ProfileDDegreeTenMatrixLeafTenDataUUU0.Leaf

/-! ## Numeric catalogue labels -/

/-- The `(K15-support index, matrix index)` label attached to a leaf. -/
def representativePair (leaf : Leaf) : Nat × Nat :=
  (supportIndex leaf, matrixIndexNumber leaf)

def representativePairs : List (Nat × Nat) :=
  [(0, 0), (0, 20), (0, 21), (0, 25),
   (2, 0), (2, 1), (2, 5), (2, 100),
   (7, 0), (7, 45)]

theorem representativePair_values :
    leaves.map representativePair = representativePairs := by
  exact leaves_metadata

theorem representativePair_mem (leaf : Leaf) :
    representativePair leaf ∈ representativePairs := by
  cases leaf <;> decide

theorem representativePair_injective :
    Function.Injective representativePair := by
  intro left right heq
  cases left <;> cases right <;>
    simp_all [representativePair, supportIndex, matrixIndexNumber]

theorem representativePair_complete (pair : Nat × Nat) :
    pair ∈ representativePairs ↔
      ∃ leaf : Leaf, representativePair leaf = pair := by
  constructor
  · intro hpair
    simp [representativePairs] at hpair
    rcases hpair with hpair | hpair | hpair | hpair | hpair |
      hpair | hpair | hpair | hpair | hpair
    · exact ⟨.s0m0, hpair.symm⟩
    · exact ⟨.s0m20, hpair.symm⟩
    · exact ⟨.s0m21, hpair.symm⟩
    · exact ⟨.s0m25, hpair.symm⟩
    · exact ⟨.s2m0, hpair.symm⟩
    · exact ⟨.s2m1, hpair.symm⟩
    · exact ⟨.s2m5, hpair.symm⟩
    · exact ⟨.s2m100, hpair.symm⟩
    · exact ⟨.s7m0, hpair.symm⟩
    · exact ⟨.s7m45, hpair.symm⟩
  · rintro ⟨leaf, rfl⟩
    exact representativePair_mem leaf

theorem representativePair_unique
    {pair : Nat × Nat} {left right : Leaf}
    (hleft : representativePair left = pair)
    (hright : representativePair right = pair) :
    left = right := by
  exact representativePair_injective (hleft.trans hright.symm)

/-! ## The ten packed catalogue rows -/

/-- The 27-byte rows at the ten representative positions in the catalogue.
The order is the upper-triangle edge order used by `catalogEdgeIndex`. -/
def packedCatalogRow : Leaf → Array Nat
  | .s0m0 =>
      #[190, 136, 227, 227, 11, 43, 179, 179, 50, 184, 58, 188, 48,
        34, 179, 204, 59, 62, 190, 128, 242, 143, 203, 58, 162, 2, 2]
  | .s0m20 =>
      #[190, 200, 34, 239, 179, 34, 179, 235, 192, 139, 131, 190, 32,
        242, 176, 204, 250, 60, 236, 194, 232, 239, 232, 56, 162, 2, 2]
  | .s0m21 =>
      #[190, 200, 34, 239, 11, 46, 179, 143, 200, 139, 184, 188, 224,
        194, 176, 204, 163, 63, 142, 131, 62, 239, 200, 46, 162, 2, 2]
  | .s0m25 =>
      #[190, 200, 226, 227, 179, 34, 179, 235, 192, 184, 35, 190, 32,
        248, 176, 204, 202, 63, 236, 194, 142, 143, 238, 11, 162, 2, 2]
  | .s2m0 =>
      #[190, 160, 35, 239, 227, 40, 179, 187, 192, 139, 131, 190, 160,
        204, 176, 51, 250, 12, 163, 51, 187, 59, 190, 35, 162, 2, 2]
  | .s2m1 =>
      #[190, 160, 35, 239, 11, 43, 179, 47, 194, 139, 44, 190, 160,
        195, 176, 51, 163, 15, 250, 176, 227, 179, 187, 35, 162, 2, 2]
  | .s2m5 =>
      #[190, 160, 227, 227, 227, 40, 179, 187, 192, 184, 139, 188, 32,
        236, 176, 51, 202, 15, 59, 50, 187, 251, 50, 58, 162, 2, 2]
  | .s2m100 =>
      #[190, 176, 226, 227, 163, 44, 179, 11, 59, 184, 139, 188, 224,
        2, 179, 51, 202, 15, 59, 50, 235, 251, 50, 46, 162, 2, 2]
  | .s7m0 =>
      #[190, 160, 227, 227, 227, 40, 179, 139, 51, 184, 139, 188, 224,
        32, 179, 51, 202, 195, 59, 254, 184, 248, 194, 58, 162, 2, 2]
  | .s7m45 =>
      #[190, 176, 226, 227, 163, 44, 179, 59, 200, 184, 139, 188, 32,
        206, 176, 51, 202, 195, 59, 254, 232, 248, 194, 46, 162, 2, 2]

@[simp] theorem packedCatalogRow_size (leaf : Leaf) :
    (packedCatalogRow leaf).size = 27 := by
  cases leaf <;> decide

/-- Upper-triangle edge offset used by the packed catalogue. -/
def catalogEdgeIndex (left right : Fin 15) : Nat :=
  let low := min left.val right.val
  let high := max left.val right.val
  low * (29 - low) / 2 + (high - low - 1)

def packedCatalogColor (leaf : Leaf) (left right : Fin 15) : Fin 4 :=
  let edge := catalogEdgeIndex left right
  let byte := ((packedCatalogRow leaf)[edge / 4]?).getD 0
  Fin.ofNat 4 ((byte >>> (2 * (edge % 4))) % 4)

/-- The packed representative row and the authoritative literal leaf matrix
are exactly the same on every ordinary edge. -/
theorem packedCatalogColor_eq_matrix_of_ne
    (leaf : Leaf) (left right : Fin 15) (hne : left ≠ right) :
    packedCatalogColor leaf left right = matrix leaf left right := by
  cases leaf <;> fin_cases left <;> fin_cases right <;> simp_all <;> decide

theorem packedCatalogColor_eq_matrix_of_cross_group
    (leaf : Leaf) (left right : Fin 15)
    (hgroups : left.val / 5 ≠ right.val / 5) :
    packedCatalogColor leaf left right = matrix leaf left right := by
  apply packedCatalogColor_eq_matrix_of_ne
  intro heq
  subst right
  exact hgroups rfl

/-! ## Semantic endpoint after orbit transport -/

/-- The exact-branch type obtained when the generic transport constructor is
instantiated at one of the ten representative targets. -/
abbrev RepresentativeExactBranch (leaf : Leaf) :=
  ExactDegreeTenMatrixBranch .uuu 0
    ProfileDDegreeTenMatrixLeafUUU0S0M25.selectedPosition
    (coordinates leaf) (matrix leaf)

/-- A transported branch identified with a representative target satisfies
the exact authoritative formula consumed by that leaf's checked LRAT proof. -/
theorem representativeExactBranch_satisfies_formula
    (leaf : Leaf) (exact : RepresentativeExactBranch leaf) :
    (finalValuation exact.branch).satisfies_fmla (formula leaf) := by
  exact exactBranch_satisfies_fixedDegreeTenMatrixFmla exact

#print axioms packedCatalogColor_eq_matrix_of_ne
#print axioms representativeExactBranch_satisfies_formula

end ProfileDDegreeTenRepresentativeLeafBridge61
end R4333
