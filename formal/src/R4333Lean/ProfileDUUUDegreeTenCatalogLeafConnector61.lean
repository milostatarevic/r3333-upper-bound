import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitCertificate61
import R4333Lean.ProfileDDegreeTenRepresentativeLeafBridge61

/-!
# Catalogue representatives are the ten authoritative UUU leaves

This is the small data connector between the independently checked 600-row
orbit certificate and the literal matrices used by the ten LRAT leaves.
Only ten 27-byte array equalities are checked here.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogLeafConnector61

open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDDegreeTenMatrixLeafTenDataUUU0
open ProfileDDegreeTenRepresentativeLeafBridge61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Leaf := ProfileDDegreeTenMatrixLeafTenDataUUU0.Leaf

def leafSupportKind : Leaf → SupportKind
  | .s0m0 | .s0m20 | .s0m21 | .s0m25 => .support0
  | .s2m0 | .s2m1 | .s2m5 | .s2m100 => .support2
  | .s7m0 | .s7m45 => .support7

def leafCatalogIndex (leaf : Leaf) : Fin 600 :=
  Fin.ofNat 600 (matrixIndexNumber leaf)

theorem leafCatalogIndex_values (leaf : Leaf) :
    leafCatalogIndex leaf = Fin.ofNat 600 (matrixIndexNumber leaf) := rfl

theorem leafCatalogIndex_mem_representativeSet (leaf : Leaf) :
    leafCatalogIndex leaf ∈ representativeSet (leafSupportKind leaf) := by
  cases leaf <;> decide

/-- Every member of the three finite representative sets names one of the
ten authoritative leaves. -/
theorem exists_leaf_of_representative
    (kind : SupportKind) (i : Fin 600)
    (hi : i ∈ representativeSet kind) :
    ∃ leaf : Leaf,
      leafSupportKind leaf = kind ∧ leafCatalogIndex leaf = i := by
  cases kind with
  | support0 =>
      simp [representativeSet] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨.s0m0, by decide⟩
      · exact ⟨.s0m20, by decide⟩
      · exact ⟨.s0m21, by decide⟩
      · exact ⟨.s0m25, by decide⟩
  | support2 =>
      simp [representativeSet] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨.s2m0, by decide⟩
      · exact ⟨.s2m1, by decide⟩
      · exact ⟨.s2m5, by decide⟩
      · exact ⟨.s2m100, by decide⟩
  | support7 =>
      simp [representativeSet] at hi
      rcases hi with rfl | rfl
      · exact ⟨.s7m0, by decide⟩
      · exact ⟨.s7m45, by decide⟩

/-- The selected row in the large catalogue is byte-for-byte the compact
row independently decoded by the representative-leaf bridge. -/
def catalogRepresentativeRow (leaf : Leaf) : Array Nat :=
  let i := leafCatalogIndex leaf
  ((catalogMatrixByteTable (leafSupportKind leaf))[i.val]?).getD #[]

theorem catalogRepresentativeRow_eq_packedCatalogRow (leaf : Leaf) :
    catalogRepresentativeRow leaf = packedCatalogRow leaf := by
  cases leaf <;> decide

theorem catalogMatrixColor_eq_packedCatalogColor
    (leaf : Leaf) (left right : Fin 15) :
    catalogMatrixColor (leafSupportKind leaf) (leafCatalogIndex leaf)
        left right =
      packedCatalogColor leaf left right := by
  unfold catalogMatrixColor packedCatalogColor
  change
    let edge := ProfileDUUUDegreeTenCatalogOrbits61.catalogEdgeIndex left right
    let row := catalogRepresentativeRow leaf
    let byte := (row[edge / 4]?).getD 0
    Fin.ofNat 4 ((byte >>> (2 * (edge % 4))) % 4) = _
  rw [catalogRepresentativeRow_eq_packedCatalogRow]
  rfl

theorem catalogMatrixColor_eq_leafMatrix_of_ne
    (leaf : Leaf) (left right : Fin 15) (hne : left ≠ right) :
    catalogMatrixColor (leafSupportKind leaf) (leafCatalogIndex leaf)
        left right = matrix leaf left right := by
  exact (catalogMatrixColor_eq_packedCatalogColor leaf left right).trans
    (packedCatalogColor_eq_matrix_of_ne leaf left right hne)

theorem catalogMatrixColor_eq_leafMatrix_of_cross_group
    (leaf : Leaf) (left right : Fin 15)
    (hgroups : left.val / 5 ≠ right.val / 5) :
    catalogMatrixColor (leafSupportKind leaf) (leafCatalogIndex leaf)
        left right = matrix leaf left right := by
  exact (catalogMatrixColor_eq_packedCatalogColor leaf left right).trans
    (packedCatalogColor_eq_matrix_of_cross_group leaf left right hgroups)

#print axioms exists_leaf_of_representative
#print axioms catalogRepresentativeRow_eq_packedCatalogRow
#print axioms catalogMatrixColor_eq_leafMatrix_of_cross_group

end ProfileDUUUDegreeTenCatalogLeafConnector61
end R4333
