import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P0C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P0C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P0C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P0C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P0C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P0C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P1C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P1C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P1C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P1C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P1C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P1C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P2C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P2C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P2C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P2C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P2C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P2C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P3C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P3C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P3C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P3C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P3C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P3C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P4C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P4C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P4C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P4C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P4C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P4C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P5C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P5C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P5C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P5C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P5C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P5C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P6C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P6C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P6C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P6C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P6C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P6C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P7C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P7C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P7C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P7C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P7C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P7C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P8C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P8C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P8C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P8C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P8C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkUUU2P15P8C5

/-!
# Complete orbit certificate for UUU / block two / position fifteen

The 54 bounded certificates below combine into an explicit normalization of
all nine 600-row catalogues to the 82 authoritative literal leaves.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogLeafBridgeUUU2P15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem normalizerEquationAt_of_sixChunks
    (pair : Fin 9)
    (chunk0 : ∀ offset : Fin 100,
      NormalizerEquationAt pair (catalogChunkIndex 0 offset))
    (chunk1 : ∀ offset : Fin 100,
      NormalizerEquationAt pair (catalogChunkIndex 1 offset))
    (chunk2 : ∀ offset : Fin 100,
      NormalizerEquationAt pair (catalogChunkIndex 2 offset))
    (chunk3 : ∀ offset : Fin 100,
      NormalizerEquationAt pair (catalogChunkIndex 3 offset))
    (chunk4 : ∀ offset : Fin 100,
      NormalizerEquationAt pair (catalogChunkIndex 4 offset))
    (chunk5 : ∀ offset : Fin 100,
      NormalizerEquationAt pair (catalogChunkIndex 5 offset))
    (row : Fin 600) :
    NormalizerEquationAt pair row := by
  by_cases h0 : row.val < 100
  · let offset : Fin 100 := ⟨row.val, h0⟩
    have hindex : catalogChunkIndex 0 offset = row := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
    rw [← hindex]
    exact chunk0 offset
  by_cases h1 : row.val < 200
  · let offset : Fin 100 := ⟨row.val - 100, by omega⟩
    have hindex : catalogChunkIndex 1 offset = row := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk1 offset
  by_cases h2 : row.val < 300
  · let offset : Fin 100 := ⟨row.val - 200, by omega⟩
    have hindex : catalogChunkIndex 2 offset = row := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk2 offset
  by_cases h3 : row.val < 400
  · let offset : Fin 100 := ⟨row.val - 300, by omega⟩
    have hindex : catalogChunkIndex 3 offset = row := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk3 offset
  by_cases h4 : row.val < 500
  · let offset : Fin 100 := ⟨row.val - 400, by omega⟩
    have hindex : catalogChunkIndex 4 offset = row := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk4 offset
  · let offset : Fin 100 := ⟨row.val - 500, by omega⟩
    have hindex : catalogChunkIndex 5 offset = row := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk5 offset

theorem normalizerEquationAt_all (pair : Fin 9) (row : Fin 600) :
    NormalizerEquationAt pair row := by
  fin_cases pair
  · exact normalizerEquationAt_of_sixChunks 0
      normalizerEquation_pair0_chunk0
      normalizerEquation_pair0_chunk1
      normalizerEquation_pair0_chunk2
      normalizerEquation_pair0_chunk3
      normalizerEquation_pair0_chunk4
      normalizerEquation_pair0_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 1
      normalizerEquation_pair1_chunk0
      normalizerEquation_pair1_chunk1
      normalizerEquation_pair1_chunk2
      normalizerEquation_pair1_chunk3
      normalizerEquation_pair1_chunk4
      normalizerEquation_pair1_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 2
      normalizerEquation_pair2_chunk0
      normalizerEquation_pair2_chunk1
      normalizerEquation_pair2_chunk2
      normalizerEquation_pair2_chunk3
      normalizerEquation_pair2_chunk4
      normalizerEquation_pair2_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 3
      normalizerEquation_pair3_chunk0
      normalizerEquation_pair3_chunk1
      normalizerEquation_pair3_chunk2
      normalizerEquation_pair3_chunk3
      normalizerEquation_pair3_chunk4
      normalizerEquation_pair3_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 4
      normalizerEquation_pair4_chunk0
      normalizerEquation_pair4_chunk1
      normalizerEquation_pair4_chunk2
      normalizerEquation_pair4_chunk3
      normalizerEquation_pair4_chunk4
      normalizerEquation_pair4_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 5
      normalizerEquation_pair5_chunk0
      normalizerEquation_pair5_chunk1
      normalizerEquation_pair5_chunk2
      normalizerEquation_pair5_chunk3
      normalizerEquation_pair5_chunk4
      normalizerEquation_pair5_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 6
      normalizerEquation_pair6_chunk0
      normalizerEquation_pair6_chunk1
      normalizerEquation_pair6_chunk2
      normalizerEquation_pair6_chunk3
      normalizerEquation_pair6_chunk4
      normalizerEquation_pair6_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 7
      normalizerEquation_pair7_chunk0
      normalizerEquation_pair7_chunk1
      normalizerEquation_pair7_chunk2
      normalizerEquation_pair7_chunk3
      normalizerEquation_pair7_chunk4
      normalizerEquation_pair7_chunk5 row
  · exact normalizerEquationAt_of_sixChunks 8
      normalizerEquation_pair8_chunk0
      normalizerEquation_pair8_chunk1
      normalizerEquation_pair8_chunk2
      normalizerEquation_pair8_chunk3
      normalizerEquation_pair8_chunk4
      normalizerEquation_pair8_chunk5 row

theorem catalog_normalizer_equation
    (pair : Fin 9) (row : Fin 600)
    (leftBlock rightBlock : Fin 3) (hblocks : leftBlock < rightBlock)
    (left right : Fin 5) :
    catalogMatrixColor (catalogSupportKind (pairFirst pair)) row
        (blockVertex leftBlock (actionAt pair row leftBlock left))
        (blockVertex rightBlock (actionAt pair row rightBlock right)) =
      catalogMatrixColor (catalogSupportKind (pairFirst pair))
        (representativeIndex pair row)
        (blockVertex leftBlock left) (blockVertex rightBlock right) :=
  normalizerEquationAt_all pair row leftBlock rightBlock hblocks left right

def pairBlockAction (pair : Fin 9) (a0 a1 a2 : Fin 10)
    (block : Fin 3) (position : Fin 5) : Fin 5 :=
  match block.val with
  | 0 => freeAction a0 position
  | 1 => alignedFirstAction (pairFirst pair) a1 position
  | _ => alignedSecondAction (pairSecond pair) a2 position

theorem exists_catalog_normalization
    (pair : Fin 9) (row : Fin 600) :
    ∃ representative ∈ representativeSet pair,
      ∃ a0 a1 a2 : Fin 10,
        ∀ leftBlock rightBlock : Fin 3, leftBlock < rightBlock →
          ∀ left right : Fin 5,
            catalogMatrixColor (catalogSupportKind (pairFirst pair)) row
                (blockVertex leftBlock
                  (pairBlockAction pair a0 a1 a2 leftBlock left))
                (blockVertex rightBlock
                  (pairBlockAction pair a0 a1 a2 rightBlock right)) =
              catalogMatrixColor (catalogSupportKind (pairFirst pair)) representative
                (blockVertex leftBlock left) (blockVertex rightBlock right) := by
  refine ⟨representativeIndex pair row, representativeIndex_mem pair row,
    freeActionIndex pair row, firstActionIndex pair row,
    secondActionIndex pair row, ?_⟩
  intro leftBlock rightBlock hblocks left right
  exact catalog_normalizer_equation pair row leftBlock rightBlock hblocks left right

def authoritativeLeaves (pair : Fin 9) : Finset Leaf :=
  Finset.univ.filter fun leaf => pairIndex leaf = pair

theorem representativeSet_eq_alignedRows (pair : Fin 9) :
    representativeSet pair =
      (authoritativeLeaves pair).image alignedCatalogRowIndex := by
  fin_cases pair <;> decide

theorem exists_authoritative_leaf_of_mem
    {pair : Fin 9} {row : Fin 600}
    (hrow : row ∈ representativeSet pair) :
    ∃ leaf : Leaf,
      pairIndex leaf = pair ∧ alignedCatalogRowIndex leaf = row := by
  have himage : row ∈ (authoritativeLeaves pair).image alignedCatalogRowIndex := by
    rw [← representativeSet_eq_alignedRows]
    exact hrow
  obtain ⟨leaf, hleaf, heq⟩ := Finset.mem_image.mp himage
  exact ⟨leaf, (Finset.mem_filter.mp hleaf).2, heq⟩

/-- Every one of the 5,400 labelled catalogue rows is explicitly normalized
to the aligned catalogue row of one of the 82 authoritative literal leaves. -/
theorem exists_catalog_normalization_to_authoritative_leaf
    (pair : Fin 9) (row : Fin 600) :
    ∃ leaf : Leaf, pairIndex leaf = pair ∧
      ∃ a0 a1 a2 : Fin 10,
        ∀ leftBlock rightBlock : Fin 3, leftBlock < rightBlock →
          ∀ left right : Fin 5,
            catalogMatrixColor (catalogSupportKind (pairFirst pair)) row
                (blockVertex leftBlock
                  (pairBlockAction pair a0 a1 a2 leftBlock left))
                (blockVertex rightBlock
                  (pairBlockAction pair a0 a1 a2 rightBlock right)) =
              catalogMatrixColor (catalogSupportKind (pairFirst pair))
                (alignedCatalogRowIndex leaf)
                (blockVertex leftBlock left) (blockVertex rightBlock right) := by
  obtain ⟨leaf, hpair, hrow⟩ :=
    exists_authoritative_leaf_of_mem (representativeIndex_mem pair row)
  refine ⟨leaf, hpair, freeActionIndex pair row, firstActionIndex pair row,
    secondActionIndex pair row, ?_⟩
  intro leftBlock rightBlock hblocks left right
  rw [hrow]
  exact catalog_normalizer_equation pair row leftBlock rightBlock hblocks left right

#print axioms catalog_normalizer_equation
#print axioms exists_catalog_normalization
#print axioms representativeSet_eq_alignedRows
#print axioms exists_catalog_normalization_to_authoritative_leaf

end ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
end R4333
