import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS0C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS0C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS0C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS0C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS0C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS0C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS2C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS2C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS2C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS2C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS2C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS2C5
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS7C0
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS7C1
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS7C2
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS7C3
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS7C4
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitChunkS7C5

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem catalogNormalizerEquationAt_of_sixChunks
    (kind : SupportKind)
    (chunk0 : ∀ offset : Fin 100,
      CatalogNormalizerEquationAt kind (catalogChunkIndex 0 offset))
    (chunk1 : ∀ offset : Fin 100,
      CatalogNormalizerEquationAt kind (catalogChunkIndex 1 offset))
    (chunk2 : ∀ offset : Fin 100,
      CatalogNormalizerEquationAt kind (catalogChunkIndex 2 offset))
    (chunk3 : ∀ offset : Fin 100,
      CatalogNormalizerEquationAt kind (catalogChunkIndex 3 offset))
    (chunk4 : ∀ offset : Fin 100,
      CatalogNormalizerEquationAt kind (catalogChunkIndex 4 offset))
    (chunk5 : ∀ offset : Fin 100,
      CatalogNormalizerEquationAt kind (catalogChunkIndex 5 offset))
    (i : Fin 600) :
    CatalogNormalizerEquationAt kind i := by
  by_cases h0 : i.val < 100
  · let offset : Fin 100 := ⟨i.val, h0⟩
    have hindex : catalogChunkIndex 0 offset = i := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
    rw [← hindex]
    exact chunk0 offset
  by_cases h1 : i.val < 200
  · let offset : Fin 100 := ⟨i.val - 100, by omega⟩
    have hindex : catalogChunkIndex 1 offset = i := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk1 offset
  by_cases h2 : i.val < 300
  · let offset : Fin 100 := ⟨i.val - 200, by omega⟩
    have hindex : catalogChunkIndex 2 offset = i := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk2 offset
  by_cases h3 : i.val < 400
  · let offset : Fin 100 := ⟨i.val - 300, by omega⟩
    have hindex : catalogChunkIndex 3 offset = i := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk3 offset
  by_cases h4 : i.val < 500
  · let offset : Fin 100 := ⟨i.val - 400, by omega⟩
    have hindex : catalogChunkIndex 4 offset = i := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk4 offset
  · let offset : Fin 100 := ⟨i.val - 500, by omega⟩
    have hindex : catalogChunkIndex 5 offset = i := by
      apply Fin.ext
      simp [catalogChunkIndex, offset]
      omega
    rw [← hindex]
    exact chunk5 offset

theorem catalogNormalizerEquationAt_all
    (kind : SupportKind) (i : Fin 600) :
    CatalogNormalizerEquationAt kind i := by
  cases kind with
  | support0 =>
      exact catalogNormalizerEquationAt_of_sixChunks .support0
        catalogNormalizerEquation_support0_chunk0
        catalogNormalizerEquation_support0_chunk1
        catalogNormalizerEquation_support0_chunk2
        catalogNormalizerEquation_support0_chunk3
        catalogNormalizerEquation_support0_chunk4
        catalogNormalizerEquation_support0_chunk5 i
  | support2 =>
      exact catalogNormalizerEquationAt_of_sixChunks .support2
        catalogNormalizerEquation_support2_chunk0
        catalogNormalizerEquation_support2_chunk1
        catalogNormalizerEquation_support2_chunk2
        catalogNormalizerEquation_support2_chunk3
        catalogNormalizerEquation_support2_chunk4
        catalogNormalizerEquation_support2_chunk5 i
  | support7 =>
      exact catalogNormalizerEquationAt_of_sixChunks .support7
        catalogNormalizerEquation_support7_chunk0
        catalogNormalizerEquation_support7_chunk1
        catalogNormalizerEquation_support7_chunk2
        catalogNormalizerEquation_support7_chunk3
        catalogNormalizerEquation_support7_chunk4
        catalogNormalizerEquation_support7_chunk5 i

/-- The central finite certificate: relabeling all three five-blocks by the
stored extendible actions sends every decoded catalogue matrix exactly to its
stored representative matrix. -/
theorem catalog_normalizer_equation
    (kind : SupportKind) (i : Fin 600)
    (leftBlock rightBlock : Fin 3) (left right : Fin 5)
    (hblocks : leftBlock < rightBlock) :
    catalogMatrixColor kind i
        (blockVertex leftBlock
          (normalizerBlockAction kind i leftBlock left))
        (blockVertex rightBlock
          (normalizerBlockAction kind i rightBlock right)) =
      catalogMatrixColor kind (representativeIndex kind i)
        (blockVertex leftBlock left) (blockVertex rightBlock right) :=
  catalogNormalizerEquationAt_all kind i leftBlock rightBlock left right hblocks

theorem exists_catalog_normalization
    (kind : SupportKind) (i : Fin 600) :
    ∃ representative ∈ representativeSet kind,
      ∃ a0 a1 a2 : Fin 10,
        ∀ leftBlock rightBlock : Fin 3, ∀ left right : Fin 5,
          leftBlock < rightBlock →
          catalogMatrixColor kind i
              (blockVertex leftBlock
                (blockAction kind a0 a1 a2 leftBlock left))
              (blockVertex rightBlock
                (blockAction kind a0 a1 a2 rightBlock right)) =
            catalogMatrixColor kind representative
              (blockVertex leftBlock left) (blockVertex rightBlock right) := by
  refine ⟨representativeIndex kind i, representativeIndex_mem kind i,
    freeActionIndex kind i, u15ActionIndex kind i, u16ActionIndex kind i, ?_⟩
  intro leftBlock rightBlock left right hblocks
  exact catalog_normalizer_equation kind i leftBlock rightBlock left right hblocks

#print axioms catalog_normalizer_equation
#print axioms exists_catalog_normalization

end ProfileDUUUDegreeTenCatalogOrbits61
end R4333
