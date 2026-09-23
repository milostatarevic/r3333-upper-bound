import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C0
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C1
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C2
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C3
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C4
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C5
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C6
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C7
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C8
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C9
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C10
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C11
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C12
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C13
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C14
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C15
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C16
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C17
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C18
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS0C19
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C0
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C1
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C2
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C3
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C4
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C5
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C6
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C7
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C8
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C9
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C10
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C11
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C12
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C13
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C14
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C15
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C16
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C17
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C18
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS2C19
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C0
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C1
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C2
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C3
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C4
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C5
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C6
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C7
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C8
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C9
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C10
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C11
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C12
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C13
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C14
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C15
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C16
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C17
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C18
import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateChunkS7C19

/-!
# Aggregated candidate-to-catalogue certificate
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogCandidateEquation61

open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogCompletenessData61

theorem candidateCatalogEquation_chunk
    (kind : SupportKind) (chunk : Fin 20) (offset : Fin 100) :
    CandidateCatalogEquationAt kind
      (candidateEquationChunkIndex chunk offset) := by
  cases kind <;> fin_cases chunk
  · exact candidateCatalogEquation_support0_chunk0 offset
  · exact candidateCatalogEquation_support0_chunk1 offset
  · exact candidateCatalogEquation_support0_chunk2 offset
  · exact candidateCatalogEquation_support0_chunk3 offset
  · exact candidateCatalogEquation_support0_chunk4 offset
  · exact candidateCatalogEquation_support0_chunk5 offset
  · exact candidateCatalogEquation_support0_chunk6 offset
  · exact candidateCatalogEquation_support0_chunk7 offset
  · exact candidateCatalogEquation_support0_chunk8 offset
  · exact candidateCatalogEquation_support0_chunk9 offset
  · exact candidateCatalogEquation_support0_chunk10 offset
  · exact candidateCatalogEquation_support0_chunk11 offset
  · exact candidateCatalogEquation_support0_chunk12 offset
  · exact candidateCatalogEquation_support0_chunk13 offset
  · exact candidateCatalogEquation_support0_chunk14 offset
  · exact candidateCatalogEquation_support0_chunk15 offset
  · exact candidateCatalogEquation_support0_chunk16 offset
  · exact candidateCatalogEquation_support0_chunk17 offset
  · exact candidateCatalogEquation_support0_chunk18 offset
  · exact candidateCatalogEquation_support0_chunk19 offset
  · exact candidateCatalogEquation_support2_chunk0 offset
  · exact candidateCatalogEquation_support2_chunk1 offset
  · exact candidateCatalogEquation_support2_chunk2 offset
  · exact candidateCatalogEquation_support2_chunk3 offset
  · exact candidateCatalogEquation_support2_chunk4 offset
  · exact candidateCatalogEquation_support2_chunk5 offset
  · exact candidateCatalogEquation_support2_chunk6 offset
  · exact candidateCatalogEquation_support2_chunk7 offset
  · exact candidateCatalogEquation_support2_chunk8 offset
  · exact candidateCatalogEquation_support2_chunk9 offset
  · exact candidateCatalogEquation_support2_chunk10 offset
  · exact candidateCatalogEquation_support2_chunk11 offset
  · exact candidateCatalogEquation_support2_chunk12 offset
  · exact candidateCatalogEquation_support2_chunk13 offset
  · exact candidateCatalogEquation_support2_chunk14 offset
  · exact candidateCatalogEquation_support2_chunk15 offset
  · exact candidateCatalogEquation_support2_chunk16 offset
  · exact candidateCatalogEquation_support2_chunk17 offset
  · exact candidateCatalogEquation_support2_chunk18 offset
  · exact candidateCatalogEquation_support2_chunk19 offset
  · exact candidateCatalogEquation_support7_chunk0 offset
  · exact candidateCatalogEquation_support7_chunk1 offset
  · exact candidateCatalogEquation_support7_chunk2 offset
  · exact candidateCatalogEquation_support7_chunk3 offset
  · exact candidateCatalogEquation_support7_chunk4 offset
  · exact candidateCatalogEquation_support7_chunk5 offset
  · exact candidateCatalogEquation_support7_chunk6 offset
  · exact candidateCatalogEquation_support7_chunk7 offset
  · exact candidateCatalogEquation_support7_chunk8 offset
  · exact candidateCatalogEquation_support7_chunk9 offset
  · exact candidateCatalogEquation_support7_chunk10 offset
  · exact candidateCatalogEquation_support7_chunk11 offset
  · exact candidateCatalogEquation_support7_chunk12 offset
  · exact candidateCatalogEquation_support7_chunk13 offset
  · exact candidateCatalogEquation_support7_chunk14 offset
  · exact candidateCatalogEquation_support7_chunk15 offset
  · exact candidateCatalogEquation_support7_chunk16 offset
  · exact candidateCatalogEquation_support7_chunk17 offset
  · exact candidateCatalogEquation_support7_chunk18 offset
  · exact candidateCatalogEquation_support7_chunk19 offset

theorem candidateCatalogEquation
    (kind : SupportKind) (rank : Fin 2000) :
    CandidateCatalogEquationAt kind rank := by
  let chunk : Fin 20 := Fin.ofNat 20 (rank.val / 100)
  let offset : Fin 100 := Fin.ofNat 100 rank.val
  have hrank : candidateEquationChunkIndex chunk offset = rank := by
    apply Fin.ext
    simp [candidateEquationChunkIndex, chunk, offset]
    omega
  rw [← hrank]
  exact candidateCatalogEquation_chunk kind chunk offset

theorem candidateCatalogEquation_selected
    (kind : SupportKind) (twisted : Bool) (a0 a1 a2 : Fin 10) :
    ∀ leftBlock rightBlock : Fin 3,
      leftBlock.val < rightBlock.val →
      ∀ left right : Fin 5,
        candidateMatrixColor kind twisted a0 a1 a2
            (blockVertex leftBlock left) (blockVertex rightBlock right) =
          catalogMatrixColor kind
            (candidateCatalogIndex kind twisted a0 a1 a2)
            (blockVertex leftBlock left) (blockVertex rightBlock right) := by
  have h := candidateCatalogEquation kind
    (candidateRankIndex twisted a0 a1 a2)
  simpa [CandidateCatalogEquationAt] using h

#print axioms candidateCatalogEquation_chunk
#print axioms candidateCatalogEquation
#print axioms candidateCatalogEquation_selected

end ProfileDUUUDegreeTenCatalogCandidateEquation61
end R4333
