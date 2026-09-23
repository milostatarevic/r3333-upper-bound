import R4333Lean.ProfileDUUUDegreeTenCatalogCompletenessData61

/-!
# Candidate-to-catalogue equation

This module packages the remaining finite statement: each one of the 2000
color-preserving K15 candidates has the cross-block matrix stored at its
displayed catalogue index.  The bounded statement is split into independent
100-candidate certificates in subsequent modules.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogCandidateEquation61

open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogCompletenessData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def candidateTwistedAt (rank : Fin 2000) : Bool :=
  if rank.val < 1000 then false else true

def candidateActionZeroAt (rank : Fin 2000) : Fin 10 :=
  Fin.ofNat 10 ((rank.val % 1000) / 100)

def candidateActionOneAt (rank : Fin 2000) : Fin 10 :=
  Fin.ofNat 10 ((rank.val % 100) / 10)

def candidateActionTwoAt (rank : Fin 2000) : Fin 10 :=
  Fin.ofNat 10 (rank.val % 10)

def candidateRankIndex (twisted : Bool) (a0 a1 a2 : Fin 10) : Fin 2000 :=
  ⟨candidateRank twisted a0 a1 a2, candidateRank_lt twisted a0 a1 a2⟩

@[simp] theorem candidateTwistedAt_rankIndex
    (twisted : Bool) (a0 a1 a2 : Fin 10) :
    candidateTwistedAt (candidateRankIndex twisted a0 a1 a2) = twisted := by
  cases twisted <;>
    simp [candidateTwistedAt, candidateRankIndex, candidateRank] <;> omega

@[simp] theorem candidateActionZeroAt_rankIndex
    (twisted : Bool) (a0 a1 a2 : Fin 10) :
    candidateActionZeroAt (candidateRankIndex twisted a0 a1 a2) = a0 := by
  apply Fin.ext
  cases twisted <;>
    simp [candidateActionZeroAt, candidateRankIndex, candidateRank] <;> omega

@[simp] theorem candidateActionOneAt_rankIndex
    (twisted : Bool) (a0 a1 a2 : Fin 10) :
    candidateActionOneAt (candidateRankIndex twisted a0 a1 a2) = a1 := by
  apply Fin.ext
  cases twisted <;>
    simp [candidateActionOneAt, candidateRankIndex, candidateRank] <;> omega

@[simp] theorem candidateActionTwoAt_rankIndex
    (twisted : Bool) (a0 a1 a2 : Fin 10) :
    candidateActionTwoAt (candidateRankIndex twisted a0 a1 a2) = a2 := by
  apply Fin.ext
  cases twisted <;>
    simp [candidateActionTwoAt, candidateRankIndex, candidateRank] <;> omega

def CandidateCatalogEquationAt (kind : SupportKind) (rank : Fin 2000) : Prop :=
  let twisted := candidateTwistedAt rank
  let a0 := candidateActionZeroAt rank
  let a1 := candidateActionOneAt rank
  let a2 := candidateActionTwoAt rank
  ∀ leftBlock rightBlock : Fin 3,
    leftBlock.val < rightBlock.val →
    ∀ left right : Fin 5,
      candidateMatrixColor kind twisted a0 a1 a2
          (blockVertex leftBlock left) (blockVertex rightBlock right) =
        catalogMatrixColor kind (candidateCatalogIndex kind twisted a0 a1 a2)
          (blockVertex leftBlock left) (blockVertex rightBlock right)

def candidateEquationChunkIndex (chunk : Fin 20) (offset : Fin 100) : Fin 2000 :=
  Fin.ofNat 2000 (100 * chunk.val + offset.val)

end ProfileDUUUDegreeTenCatalogCandidateEquation61
end R4333
