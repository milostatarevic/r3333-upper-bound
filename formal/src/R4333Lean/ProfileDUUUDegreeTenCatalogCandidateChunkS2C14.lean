import R4333Lean.ProfileDUUUDegreeTenCatalogCandidateEquation61

namespace R4333
namespace ProfileDUUUDegreeTenCatalogCandidateEquation61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem candidateCatalogEquation_support2_chunk14 :
    ∀ offset : Fin 100,
      CandidateCatalogEquationAt .support2
        (candidateEquationChunkIndex 14 offset) := by
  intro offset
  unfold CandidateCatalogEquationAt
  fin_cases offset <;> decide +revert

#print axioms candidateCatalogEquation_support2_chunk14

end ProfileDUUUDegreeTenCatalogCandidateEquation61
end R4333
