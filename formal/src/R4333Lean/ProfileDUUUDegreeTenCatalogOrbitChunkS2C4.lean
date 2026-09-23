import R4333Lean.ProfileDUUUDegreeTenCatalogOrbits61

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem catalogNormalizerEquation_support2_chunk4 :
    ∀ offset : Fin 100,
      CatalogNormalizerEquationAt .support2 (catalogChunkIndex 4 offset) := by
  intro offset
  unfold CatalogNormalizerEquationAt
  fin_cases offset <;> decide +revert

#print axioms catalogNormalizerEquation_support2_chunk4

end ProfileDUUUDegreeTenCatalogOrbits61
end R4333
