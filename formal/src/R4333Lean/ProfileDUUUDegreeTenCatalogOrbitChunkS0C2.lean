import R4333Lean.ProfileDUUUDegreeTenCatalogOrbits61

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem catalogNormalizerEquation_support0_chunk2 :
    ∀ offset : Fin 100,
      CatalogNormalizerEquationAt .support0 (catalogChunkIndex 2 offset) := by
  intro offset
  unfold CatalogNormalizerEquationAt
  fin_cases offset <;> decide +revert

#print axioms catalogNormalizerEquation_support0_chunk2

end ProfileDUUUDegreeTenCatalogOrbits61
end R4333
