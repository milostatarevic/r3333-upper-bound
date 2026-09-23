import R4333Lean.ProfileDUUUDegreeTenCatalogOrbits61

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem catalogNormalizerEquation_support7_chunk5 :
    ∀ offset : Fin 100,
      CatalogNormalizerEquationAt .support7 (catalogChunkIndex 5 offset) := by
  intro offset
  unfold CatalogNormalizerEquationAt
  fin_cases offset <;> decide +revert

#print axioms catalogNormalizerEquation_support7_chunk5

end ProfileDUUUDegreeTenCatalogOrbits61
end R4333
