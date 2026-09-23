import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

open ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem normalizerEquation_pair4_chunk0 :
    ∀ offset : Fin 100,
      NormalizerEquationAt 4 (catalogChunkIndex 0 offset) := by
  intro offset
  unfold NormalizerEquationAt
  fin_cases offset <;> decide +revert

#print axioms normalizerEquation_pair4_chunk0

end ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
end R4333
