import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

open ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem normalizerEquation_pair6_chunk4 :
    ∀ offset : Fin 100,
      NormalizerEquationAt 6 (catalogChunkIndex 4 offset) := by
  intro offset
  unfold NormalizerEquationAt
  fin_cases offset <;> decide +revert

#print axioms normalizerEquation_pair6_chunk4

end ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
end R4333
