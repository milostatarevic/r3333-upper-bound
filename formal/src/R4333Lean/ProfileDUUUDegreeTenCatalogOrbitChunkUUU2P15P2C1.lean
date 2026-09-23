import R4333Lean.ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

namespace R4333
namespace ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15

open ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem normalizerEquation_pair2_chunk1 :
    ∀ offset : Fin 100,
      NormalizerEquationAt 2 (catalogChunkIndex 1 offset) := by
  intro offset
  unfold NormalizerEquationAt
  fin_cases offset <;> decide +revert

#print axioms normalizerEquation_pair2_chunk1

end ProfileDUUUDegreeTenCatalogOrbitDataUUU2P15
end R4333
