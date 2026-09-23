import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMaps61

namespace R4333
namespace ProfileDUUUDegreeTenCatalogLocalMaps61

open ProfileDUUUDegreeTenCatalogCompletenessData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem compatibleMap_complete_support0_true_group1
    (perm : Equiv.Perm (Fin 5))
    (hmap : IsCompatiblePerm .support0 true 1 perm) :
    ∃ action : Fin 10,
      ∀ position, perm position =
        compatibleMap .support0 true 1 action position := by
  fin_cases perm <;> (revert hmap; unfold IsCompatiblePerm; decide)

#print axioms compatibleMap_complete_support0_true_group1

end ProfileDUUUDegreeTenCatalogLocalMaps61
end R4333
