import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMaps61

namespace R4333
namespace ProfileDUUUDegreeTenCatalogLocalMaps61

open ProfileDUUUDegreeTenCatalogCompletenessData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem compatibleMap_complete_support2_false_group2
    (perm : Equiv.Perm (Fin 5))
    (hmap : IsCompatiblePerm .support2 false 2 perm) :
    ∃ action : Fin 10,
      ∀ position, perm position =
        compatibleMap .support2 false 2 action position := by
  fin_cases perm <;> (revert hmap; unfold IsCompatiblePerm; decide)

#print axioms compatibleMap_complete_support2_false_group2

end ProfileDUUUDegreeTenCatalogLocalMaps61
end R4333
