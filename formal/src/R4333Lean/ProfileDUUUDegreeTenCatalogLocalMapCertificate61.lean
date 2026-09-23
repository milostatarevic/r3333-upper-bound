import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS0F0G0
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS0F0G1
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS0F0G2
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS0F1G0
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS0F1G1
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS0F1G2
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS2F0G0
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS2F0G1
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS2F0G2
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS2F1G0
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS2F1G1
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS2F1G2
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS7F0G0
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS7F0G1
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS7F0G2
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS7F1G0
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS7F1G1
import R4333Lean.ProfileDUUUDegreeTenCatalogLocalMapCompleteS7F1G2

/-!
# Certified completeness of the ten local maps

The eighteen small finite certificates are aggregated here.  In particular,
an arbitrary bijective local map preserving the internal five-vertex row-zero
pattern is one of the ten displayed maps.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogLocalMaps61

open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogCompletenessData61

theorem compatiblePerm_complete
    (kind : SupportKind) (twisted : Bool) (group : Fin 3)
    (perm : Equiv.Perm (Fin 5))
    (hmap : IsCompatiblePerm kind twisted group perm) :
    ∃ action : Fin 10,
      ∀ position, perm position =
        compatibleMap kind twisted group action position := by
  cases kind <;> cases twisted <;> fin_cases group
  · exact compatibleMap_complete_support0_false_group0 perm hmap
  · exact compatibleMap_complete_support0_false_group1 perm hmap
  · exact compatibleMap_complete_support0_false_group2 perm hmap
  · exact compatibleMap_complete_support0_true_group0 perm hmap
  · exact compatibleMap_complete_support0_true_group1 perm hmap
  · exact compatibleMap_complete_support0_true_group2 perm hmap
  · exact compatibleMap_complete_support2_false_group0 perm hmap
  · exact compatibleMap_complete_support2_false_group1 perm hmap
  · exact compatibleMap_complete_support2_false_group2 perm hmap
  · exact compatibleMap_complete_support2_true_group0 perm hmap
  · exact compatibleMap_complete_support2_true_group1 perm hmap
  · exact compatibleMap_complete_support2_true_group2 perm hmap
  · exact compatibleMap_complete_support7_false_group0 perm hmap
  · exact compatibleMap_complete_support7_false_group1 perm hmap
  · exact compatibleMap_complete_support7_false_group2 perm hmap
  · exact compatibleMap_complete_support7_true_group0 perm hmap
  · exact compatibleMap_complete_support7_true_group1 perm hmap
  · exact compatibleMap_complete_support7_true_group2 perm hmap

theorem compatibleMap_complete
    (kind : SupportKind) (twisted : Bool) (group : Fin 3)
    (map : Fin 5 → Fin 5)
    (hmap : IsCompatibleMap kind twisted group map) :
    ∃ action : Fin 10,
      ∀ position, map position =
        compatibleMap kind twisted group action position := by
  let perm : Equiv.Perm (Fin 5) := Equiv.ofBijective map hmap.1
  have hperm : IsCompatiblePerm kind twisted group perm := by
    intro left right hne
    exact hmap.2 left right hne
  obtain ⟨action, ha⟩ := compatiblePerm_complete kind twisted group perm hperm
  exact ⟨action, ha⟩

#print axioms compatiblePerm_complete
#print axioms compatibleMap_complete

end ProfileDUUUDegreeTenCatalogLocalMaps61
end R4333
