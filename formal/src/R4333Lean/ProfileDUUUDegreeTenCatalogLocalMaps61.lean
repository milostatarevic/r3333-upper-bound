import R4333Lean.ProfileDUUUDegreeTenCatalogCompletenessData61

/-!
# Complete ten-map classification inside each canonical K15 part

The compatible local maps are classified independently for each support,
template kind, and part.  The proof is a small finite check over maps on five
vertices; it does not enumerate K15 colorings.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogLocalMaps61

open SingleRootStarCNF
open CriticalK15PartitionClassification
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUDegreeTenCatalogCompletenessData61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Inverse lookup on each canonical part; values outside the selected part
are irrelevant and set to zero. -/
def canonicalPartPosition : Bool → Fin 3 → Fin 15 → Fin 5
  | false => ![![0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 4], ![0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 4, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 3, 4, 0, 0, 0]]
  | true => ![![0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 4], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 3, 4, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 4, 0, 0, 0, 0]]

@[simp] theorem canonicalPartPosition_vertex
    (twisted : Bool) (group : Fin 3) (position : Fin 5) :
    canonicalPartPosition twisted group
        (canonicalPartVertex twisted group position) = position := by
  cases twisted <;> fin_cases group <;> fin_cases position <;> decide

theorem canonicalPartVertex_mem
    (twisted : Bool) (group : Fin 3) (position : Fin 5) :
    canonicalPartVertex twisted group position ∈
      canonicalPart twisted group := by
  cases twisted <;> fin_cases group <;> fin_cases position <;>
    decide

theorem canonicalPartVertex_position_of_mem
    (twisted : Bool) (group : Fin 3) (vertex : Fin 15)
    (hmem : vertex ∈ canonicalPart twisted group) :
    canonicalPartVertex twisted group
      (canonicalPartPosition twisted group vertex) = vertex := by
  cases twisted <;> fin_cases group <;> fin_cases vertex <;>
    simp_all [canonicalPart, canonicalPartVertex, canonicalPartPosition,
      untwistedPartZero, untwistedPartOne, untwistedPartTwo,
      twistedPartZero, twistedPartOne, twistedPartTwo]

def IsCompatibleMap (kind : SupportKind) (twisted : Bool)
    (group : Fin 3) (map : Fin 5 → Fin 5) : Prop :=
  Function.Bijective map ∧
    ∀ left right : Fin 5, left ≠ right →
      canonicalPalette 1
          (k15Template twisted
            (canonicalPartVertex twisted group (map left))
            (canonicalPartVertex twisted group (map right))) =
        catalogMatrixColor kind 0
          (blockVertex group left) (blockVertex group right)

def IsCompatiblePerm (kind : SupportKind) (twisted : Bool)
    (group : Fin 3) (perm : Equiv.Perm (Fin 5)) : Prop :=
  ∀ left right : Fin 5, left ≠ right →
    canonicalPalette 1
        (k15Template twisted
          (canonicalPartVertex twisted group (perm left))
          (canonicalPartVertex twisted group (perm right))) =
      catalogMatrixColor kind 0
        (blockVertex group left) (blockVertex group right)

theorem compatibleMap_isCompatible
    (kind : SupportKind) (twisted : Bool)
    (group : Fin 3) (action : Fin 10) :
    IsCompatibleMap kind twisted group
      (compatibleMap kind twisted group action) := by
  unfold IsCompatibleMap
  constructor
  · cases kind <;> cases twisted <;> fin_cases group <;>
      fin_cases action <;> decide
  · intro left right hne
    cases kind <;> cases twisted <;> fin_cases group <;>
      fin_cases action <;> fin_cases left <;> fin_cases right <;>
      simp_all <;> decide

#print axioms canonicalPartVertex_position_of_mem
#print axioms compatibleMap_isCompatible

end ProfileDUUUDegreeTenCatalogLocalMaps61
end R4333
