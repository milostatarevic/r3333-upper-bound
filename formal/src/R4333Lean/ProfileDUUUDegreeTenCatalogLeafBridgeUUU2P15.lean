import R4333Lean.ProfileDDegreeTenMatrixLeafDataUUU2P15
import R4333Lean.ProfileDUUUDegreeTenCatalogOrbits61

/-!
# The 82 block-two leaves are relabelled generic catalogue rows

The block-two matrix words use host colors `0,1,2`, whereas the reusable
block-zero catalogue uses `0,2,3`.  A fixed host-color permutation and small
within-five coordinate changes identify every one of the 82 literal words
with its advertised row of the existing 600-entry kernel catalogue.

This theorem is a finite data identity only.  It does not claim that the 82
rows cover all orbits for any support pair, and it makes no UNSAT claim.
-/

namespace R4333
namespace ProfileDUUUDegreeTenCatalogLeafBridgeUUU2P15

open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def catalogSupportKind : SupportRepresentative → SupportKind
  | .s0 => .support0
  | .s1 => .support2
  | .s4 => .support7

/-- Coordinate alignment for the first foreign K15 support. -/
def firstLocalAlignment : SupportRepresentative → Fin 5 → Fin 5
  | .s0 => ![0, 1, 2, 3, 4]
  | .s1 => ![0, 2, 1, 3, 4]
  | .s4 => ![0, 1, 2, 3, 4]

/-- Coordinate alignment for the second foreign K15 support. -/
def secondLocalAlignment : SupportRepresentative → Fin 5 → Fin 5
  | .s0 => ![0, 1, 2, 3, 4]
  | .s1 => ![0, 1, 2, 4, 3]
  | .s4 => ![0, 4, 1, 2, 3]

theorem firstLocalAlignment_bijective (support : SupportRepresentative) :
    Function.Bijective (firstLocalAlignment support) := by
  cases support <;> decide

theorem secondLocalAlignment_bijective (support : SupportRepresentative) :
    Function.Bijective (secondLocalAlignment support) := by
  cases support <;> decide

def alignedCatalogVertex (first second : SupportRepresentative)
    (vertex : Fin 15) : Fin 15 :=
  if hfree : vertex.val < 5 then vertex
  else if hfirst : vertex.val < 10 then
    ⟨5 + (firstLocalAlignment first
      ⟨vertex.val - 5, by omega⟩).val, by omega⟩
  else
    ⟨10 + (secondLocalAlignment second
      ⟨vertex.val - 10, by omega⟩).val, by omega⟩

theorem alignedCatalogVertex_bijective
    (first second : SupportRepresentative) :
    Function.Bijective (alignedCatalogVertex first second) := by
  cases first <;> cases second <;> decide

/-- Host-color permutation from the reusable block-zero convention to the
block-two convention: `0↦0, 1↦3, 2↦1, 3↦2`. -/
def catalogToBlockTwoColor : Fin 4 → Fin 4 := ![0, 3, 1, 2]

theorem catalogToBlockTwoColor_bijective :
    Function.Bijective catalogToBlockTwoColor := by
  decide

/-- Row number after applying the pair-specific coordinate alignment.  Most
rows retain the discovery index.  Ten rows move because the local alignment
itself acts nontrivially on the labelled 600-row catalogue. -/
def alignedCatalogRowIndex : Leaf → Fin 600 :=
  ![0, 1, 8, 12, 13, 20, 24, 25, 26, 27, 40, 68, 75, 100, 101, 113,
    0, 1, 4, 8, 9, 20, 24, 25, 26, 27, 32, 33, 48, 100, 101, 104,
    0, 24, 25, 100,
    0, 4, 5, 20, 32, 36, 37, 48, 52, 53, 60, 80, 81, 88, 92, 93,
    0, 4, 5, 12, 13, 24, 28, 36, 37, 44, 64, 80, 81, 84, 88, 89,
    4, 5, 24, 80,
    0, 1, 13, 45,
    0, 1, 4, 45,
    0, 45]

def CatalogLeafEquation (leaf : Leaf) : Prop :=
  let pair := pairIndex leaf
  let first := pairFirst pair
  let second := pairSecond pair
  let kind := catalogSupportKind first
  let row := alignedCatalogRowIndex leaf
  ∀ left right : Fin 15, left ≠ right →
    matrix leaf left right =
      catalogToBlockTwoColor
        (catalogMatrixColor kind row
          (alignedCatalogVertex first second left)
          (alignedCatalogVertex first second right))

theorem catalogLeafEquation_all : ∀ leaf : Leaf, CatalogLeafEquation leaf := by
  intro leaf
  unfold CatalogLeafEquation
  fin_cases leaf <;> decide

theorem matrix_eq_alignedCatalog
    (leaf : Leaf) (left right : Fin 15) (hne : left ≠ right) :
    let pair := pairIndex leaf
    let first := pairFirst pair
    let second := pairSecond pair
    matrix leaf left right =
      catalogToBlockTwoColor
        (catalogMatrixColor (catalogSupportKind first)
          (alignedCatalogRowIndex leaf)
          (alignedCatalogVertex first second left)
          (alignedCatalogVertex first second right)) := by
  exact catalogLeafEquation_all leaf left right hne

#print axioms alignedCatalogVertex_bijective
#print axioms catalogLeafEquation_all
#print axioms matrix_eq_alignedCatalog

end ProfileDUUUDegreeTenCatalogLeafBridgeUUU2P15
end R4333
