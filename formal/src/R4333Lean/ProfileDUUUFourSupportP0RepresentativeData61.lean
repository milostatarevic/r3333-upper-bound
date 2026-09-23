import R4333Lean.ProfileDUUUFourSupportP0SupportPair61

/-!
# Exact representative data for the UUU/block-zero/position-zero quotient

The authoritative discovery quotient has three normalized support pairs and
36 restored-`K15` matrix representatives.  This module records precisely
those representatives, packed with two bits per one of the 91 edges of
`Fin 14` in lexicographic order.  Packing is only storage; all public colour
lookups reduce inside Lean.

No orbit-completeness or unsatisfiability assertion is made here.
-/

namespace R4333
namespace ProfileDUUUFourSupportP0RepresentativeData61

open ProfileDUUUDegreeTenCatalogOrbits61

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev SupportPair := Fin 3
abbrev MatrixSelector := Fin 36

def pairSupportKind : SupportPair → SupportKind :=
  ![.support0, .support2, .support7]

def pairFirstSupportIndex (pair : SupportPair) : Fin 11 :=
  supportIndex (pairSupportKind pair)

def matrixPair (selector : MatrixSelector) : SupportPair :=
  if selector.val < 16 then 0
  else if selector.val < 32 then 1
  else 2

def matrixLocalIndex (selector : MatrixSelector) : Nat :=
  if selector.val < 16 then selector.val
  else if selector.val < 32 then selector.val - 16
  else selector.val - 32

def matrixRawCatalogIndexTable : Array Nat :=
  #[0, 2, 40, 41, 42, 43, 48, 49, 52, 53, 200, 202, 321, 482, 493, 682,
    0, 1, 2, 3, 9, 12, 13, 160, 162, 200, 202, 522, 523, 532, 533, 682,
    0, 2, 80, 89]

def matrixRawCatalogIndex (selector : MatrixSelector) : Nat :=
  (matrixRawCatalogIndexTable[selector.val]?).getD 0

/-- The first selector atom is DIMACS variable `6000055`, hence Lean atom
`6000054`.  The three pair atoms are followed by the 36 matrix atoms. -/
def firstSelectorAtom : Nat := 6000054

def pairSelectorAtom (pair : SupportPair) : Nat :=
  firstSelectorAtom + pair.val

def matrixSelectorAtom (selector : MatrixSelector) : Nat :=
  firstSelectorAtom + 3 + selector.val

theorem lastMatrixSelectorAtom_eq :
    matrixSelectorAtom (Fin.last 35) = 6000092 := by decide

/-! ## Packed representative matrices -/

def representativeByteTable : Array (Array Nat) := #[
  #[58, 226, 248, 172, 176, 50, 63, 34, 179, 172, 12, 206, 188, 227, 227, 11, 40, 255, 184, 172, 35, 42, 32],
  #[58, 226, 248, 236, 136, 204, 46, 172, 204, 58, 188, 192, 188, 227, 227, 11, 40, 255, 184, 172, 35, 42, 32],
  #[58, 178, 200, 47, 43, 50, 47, 242, 176, 58, 240, 194, 172, 207, 195, 46, 140, 254, 142, 142, 35, 42, 32],
  #[58, 178, 200, 175, 224, 50, 239, 194, 176, 35, 242, 194, 60, 250, 227, 56, 232, 243, 142, 236, 34, 42, 32],
  #[58, 178, 200, 175, 200, 195, 206, 138, 204, 131, 190, 192, 172, 207, 195, 46, 140, 254, 142, 142, 35, 42, 32],
  #[58, 178, 200, 175, 11, 195, 46, 184, 204, 184, 188, 192, 60, 250, 227, 56, 232, 243, 142, 236, 34, 42, 32],
  #[58, 178, 248, 44, 43, 194, 47, 248, 140, 50, 50, 206, 172, 243, 227, 11, 44, 251, 232, 236, 34, 42, 32],
  #[58, 178, 248, 44, 43, 50, 47, 248, 176, 58, 48, 206, 172, 252, 195, 46, 236, 248, 232, 190, 32, 42, 32],
  #[58, 178, 248, 172, 224, 194, 207, 202, 140, 43, 48, 206, 188, 236, 195, 46, 232, 252, 232, 190, 32, 42, 32],
  #[58, 178, 248, 172, 224, 50, 207, 202, 176, 35, 50, 206, 188, 227, 227, 11, 40, 255, 232, 236, 34, 42, 32],
  #[58, 58, 248, 44, 163, 50, 47, 56, 179, 58, 12, 206, 172, 252, 51, 46, 248, 50, 235, 59, 34, 42, 32],
  #[58, 58, 248, 172, 224, 204, 206, 168, 204, 35, 190, 192, 172, 252, 51, 46, 248, 50, 235, 59, 34, 42, 32],
  #[58, 43, 200, 175, 176, 195, 174, 131, 204, 136, 191, 192, 60, 250, 179, 35, 176, 187, 227, 250, 32, 42, 32],
  #[186, 224, 200, 239, 136, 50, 143, 206, 176, 58, 240, 194, 204, 238, 163, 15, 140, 190, 227, 59, 34, 42, 32],
  #[186, 224, 248, 236, 136, 50, 143, 236, 176, 58, 48, 206, 204, 238, 163, 60, 236, 184, 47, 163, 35, 42, 32],
  #[186, 200, 248, 236, 160, 50, 143, 44, 179, 58, 12, 206, 60, 238, 163, 60, 248, 242, 142, 172, 35, 42, 32],
  #[58, 232, 200, 47, 142, 50, 175, 204, 176, 46, 240, 50, 163, 207, 48, 58, 179, 187, 227, 59, 34, 42, 32],
  #[58, 232, 200, 175, 176, 50, 175, 195, 176, 139, 240, 50, 51, 250, 160, 15, 59, 62, 187, 59, 34, 42, 32],
  #[58, 232, 200, 175, 50, 195, 142, 163, 204, 131, 190, 48, 163, 207, 48, 58, 179, 187, 227, 59, 34, 42, 32],
  #[58, 232, 200, 175, 14, 195, 46, 172, 204, 44, 190, 48, 51, 250, 160, 15, 59, 62, 187, 59, 34, 42, 32],
  #[58, 232, 248, 44, 142, 50, 47, 236, 176, 46, 48, 62, 163, 252, 176, 35, 179, 187, 47, 163, 35, 42, 32],
  #[58, 232, 248, 172, 176, 194, 143, 227, 140, 43, 48, 62, 179, 236, 160, 51, 179, 187, 47, 163, 35, 42, 32],
  #[58, 232, 248, 172, 176, 50, 143, 227, 176, 139, 48, 62, 179, 227, 160, 60, 251, 50, 187, 163, 35, 42, 32],
  #[58, 184, 248, 172, 224, 50, 191, 8, 179, 56, 14, 62, 179, 227, 160, 60, 251, 50, 235, 227, 34, 42, 32],
  #[58, 184, 248, 236, 34, 204, 46, 184, 204, 46, 188, 48, 179, 227, 160, 60, 251, 50, 235, 227, 34, 42, 32],
  #[58, 172, 248, 44, 202, 50, 239, 2, 179, 194, 14, 62, 163, 252, 176, 35, 179, 190, 47, 227, 34, 42, 32],
  #[58, 172, 248, 172, 11, 204, 142, 178, 204, 139, 188, 48, 163, 252, 176, 35, 179, 190, 47, 227, 34, 42, 32],
  #[186, 176, 200, 239, 34, 50, 143, 242, 176, 46, 240, 50, 195, 238, 48, 58, 235, 243, 142, 142, 35, 42, 32],
  #[186, 176, 200, 239, 10, 195, 14, 186, 204, 142, 188, 48, 227, 248, 160, 15, 143, 254, 142, 236, 34, 42, 32],
  #[186, 176, 248, 236, 34, 194, 15, 250, 140, 44, 50, 62, 227, 203, 176, 44, 235, 252, 232, 236, 34, 42, 32],
  #[186, 176, 248, 236, 34, 50, 15, 250, 176, 46, 48, 62, 195, 238, 176, 35, 43, 255, 232, 190, 32, 42, 32],
  #[186, 50, 248, 236, 160, 50, 15, 58, 179, 46, 12, 62, 51, 238, 224, 11, 43, 63, 235, 59, 34, 42, 32],
  #[58, 232, 248, 44, 142, 50, 239, 32, 179, 226, 12, 62, 163, 60, 188, 227, 143, 139, 47, 172, 35, 42, 32],
  #[58, 232, 248, 172, 131, 204, 142, 163, 204, 139, 188, 48, 163, 60, 188, 227, 143, 139, 47, 172, 35, 42, 32],
  #[58, 172, 200, 47, 202, 50, 175, 204, 176, 14, 242, 50, 163, 15, 60, 250, 239, 136, 227, 236, 34, 42, 32],
  #[58, 172, 248, 44, 202, 50, 47, 206, 176, 14, 50, 62, 163, 60, 188, 227, 143, 142, 47, 236, 34, 42, 32]
]

def matrixEdgeIndex (u v : Fin 14) : Nat :=
  let left := min u.val v.val
  let right := max u.val v.val
  left * (27 - left) / 2 + (right - left - 1)

def representativeMatrixColor (selector : MatrixSelector)
    (u v : Fin 14) : Fin 4 :=
  let edge := matrixEdgeIndex u v
  let row := (representativeByteTable[selector.val]?).getD #[]
  let byte := (row[edge / 4]?).getD 0
  Fin.ofNat 4 ((byte >>> (2 * (edge % 4))) % 4)

def representativeMatrix (selector : MatrixSelector) :
    EdgeColoring (Fin 14) (Fin 4) where
  color := representativeMatrixColor selector
  color_symm := by
    intro u v
    simp [representativeMatrixColor, matrixEdgeIndex, min_comm, max_comm]

/-! ## Physical `Fin 50` coordinates: free four, U15 five, U16 five -/

def physicalVertex : SupportKind → Fin 14 → ProfileDFourRowCNF.TotalVertex
  | .support0 => ![0, 1, 2, 3, 19, 20, 23, 27, 33, 34, 35, 38, 42, 48]
  | .support2 => ![0, 1, 2, 3, 19, 25, 27, 28, 31, 34, 35, 38, 42, 48]
  | .support7 => ![0, 1, 2, 3, 21, 23, 27, 31, 32, 34, 35, 38, 42, 48]

theorem physicalVertex_injective (kind : SupportKind) :
    Function.Injective (physicalVertex kind) := by
  cases kind <;> decide

theorem physicalVertex_strictMono (kind : SupportKind) :
    StrictMono (physicalVertex kind) := by
  cases kind <;> decide

theorem representativeByteTable_size :
    representativeByteTable.size = 36 := by decide

theorem representativeByteRow_size (selector : MatrixSelector) :
    ((representativeByteTable[selector.val]?).getD #[]).size = 23 := by
  fin_cases selector <;> decide

theorem matrixPair_partition (selector : MatrixSelector) :
    (matrixPair selector = 0 ∧ selector.val < 16) ∨
    (matrixPair selector = 1 ∧ 16 ≤ selector.val ∧ selector.val < 32) ∨
    (matrixPair selector = 2 ∧ 32 ≤ selector.val) := by
  fin_cases selector <;> decide

#print axioms representativeByteRow_size
#print axioms physicalVertex_injective
#print axioms physicalVertex_strictMono
#print axioms matrixPair_partition

end ProfileDUUUFourSupportP0RepresentativeData61
end R4333
