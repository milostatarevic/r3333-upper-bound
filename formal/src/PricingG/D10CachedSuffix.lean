import PricingG.D10SuffixRepresentation
namespace PricingG.D10CachedSuffix
open R4333
open ProfileDDegreeTenMatrixCNF ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDHighOwnFiveSupportC5CNF
open PricingG.D10NativeSuffixFast
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def cached (first second : Array Bool) (vertices : Array TotalVertex)
    (word : Array (Fin 3)) : Sat.Fmla :=
  ((List.finRange 15).map fun p => [supportLiteral
      (selectedToForeignAtom 2 selectedPosition 0 p) first[p.val]!]) ++
  ((List.finRange 15).map fun p => [supportLiteral
      (selectedToForeignAtom 2 selectedPosition 1 p) second[p.val]!]) ++
  crossGroupMatrixPairs.map fun pair =>
    let left := matrixIndex pair.1
    let right := matrixIndex pair.2
    [Sat.Literal.pos (OutsideDegreeCapCNF.outsideIncidentEdgeAtom
      vertices[left.val]! vertices[right.val]!
      (if left=right then 0 else Fin.castLE (show 3 ≤ 4 by omega)
        word[(Fin.ofNat 105 (edgeIndex left right)).val]!))]

def fastSuffix (i : Leaf) : Sat.Fmla :=
  cached
    (Array.ofFn fun p : Fin 15 => decide (p ∈ (coordinates i).first.positions))
    (Array.ofFn fun p : Fin 15 => decide (p ∈ (coordinates i).second.positions))
    (Array.ofFn (coordinates i).vertex)
    (Array.ofFn (fastWord i))

theorem fastSuffix_eq (i : Leaf) : fastSuffix i =
    foreignSupportUnitClauses 2 selectedPosition (coordinates i) ++
    matrixUnitClauses (coordinates i) (matrix i) := by
  simp only [fastSuffix,cached,foreignSupportUnitClauses,matrixUnitClauses]
  simp [ProfileDTripleJoinReduction.blockSize,ProfileDHighOwnForeignC5Skeleton61.firstForeignBlock,
    ProfileDHighOwnForeignC5Skeleton61.secondForeignBlock,
    matrix,matrixTable,fastWord_eq,List.append_assoc,
    getElem!_pos, Nat.mod_lt _ (by omega : 0 < 105)]
  rfl

#print axioms fastSuffix_eq
end PricingG.D10CachedSuffix
