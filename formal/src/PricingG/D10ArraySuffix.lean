import PricingG.D10ArrayWord
namespace PricingG.D10ArraySuffix
open R4333 ProfileDDegreeTenMatrixCNF ProfileDDegreeTenMatrixLeafDataUUU2P15
open PricingG.D10NativeSuffixFast PricingG.D10CachedSuffix
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def pairCode : Array (Fin 9) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8]

def fastPair (i : Leaf) : Fin 9 := pairCode[i.val]!
theorem fastPair_eq (i : Leaf) : fastPair i=pairIndex i := by fin_cases i <;> rfl

def fastCoordinates (i : Leaf) : MatrixCoordinates 2 :=
  coordinatesFor (pairFirst (fastPair i)) (pairSecond (fastPair i))
theorem fastCoordinates_eq (i : Leaf) : fastCoordinates i=coordinates i := by
  simp only [fastCoordinates,fastPair_eq,coordinates]

theorem word_eq_ofFn (i : Leaf) : D10ArrayWord.word i=Array.ofFn (fastWord i) := by
  apply Array.ext
  · simp [D10ArrayWord.word_size]
  · intro j h₁ h₂
    have hj : j < 105 := by simpa [D10ArrayWord.word_size] using h₁
    simpa [getElem!_pos,h₁] using D10ArrayWord.word_get i ⟨j,hj⟩

def arraySuffix (i : Leaf) : Sat.Fmla :=
  cached
    (Array.ofFn fun p : Fin 15 => decide (p ∈ (fastCoordinates i).first.positions))
    (Array.ofFn fun p : Fin 15 => decide (p ∈ (fastCoordinates i).second.positions))
    (Array.ofFn (fastCoordinates i).vertex)
    (D10ArrayWord.word i)

theorem arraySuffix_eq (i : Leaf) : arraySuffix i =
    foreignSupportUnitClauses 2 selectedPosition (coordinates i) ++
    matrixUnitClauses (coordinates i) (matrix i) := by
  unfold arraySuffix
  rw [fastCoordinates_eq,word_eq_ofFn]
  exact fastSuffix_eq i

#print axioms arraySuffix_eq
end PricingG.D10ArraySuffix
