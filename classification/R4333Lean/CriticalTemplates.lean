import R4333Lean.ThreeColorCatalogue

/-!
# Explicit critical `K16` and `K15` three-colourings

These are the two historical representatives, encoded directly and checked
inside Lean.  Completeness is deliberately *not* asserted here; that is the
separate certificate problem.
-/

namespace R4333

/-- Index the XOR difference of two four-bit vertex labels. -/
def xorIndex16 (u v : Fin 16) : Fin 16 :=
  ⟨(u.val ^^^ v.val) % 16, Nat.mod_lt _ (by decide)⟩

/-- The three five-element difference classes of the GF(16) representative.
Index zero is the irrelevant diagonal value. -/
def untwistedDifferenceColor : Fin 16 → ThreeColor :=
  ![0, 0, 1, 1, 2, 2, 2, 1, 0, 2, 0, 1, 0, 1, 2, 0]

/-- The translation-invariant critical coloring on sixteen vertices. -/
def k16Untwisted : EdgeColoring (Fin 16) ThreeColor where
  color u v := untwistedDifferenceColor (xorIndex16 u v)
  color_symm u v := by
    congr 1
    apply Fin.ext
    simp only [xorIndex16, Fin.val_mk]
    exact congrArg (· % 16) (Nat.xor_comm u.val v.val)

/-- Canonical integer code of an unordered pair of vertices. -/
def unorderedPairCode16 (u v : Fin 16) : Nat :=
  min u.val v.val * 16 + max u.val v.val

/-- The sixteen-edge trade converting the untwisted representative into the
second critical type. -/
def k16TradeCodes : Finset Nat :=
  {21, 22, 28, 31, 37, 38, 44, 47, 88, 91, 104, 107, 140, 143, 188, 191}

/-- Swap colors one and two, fixing color zero. -/
def swapOneTwo : ThreeColor → ThreeColor := ![0, 2, 1]

/-- The switched, or twisted, critical coloring. -/
def k16Twisted : EdgeColoring (Fin 16) ThreeColor where
  color u v :=
    if unorderedPairCode16 u v ∈ k16TradeCodes then
      swapOneTwo (k16Untwisted u v)
    else k16Untwisted u v
  color_symm u v := by
    have hcode : unorderedPairCode16 u v = unorderedPairCode16 v u := by
      simp only [unorderedPairCode16, min_comm u.val v.val,
        max_comm u.val v.val]
    rw [hcode]
    simp only [k16Untwisted.color_symm]

/-- Lean directly checks all 560 triples of the untwisted template. -/
theorem k16Untwisted_good : NoMonochromaticTriangle k16Untwisted := by
  simp only [NoMonochromaticTriangle, PairwiseDistinct,
    HomogeneousTriangle]
  decide

/-- Lean directly checks all 560 triples of the twisted template. -/
theorem k16Twisted_good : NoMonochromaticTriangle k16Twisted := by
  simp only [NoMonochromaticTriangle, PairwiseDistinct,
    HomogeneousTriangle]
  decide

/-- Delete the last vertex from the untwisted template. -/
def k15Untwisted : EdgeColoring (Fin 15) ThreeColor :=
  pullbackColoring k16Untwisted (Fin.castLE (by omega))

/-- Delete the last vertex from the twisted template. -/
def k15Twisted : EdgeColoring (Fin 15) ThreeColor :=
  pullbackColoring k16Twisted (Fin.castLE (by omega))

theorem k15Untwisted_good : NoMonochromaticTriangle k15Untwisted :=
  noMono_pullback k16Untwisted _ (Fin.castLE_injective (by omega))
    k16Untwisted_good

theorem k15Twisted_good : NoMonochromaticTriangle k15Twisted :=
  noMono_pullback k16Twisted _ (Fin.castLE_injective (by omega))
    k16Twisted_good

/-- The concrete two-entry lists whose completeness will be supplied by
checked finite evidence. -/
def k16CriticalCatalogue : List (EdgeColoring (Fin 16) ThreeColor) :=
  [k16Untwisted, k16Twisted]

def k15CriticalCatalogue : List (EdgeColoring (Fin 15) ThreeColor) :=
  [k15Untwisted, k15Twisted]

#print axioms R4333.k16Untwisted_good
#print axioms R4333.k16Twisted_good
#print axioms R4333.k15Untwisted_good
#print axioms R4333.k15Twisted_good

end R4333
