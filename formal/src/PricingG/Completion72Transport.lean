import PricingG.Completion72Data

namespace PricingG.Completion72
open R4333

/-- The shared physical XOR labels used by the retained reference table. -/
def xorClebsch (u v : Fin 16) : Bool :=
  decide ((u.val ^^^ v.val) ∈ ([1, 2, 4, 8, 15] : List Nat))

def referenceIndex (u v : Fin 16) : Nat :=
  referenceEdges.idxOf (min u.val v.val, max u.val v.val)

/-- Literal reference row; the two remaining physical colors are distinguished. -/
def referenceColor (i : Fin 72) : EdgeColoring (Fin 16) ThreeColor where
  color u v := if u = v then 0 else if xorClebsch u v then 0
    else if (referenceMask i).testBit (referenceIndex u v) then 1 else 2
  color_symm u v := by
    by_cases huv : u = v
    · subst v; rfl
    · simp only [huv, Ne.symm huv, ↓reduceIte]
      have hx : xorClebsch u v = xorClebsch v u := by
        simp [xorClebsch, Nat.xor_comm]
      have hi : referenceIndex u v = referenceIndex v u := by
        simp [referenceIndex, min_comm, max_comm]
      rw [hx, hi]

private theorem labels_left_inverse : Function.LeftInverse fromLegacyLabels toLegacyLabels := by
  decide
private theorem labels_right_inverse : Function.RightInverse fromLegacyLabels toLegacyLabels := by
  decide

def legacyLabels : Fin 16 ≃ Fin 16 where
  toFun := toLegacyLabels
  invFun := fromLegacyLabels
  left_inv := labels_left_inverse
  right_inv := labels_right_inverse

@[simp] theorem legacyLabels_apply (u : Fin 16) : legacyLabels u = toLegacyLabels u := rfl
@[simp] theorem legacyLabels_symm_apply (u : Fin 16) :
    legacyLabels.symm u = fromLegacyLabels u := rfl

set_option maxRecDepth 100000 in
theorem fixed_color_transport : ∀ u v : Fin 16,
    canonicalClebschRed (toLegacyLabels u).val (toLegacyLabels v).val = xorClebsch u v := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every certificate row is exactly a reference row under one fixed vertex map.
This is literal equality with the palette unchanged, not isomorphism counting. -/
theorem reference_row_transport (i : Fin 72) : ∀ u v : Fin 16,
    canonicalClebschCompletion (clebschDecompositionAt i)
        (toLegacyLabels u) (toLegacyLabels v) = referenceColor (legacyToReference i) u v := by
  fin_cases i <;> decide


#print axioms reference_row_transport
end PricingG.Completion72
