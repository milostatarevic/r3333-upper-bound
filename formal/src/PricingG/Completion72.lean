import PricingG.Completion72Transport

namespace PricingG.Completion72
open R4333

/-- Exhaustiveness of the exact retained table for arbitrary good colorings
in its physical XOR coordinates. No independent matrix assumption is present. -/
theorem reference_exhaustive
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d)
    (hzero : ∀ u v, u ≠ v → (d u v = 0 ↔ xorClebsch u v = true)) :
    ∃ i : Fin 72, ∀ u v, u ≠ v → d u v = referenceColor i u v := by
  let d' := relabelVertices d legacyLabels.symm
  have hd' : NoMonochromaticTriangle d' := noMono_relabelVertices d legacyLabels.symm hd
  have hz' : HasCanonicalClebschZero d' := by
    intro u v huv
    change d (legacyLabels.symm u) (legacyLabels.symm v) = 0 ↔ _
    rw [hzero _ _ (legacyLabels.symm.injective.ne huv)]
    have h := fixed_color_transport (legacyLabels.symm u) (legacyLabels.symm v)
    change canonicalClebschRed (legacyLabels (legacyLabels.symm u)).val
      (legacyLabels (legacyLabels.symm v)).val = _ at h
    exact Iff.of_eq (by simpa only [Equiv.apply_symm_apply] using congrArg (fun b => b = true) h.symm)
  obtain ⟨j, hj⟩ := exists_clebschDecompositionAt_of_mem (clebschCompletionBits_mem d' hd' hz')
  refine ⟨legacyToReference j, ?_⟩
  intro u v huv
  have he := eq_canonicalClebschCompletion_of_bits d' hz' _ hj.symm
    (legacyLabels u) (legacyLabels v) (legacyLabels.injective.ne huv)
  have he' : d u v = canonicalClebschCompletion (clebschDecompositionAt j)
      (toLegacyLabels u) (toLegacyLabels v) := by
    change d (legacyLabels.symm (legacyLabels u)) (legacyLabels.symm (legacyLabels v)) = _ at he
    simp only [Equiv.symm_apply_apply] at he
    simpa only [legacyLabels_apply] using he
  exact he'.trans (reference_row_transport j u v)

#print axioms reference_row_transport
#print axioms reference_exhaustive
end PricingG.Completion72
