import PricingC.ScopeReference

namespace PricingC
open R4333 SimpleGraph Finset

/-- Exact fixed-palette reference coordinates for an arbitrary good K16. -/
theorem some_reference (d : EdgeColoring (Fin 16) (Fin 3))
    (hd : NoMonochromaticTriangle d) :
    ∃ (i : Fin 72) (e : Fin 16 ≃ Fin 16),
      ∀ u v, u ≠ v → d (e u) (e v) = PricingG.Completion72.referenceColor i u v := by
  classical
  have hs := k16_colorGraph_isSRG d hd (0 : Fin 3)
  have hcard : Fintype.card ↥(clebschA (colorGraph d 0) 0) = 5 := by
    rw [Fintype.card_coe,card_clebschA _ hs]
  let points := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨i,e,_,_,he⟩ := ordered_anchor_reference d hd 0 points
  exact ⟨i,e,he⟩

def xorTranslation (a : Fin 16) : Fin 16 ≃ Fin 16 where
  toFun := xorIndex16 a
  invFun := xorIndex16 a
  left_inv := by revert a; decide
  right_inv := by revert a; decide

set_option maxRecDepth 100000 in
theorem xorTranslation_graph : ∀ (a u v : Fin 16),
    xorGraph.Adj (xorTranslation a u) (xorTranslation a v) ↔ xorGraph.Adj u v := by decide

 theorem xorTranslation_zero : ∀ a : Fin 16, xorTranslation a 0 = a := by decide
 theorem xorTranslation_self : ∀ a : Fin 16, xorTranslation a a = 0 := by decide

#print axioms some_reference
#print axioms xorTranslation_graph
end PricingC
