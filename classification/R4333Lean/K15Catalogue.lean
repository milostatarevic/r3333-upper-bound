import R4333Lean.CriticalTemplateRestriction
import R4333Lean.K15DeficientCertificate

/-!
# Consequences of the certified K15 extension

Every good three-colouring of K15 extends canonically to K16.  Moreover,
once the K16 two-template catalogue is complete, vertex transitivity and
restriction make the corresponding K15 catalogue complete as well.
-/

namespace R4333

/-- The checked deficient-colour construction supplies the universal
`15 -> 16` extension theorem required by the attaching argument. -/
theorem everyThreeColoringExtends_15_16 : EveryThreeColoringExtends 15 16 := by
  intro c hc
  let d := extendCriticalK15 c hc
  refine ⟨d, extendCriticalK15_good_unconditional c hc, ?_⟩
  refine ⟨{
    vertex := Fin.castSuccEmb
    colors := Equiv.refl ThreeColor
    map_color := by
      intro u v huv
      simp [d, extendCriticalK15]
  }⟩

/-- Completeness descends from the K16 catalogue to its fixed K15
deletions.  The only nontrivial point is that the image of the newly added
vertex may be arbitrary; the checked template automorphisms move it to the
fixed deleted label. -/
theorem k15CriticalCatalogue_complete_of_k16
    (h16 : ThreeColorCatalogueComplete 16 k16CriticalCatalogue) :
    ThreeColorCatalogueComplete 15 k15CriticalCatalogue := by
  constructor
  · intro t ht
    simp [k15CriticalCatalogue] at ht
    rcases ht with rfl | rfl
    · exact k15Untwisted_good
    · exact k15Twisted_good
  · intro c hc
    let d := extendCriticalK15 c hc
    have hd : NoMonochromaticTriangle d :=
      extendCriticalK15_good_unconditional c hc
    obtain ⟨t, ht, ⟨e⟩⟩ := h16.2 d hd
    simp [k16CriticalCatalogue] at ht
    rcases ht with rfl | rfl
    · have e0 : WeakColorEquiv d (k16Template false) := by
        simpa [k16Template] using e
      let r := restrictCriticalK15WeakEquiv c hc false e0
      refine ⟨k15Untwisted, by simp [k15CriticalCatalogue], ⟨?_⟩⟩
      simpa [k15Template] using r
    · have e1 : WeakColorEquiv d (k16Template true) := by
        simpa [k16Template] using e
      let r := restrictCriticalK15WeakEquiv c hc true e1
      refine ⟨k15Twisted, by simp [k15CriticalCatalogue], ⟨?_⟩⟩
      simpa [k15Template] using r

#print axioms R4333.everyThreeColoringExtends_15_16
#print axioms R4333.k15CriticalCatalogue_complete_of_k16

end R4333
