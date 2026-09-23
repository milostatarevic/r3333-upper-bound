import PricingABD.PaletteSymmetry
import Ramsey61.ClassificationAdapter

namespace PricingABD.TemplateNormalization
open R4333 Finset

/-- Arbitrary goodK15 has a color-preserving literal-template realization.
The arbitrary catalogue palette is absorbed by a checked whole-template map. -/
theorem k15_color_preserving_complete (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ twisted : Bool, ∃ vertex : Fin 15 ≃ Fin 15,
      ∀ u v, u ≠ v → c (vertex u) (vertex v) = k15Template twisted u v := by
  obtain ⟨template,ht,⟨e⟩⟩ := k15CriticalCatalogue_complete.2 c hc
  simp [k15CriticalCatalogue] at ht
  rcases ht with ht | ht
  · subst template
    obtain ⟨a,ha⟩ := k15Template_fullPaletteSymmetry false e.colors
    refine ⟨false,a.trans e.vertex.symm,?_⟩
    intro u v huv
    have hmap := e.map_color (e.vertex.symm (a u)) (e.vertex.symm (a v))
      (e.vertex.symm.injective.ne (a.injective.ne huv))
    simp only [Equiv.apply_symm_apply] at hmap
    have h := ha u v huv
    change k15Untwisted (a u) (a v) = e.colors (k15Untwisted u v) at h
    rw [h] at hmap
    exact e.colors.injective hmap
  · subst template
    obtain ⟨a,ha⟩ := k15Template_fullPaletteSymmetry true e.colors
    refine ⟨true,a.trans e.vertex.symm,?_⟩
    intro u v huv
    have hmap := e.map_color (e.vertex.symm (a u)) (e.vertex.symm (a v))
      (e.vertex.symm.injective.ne (a.injective.ne huv))
    simp only [Equiv.apply_symm_apply] at hmap
    have h := ha u v huv
    change k15Twisted (a u) (a v) = e.colors (k15Twisted u v) at h
    rw [h] at hmap
    exact e.colors.injective hmap

theorem k16_color_preserving_complete (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ twisted : Bool, ∃ vertex : Fin 16 ≃ Fin 16,
      ∀ u v, u ≠ v → c (vertex u) (vertex v) = k16Template twisted u v := by
  obtain ⟨template,ht,⟨e⟩⟩ := k16CriticalCatalogue_complete.2 c hc
  simp [k16CriticalCatalogue] at ht
  rcases ht with ht | ht
  · subst template
    obtain ⟨a,ha⟩ := k16Template_fullPaletteSymmetry false e.colors
    refine ⟨false,a.trans e.vertex.symm,?_⟩
    intro u v huv
    have hmap := e.map_color (e.vertex.symm (a u)) (e.vertex.symm (a v))
      (e.vertex.symm.injective.ne (a.injective.ne huv))
    simp only [Equiv.apply_symm_apply] at hmap
    have h := ha u v huv
    change k16Untwisted (a u) (a v) = e.colors (k16Untwisted u v) at h
    rw [h] at hmap
    exact e.colors.injective hmap
  · subst template
    obtain ⟨a,ha⟩ := k16Template_fullPaletteSymmetry true e.colors
    refine ⟨true,a.trans e.vertex.symm,?_⟩
    intro u v huv
    have hmap := e.map_color (e.vertex.symm (a u)) (e.vertex.symm (a v))
      (e.vertex.symm.injective.ne (a.injective.ne huv))
    simp only [Equiv.apply_symm_apply] at hmap
    have h := ha u v huv
    change k16Twisted (a u) (a v) = e.colors (k16Twisted u v) at h
    rw [h] at hmap
    exact e.colors.injective hmap

/-- At order16the supplied root may always occupy15, with colors unchanged. -/
theorem k16_rooted_color_preserving_complete (c : EdgeColoring (Fin 16) ThreeColor)
    (hc : NoMonochromaticTriangle c) (root : Fin 16) :
    ∃ twisted : Bool, ∃ vertex : Fin 16 ≃ Fin 16, vertex 15 = root ∧
      ∀ u v, u ≠ v → c (vertex u) (vertex v) = k16Template twisted u v := by
  obtain ⟨t,e,he⟩ := k16_color_preserving_complete c hc
  let before := e.symm root
  let a := k16TemplateToLastEquiv t before
  have har : a before = 15 := k16TemplateToLastMap_deleted t before
  have har' : a.symm 15 = before := by rw [←har];simp
  refine ⟨t,a.symm.trans e,?_,?_⟩
  · change e (a.symm 15) = root
    rw [har'];exact e.apply_symm_apply root
  · intro u v huv
    change c (e (a.symm u)) (e (a.symm v)) = _
    rw [he _ _ (a.symm.injective.ne huv)]
    have hp := k16TemplateToLastMap_preserves t before (a.symm u) (a.symm v) (a.symm.injective.ne huv)
    change k16Template t (a.symm u) (a.symm v) = k16Template t (a (a.symm u)) (a (a.symm v)) at hp
    simpa only [Equiv.apply_symm_apply] using hp

/-- The same color-degree statistic is transported by the entire physical bijection. -/
theorem degree_of_color_preserving {n : Nat}
    (c d : EdgeColoring (Fin n) ThreeColor) (e : Fin n ≃ Fin n)
    (he : ∀ u v, u ≠ v → c (e u) (e v) = d u v) (q : ThreeColor) (u : Fin n) :
    colorDegree c q (e u) = colorDegree d q u := by
  classical
  unfold colorDegree
  symm
  apply Finset.card_bij (fun v _ => e v)
  · intro v hv
    obtain ⟨hne,hcolor⟩ := (mem_colorNeighborhood d q u v).mp hv
    exact (mem_colorNeighborhood c q (e u) (e v)).mpr
      ⟨e.injective.ne hne, (he u v hne.symm).trans hcolor⟩
  · intro a ha b hb hab;exact e.injective hab
  · intro v hv
    obtain ⟨hne,hcolor⟩ := (mem_colorNeighborhood c q (e u) v).mp hv
    refine ⟨e.symm v,?_,by simp⟩
    have hn : e.symm v ≠ u := by intro h;apply hne;rw [←e.apply_symm_apply v,h]
    apply (mem_colorNeighborhood d q u (e.symm v)).mpr
    refine ⟨hn,?_⟩
    rw [←he u (e.symm v) hn.symm,Equiv.apply_symm_apply]
    exact hcolor

#print axioms k15_color_preserving_complete
#print axioms k16_rooted_color_preserving_complete
#print axioms degree_of_color_preserving
end PricingABD.TemplateNormalization
