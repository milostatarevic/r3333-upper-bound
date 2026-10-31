import UniformK60.BalancedHost
import UniformK60.HostNormalizationRoot
import UniformK60.HostNormalizationTemplates

/-! Literal placements for the all-C1 branch. The actual two complete
critical cells are classified and placed in one whole-host permutation. -/
set_option autoImplicit false
namespace UniformK60.BalancedC1Normalize
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.HostNormalization UniformK60.BalancedHost
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette

theorem literal_x : ∀ i : Fin 16,canonicalCell true (xVertex true i)=some (palette 0) := by decide
theorem literal_y : ∀ i : Fin 16,canonicalCell true (yVertex true i)=some (palette 1) := by decide
theorem literal_x_cover : ∀ v : Vertex,canonicalCell true v=some (palette 0) →
    ∃ i : Fin 16,xVertex true i=v := by decide
theorem literal_y_cover : ∀ v : Vertex,canonicalCell true v=some (palette 1) →
    ∃ i : Fin 16,yVertex true i=v := by decide

theorem templates (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (hs : Spokes true c) :
    ∃ e : Vertex ≃ Vertex,∃ o : Owner,e 0=0 ∧
      Normalized true (relabel c e (Equiv.refl _)) o := by
  have hdegree (q : Color) : colorDegree c (palette q) 0=canonicalDegree true q := by
    have h := rootCell_card c 0 (Equiv.refl _) (palette q)
    have hcell : rootCell c 0 (Equiv.refl _)=canonicalCell true := funext hs
    rw [hcell,canonicalCell_card] at h
    exact h.symm
  obtain ⟨tx,mx,hx⟩ := physical_k16_fixed_palette c hc 0 (palette 0) (hdegree 0) (foreignEquiv 0)
  obtain ⟨ty,my,hy⟩ := physical_k16_fixed_palette c hc 0 (palette 1) (hdegree 1) (foreignEquiv 1)
  let sx : Fin 16 ↪ Vertex := ⟨xVertex true,x_injective true⟩
  let sy : Fin 16 ↪ Vertex := ⟨yVertex true,y_injective true⟩
  have xmem (i : Fin 16) : sx i∈colorNeighborhood c (palette 0) 0 := by
    apply (rootCell_some c 0 (sx i) (Equiv.refl _) (palette 0)).mp
    exact (hs _).trans (literal_x i)
  have ymem (i : Fin 16) : sy i∈colorNeighborhood c (palette 1) 0 := by
    apply (rootCell_some c 0 (sy i) (Equiv.refl _) (palette 1)).mp
    exact (hs _).trans (literal_y i)
  have xcover (v : Vertex) (hv : v∈colorNeighborhood c (palette 0) 0) : ∃ i,sx i=v := by
    apply literal_x_cover v
    rw [←hs v]
    exact (rootCell_some c 0 v (Equiv.refl _) (palette 0)).mpr hv
  have ycover (v : Vertex) (hv : v∈colorNeighborhood c (palette 1) 0) : ∃ i,sy i=v := by
    apply literal_y_cover v
    rw [←hs v]
    exact (rootCell_some c 0 v (Equiv.refl _) (palette 1)).mpr hv
  obtain ⟨e,he0,hsp,hex,hey⟩ := simultaneous_neighborhood_maps
    (show palette 0≠palette 1 by decide) sx sy xmem ymem xcover ycover mx my
  refine ⟨e,(tx,ty),he0,?_,?_,?_,?_⟩
  · exact relabel_named_caps c hn e (Equiv.refl _) (pairSwap_preserves false false)
  · intro v
    change (if v=0 then none else some ((Equiv.refl FourColor).symm
      ((Equiv.refl FourColor).symm (c (e 0) (e v)))))=canonicalCell true v
    simp only [Equiv.refl_symm,Equiv.refl_apply,he0,hsp]
    exact hs v
  · intro a b hab
    change c (e (sx a)) (e (sx b))=_
    rw [hex,hex,mx.map_color a b hab,hx]
    rfl
  · intro a b hab
    change c (e (sy a)) (e (sy b))=_
    rw [hey,hey,my.map_color a b hab,hy]
    rfl

#print axioms templates
end UniformK60.BalancedC1Normalize
