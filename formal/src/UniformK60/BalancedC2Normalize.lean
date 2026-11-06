import UniformK60.BalancedHost
import UniformK60.HostNormalizationRoot
import UniformK60.HostNormalizationTemplates

/-! A C2 root is placed directly in one of the four compatibility layouts.
The two actual critical neighborhoods are normalized by one whole-host
permutation; no marked neighborhood or brace facts are selected. -/
set_option autoImplicit false
namespace UniformK60.BalancedC2Normalize
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.HostNormalization UniformK60.BalancedHost
open UniformK60.ClassificationAdapter UniformK60.ClassificationFixedPalette

theorem literal_x : ∀ i : Fin 15,canonicalCell false (xVertex false i)=some (palette 0) := by decide
theorem literal_y : ∀ i : Fin 16,canonicalCell false (yVertex false i)=some (palette 1) := by decide
theorem literal_x_cover : ∀ v : Vertex,canonicalCell false v=some (palette 0) →
    ∃ i : Fin 15,xVertex false i=v := by decide
theorem literal_y_cover : ∀ v : Vertex,canonicalCell false v=some (palette 1) →
    ∃ i : Fin 16,yVertex false i=v := by decide

theorem templates (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (hs : Spokes false c) :
    ∃ e : Vertex ≃ Vertex,∃ o : Owner,e 0=0 ∧
      Normalized false (relabel c e (Equiv.refl _)) o := by
  have hdegree (q : Color) : colorDegree c (palette q) 0=canonicalDegree false q := by
    have h := rootCell_card c 0 (Equiv.refl _) (palette q)
    have hcell : rootCell c 0 (Equiv.refl _)=canonicalCell false := funext hs
    rw [hcell,canonicalCell_card] at h
    exact h.symm
  obtain ⟨tx,mx,hx⟩ := physical_k15_fixed_palette c hc 0 (palette 0) (hdegree 0) (foreignEquiv 0)
  obtain ⟨ty,my,hy⟩ := physical_k16_fixed_palette c hc 0 (palette 1) (hdegree 1) (foreignEquiv 1)
  let sx : Fin 15 ↪ Vertex := ⟨xVertex false,x_injective false⟩
  let sy : Fin 16 ↪ Vertex := ⟨yVertex false,y_injective false⟩
  have xmem (i : Fin 15) : sx i∈colorNeighborhood c (palette 0) 0 := by
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
      ((Equiv.refl FourColor).symm (c (e 0) (e v)))))=canonicalCell false v
    simp only [Equiv.refl_symm,Equiv.refl_apply,he0,hsp]
    exact hs v
  · intro a b hab
    change c (e (sx a)) (e (sx b))=_
    rw [hex,hex,mx.map_color a b hab,hx,k15Template_castSucc]
    rfl
  · intro a b hab
    change c (e (sy a)) (e (sy b))=_
    rw [hey,hey,my.map_color a b hab,hy]
    rfl

theorem canonical_C2 (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (r : Vertex) (hr : W c r=31) :
    ∃ d : Host,∃ o : Owner,NoMonochromaticTriangle d ∧ Normalized false d o := by
  obtain ⟨σ,e,_,_,hn',hs⟩ := normalize_named_C2_root c hn r hr
  let d := relabel c e σ
  have hd := relabel_noMono c hc e σ
  obtain ⟨f,o,_,hf⟩ := templates d hd hn' hs
  exact ⟨relabel d f (Equiv.refl _),o,relabel_noMono d hd f (Equiv.refl _),hf⟩

#print axioms canonical_C2
end UniformK60.BalancedC2Normalize
