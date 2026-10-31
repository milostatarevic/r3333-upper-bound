import UniformK60.BalancedRawRoot
import UniformK60.BalancedHostBraceGeometry

set_option autoImplicit false
namespace UniformK60.BalancedHostBraceStart
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.BalancedRawRoot UniformK60.BalancedHostBraceGeometry

/-- The named caps force both raw high colors to remain critical at every
vertex, even when C1 and C2 profiles coexist. -/
theorem raw_mark_high (c : Host) (h : RawCaps c) (v : Vertex) :
    15≤colorDegree c (palette 3) v := by
  have hs := fourColor_degree_sum c v
  have h0 := h v 0
  have h1 := h v 1
  have h2 := h v 2
  change colorDegree c (palette 0) v+colorDegree c (palette 1) v+
    colorDegree c (palette 2) v+colorDegree c (palette 3) v=59 at hs
  change colorDegree c (palette 0) v≤14 at h0
  change colorDegree c (palette 1) v≤14 at h1
  change colorDegree c (palette 2) v≤16 at h2
  omega

theorem lowSwap_caps (c : Host) (h : RawCaps c) : RawCaps (relabel c (Equiv.refl _) lowSwap) := by
  intro v q
  rw [relabel_degree,lowSwap_palette]
  have hh := h v ((Equiv.swap 0 1 : Color≃Color) q)
  have he : ∀ q : Color,(if ((Equiv.swap 0 1 : Color≃Color) q).val<2 then 14 else 16)=
      (if q.val<2 then 14 else 16) := by decide
  rw [he] at hh
  exact hh

theorem lowSwap_degrees (c : Host) (r : Vertex)
    (h : ∀ q : Color,colorDegree c (palette q) r=rawDegree q) :
    ∀ q : Color,colorDegree (relabel c (Equiv.refl _) lowSwap) (palette q) r=rawDegree q := by
  intro q
  rw [relabel_degree,lowSwap_palette]
  change colorDegree c (palette ((Equiv.swap 0 1 : Color≃Color) q)) r=rawDegree q
  rw [h]
  have he : ∀ q : Color,rawDegree ((Equiv.swap 0 1 : Color≃Color) q)=rawDegree q := by decide
  exact he q

/-- An arbitrary mark in the actual15-cell suffices. A single optional
low-color exchange orients its fake support to be a pentagon. -/
theorem oriented_root (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (r : Vertex) (hw : W c r=31) :
    ∃ d : Host,NoMonochromaticTriangle d ∧ RawCaps d ∧
      (∀ q : Color,colorDegree d (palette q) r=rawDegree q) ∧
      ∃ mark : Vertex,mark∈colorNeighborhood d (palette 3) r ∧
        15≤colorDegree d (palette 3) mark ∧ (support d r mark 1).card=5 := by
  obtain ⟨σ,good,caps,hd⟩ := normalized_root c hc hn r hw
  let a := relabel c (Equiv.refl _) σ
  have hpos : 0<(colorNeighborhood a (palette 3) r).card := by
    change 0<colorDegree a (palette 3) r
    rw [hd]
    decide
  obtain ⟨mark,hm⟩ := Finset.card_pos.mp hpos
  obtain ⟨τ,hτ,good',hm',hh',h5⟩ := orient_low a good r mark hm (raw_mark_high a caps mark)
  rcases hτ with rfl|rfl
  · exact ⟨a,good,caps,hd,mark,hm',hh',h5⟩
  · exact ⟨relabel a (Equiv.refl _) lowSwap,good',lowSwap_caps a caps,
      lowSwap_degrees a r hd,mark,hm',hh',h5⟩

#print axioms oriented_root
end UniformK60.BalancedHostBraceStart
