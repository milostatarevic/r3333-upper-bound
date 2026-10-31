import UniformK60.HostNormalizationPair

set_option autoImplicit false
namespace UniformK60.HostNormalization
open Ramsey61 UniformK60.Physical

/-- Palette permutations may exchange the two high colors or the two low colors,
without imposing a common deficiency color on the rest of the host. -/
def PairPreserving (σ : Equiv.Perm FourColor) : Prop :=
  ∀ q : Color, ∃ q' : Color,
    σ (palette q) = palette q' ∧ (q'.val < 2 ↔ q.val < 2)

def pairSwap (high low : Bool) : Equiv.Perm FourColor :=
  if high then Equiv.swap (palette 0) (palette 1)
  else if low then Equiv.swap (palette 2) (palette 3) else Equiv.refl _

theorem pairSwap_preserves : ∀ high low, PairPreserving (pairSwap high low) := by unfold PairPreserving; decide

theorem relabel_named_caps (c : Host) (hn : NamedCaps c)
    (e : Vertex ≃ Vertex) (σ : Equiv.Perm FourColor) (hσ : PairPreserving σ) :
    NamedCaps (relabel c e σ) := by
  intro v q
  obtain ⟨q',hq',hh⟩ := hσ q
  rw [relabel_degree,hq']
  simpa only [hh] using hn (e v) q'

/-- The named caps determine a canonical orientation at the selected root. -/
theorem named_root_orientation (c : Host) (hn : NamedCaps c) (r : Vertex) :
    ∃ c1 : Bool, ∃ σ : Equiv.Perm FourColor, PairPreserving σ ∧
      ∀ q : Color, colorDegree c (σ (palette q)) r = canonicalDegree c1 q := by
  rcases named_caps_vectors c hn r with h | h | h | h
  · refine ⟨false,pairSwap false false,pairSwap_preserves _ _,?_⟩
    intro q; fin_cases q <;> simp_all [pairSwap,canonicalDegree,firstSize]
  · refine ⟨false,pairSwap true false,pairSwap_preserves _ _,?_⟩
    intro q; fin_cases q <;>
      simp_all [pairSwap,canonicalDegree,firstSize,Equiv.swap_apply_def,palette]
  · refine ⟨true,pairSwap false false,pairSwap_preserves _ _,?_⟩
    intro q; fin_cases q <;> simp_all [pairSwap,canonicalDegree,firstSize]
  · refine ⟨true,pairSwap false true,pairSwap_preserves _ _,?_⟩
    intro q; fin_cases q <;>
      simp_all [pairSwap,canonicalDegree,firstSize,Equiv.swap_apply_def,palette]

theorem relabel_rootCell (c : Host) (e : Vertex ≃ Vertex)
    (σ : Equiv.Perm FourColor) (r : Vertex) (he : e 0 = r) (v : Vertex) :
    rootCell (relabel c e σ) 0 (Equiv.refl _) v = rootCell c r σ (e v) := by
  have hv : e v = r ↔ v = 0 := by rw [← he]; exact e.injective.eq_iff
  simp [rootCell,relabel,he,hv]

theorem canonical_degrees_W (c : Host) (r : Vertex) (c1 : Bool)
    (hd : ∀ q : Color, colorDegree c (palette q) r = canonicalDegree c1 q) :
    W c r = if c1 then 32 else 31 := by
  have h0 := hd 0; have h1 := hd 1; have h2 := hd 2; have h3 := hd 3
  rw [W_eq_mass4]
  change mass4 (colorDegree c (palette 0) r) (colorDegree c (palette 1) r)
    (colorDegree c (palette 2) r) (colorDegree c (palette 3) r) = _
  rw [h0,h1,h2,h3]
  cases c1 <;> decide

/-- Both balanced profiles admit canonical spokes through a single whole-host
vertex bijection and a global palette permutation preserving the named pair. -/
theorem normalize_named_root (c : Host) (hn : NamedCaps c) (r : Vertex) :
    ∃ c1 : Bool, ∃ σ : Equiv.Perm FourColor, ∃ e : Vertex ≃ Vertex,
      e 0 = r ∧ PairPreserving σ ∧ NamedCaps (relabel c e σ) ∧
      (∀ v, rootCell (relabel c e σ) 0 (Equiv.refl _) v = canonicalCell c1 v) ∧
      W c r = if c1 then 32 else 31 := by
  obtain ⟨c1,σ,hσ,hd⟩ := named_root_orientation c hn r
  obtain ⟨e,he0,he⟩ := exists_balanced_root_equiv c r σ c1 hd
  refine ⟨c1,σ,e,he0,hσ,relabel_named_caps c hn e σ hσ,?_,?_⟩
  · intro v; rw [relabel_rootCell c e σ r he0 v]; exact he v
  · have hw := canonical_degrees_W (relabel c e σ) 0 c1 (by
      intro q; rw [relabel_degree,he0]; exact hd q)
    simpa only [relabel_W,he0] using hw

/-- A C2 root has the15-color first and the16-color second. Only generic caps
are transported; other vertices may still have profile C1. -/
theorem normalize_named_C2_root (c : Host) (hn : NamedCaps c) (r : Vertex)
    (hw : W c r = 31) :
    ∃ σ : Equiv.Perm FourColor, ∃ e : Vertex ≃ Vertex,
      e 0 = r ∧ PairPreserving σ ∧ NamedCaps (relabel c e σ) ∧
      ∀ v, rootCell (relabel c e σ) 0 (Equiv.refl _) v = canonicalCell false v := by
  obtain ⟨c1,σ,e,he,hσ,hn,hs,hm⟩ := normalize_named_root c hn r
  cases c1
  · exact ⟨σ,e,he,hσ,hn,hs⟩
  · simp only [ite_true] at hm
    omega

/-- The C1 orientation places its13-color before its14-color. -/
theorem normalize_named_C1_root (c : Host) (hn : NamedCaps c) (r : Vertex)
    (hw : W c r = 32) :
    ∃ σ : Equiv.Perm FourColor, ∃ e : Vertex ≃ Vertex,
      e 0 = r ∧ PairPreserving σ ∧ NamedCaps (relabel c e σ) ∧
      ∀ v, rootCell (relabel c e σ) 0 (Equiv.refl _) v = canonicalCell true v := by
  obtain ⟨c1,σ,e,he,hσ,hn,hs,hm⟩ := normalize_named_root c hn r
  cases c1
  · simp only [Bool.false_eq_true,ite_false] at hm
    omega
  · exact ⟨σ,e,he,hσ,hn,hs⟩

#print axioms normalize_named_C2_root
#print axioms normalize_named_C1_root
end UniformK60.HostNormalization
