import Ramsey61.CPhysicalNormalization
import Mathlib.Logic.Equiv.Fintype

namespace PricingIntegration
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
  Ramsey61.CPhysicalNormalization

/-- An injective partial map preserving a finite partition extends to one
global permutation preserving the same partition. No coordinate outside the
partial domain is silently identified with an existing physical vertex. -/
theorem extend_labelled_injection {V L : Type*} [Fintype V] [DecidableEq V]
    (label : V → L) (D : Finset V) (f : {v // v ∈ D} → V)
    (hf : Function.Injective f) (hl : ∀ v, label (f v) = label v.val) :
    ∃ e : V ≃ V, (∀ v : {v // v ∈ D}, e v.val = f v) ∧
      ∀ v, label (e v) = label v := by
  classical
  let Cell (l : L) := {v : V // label v = l}
  let Domain (l : L) := {v : Cell l // v.val ∈ D}
  let g (l : L) (v : Domain l) : Cell l :=
    ⟨f ⟨v.val.val, v.property⟩, (hl _).trans v.val.property⟩
  have hg (l : L) : Function.Injective (g l) := by
    intro x y h
    have hh : (⟨x.val.val, x.property⟩ : {v // v ∈ D}) =
        ⟨y.val.val, y.property⟩ := hf (congrArg (fun z : Cell l => z.val) h)
    exact Subtype.ext (Subtype.ext (congrArg (fun z : {v // v ∈ D} => z.val) hh))
  have he (l : L) : ∃ e : Cell l ≃ Cell l, ∀ v : Domain l, e v.val = g l v :=
    Equiv.Perm.exists_extending_pair (fun v : Domain l => v.val) (g l)
      Subtype.val_injective (hg l)
  choose es hes using he
  let e : V ≃ V := Equiv.ofFiberEquiv es
  refine ⟨e, ?_, Equiv.ofFiberEquiv_map es⟩
  intro v
  have h := hes (label v.val) (⟨⟨v.val, rfl⟩, v.property⟩ : Domain (label v.val))
  exact congrArg Subtype.val h

/-- Two maps may overlap, but must agree there and may identify no distinct
physical vertices across their domains. These are local map conditions, not
a hypothesis asserting the existence of a global coloring or seed cover. -/
theorem glue_two_partial_injections {V L : Type*} [DecidableEq V]
    (label : V → L) (D E : Finset V) (f g : V → V)
    (hf : Set.InjOn f D) (hg : Set.InjOn g E)
    (hagree : ∀ x ∈ D, x ∈ E → f x = g x)
    (hcross : ∀ x ∈ D, ∀ y ∈ E, f x = g y → x = y)
    (hfl : ∀ x ∈ D, label (f x) = label x)
    (hgl : ∀ x ∈ E, label (g x) = label x) :
    ∃ h : V → V, Set.InjOn h (D ∪ E : Finset V) ∧
      (∀ x ∈ D, h x = f x) ∧ (∀ x ∈ E, h x = g x) ∧
      ∀ x ∈ D ∪ E, label (h x) = label x := by
  classical
  let h : V → V := fun x => if x ∈ D then f x else g x
  have hd : ∀ x ∈ D, h x = f x := by intro x hx; simp [h, hx]
  have he : ∀ x ∈ E, h x = g x := by
    intro x hx
    by_cases hxD : x ∈ D
    · rw [hd x hxD, hagree x hxD hx]
    · simp [h, hxD]
  refine ⟨h, ?_, hd, he, ?_⟩
  · intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · rw [hd x hx, hd y hy] at hxy; exact hf hx hy hxy
    · rw [hd x hx, he y hy] at hxy; exact hcross x hx y hy hxy
    · rw [he x hx, hd y hy] at hxy; exact (hcross y hy x hx hxy.symm).symm
    · rw [he x hx, he y hy] at hxy; exact hg hx hy hxy
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [hd x hx]; exact hfl x hx
    · rw [he x hx]; exact hgl x hx

/-- Partition tags preserve the root, all four root color cells, and the
distinguished exterior endpoint at 33. -/
def physicalTag (v : Vertex) : Option FourColor × Bool :=
  (canonicalCell v, decide (v = 33))

set_option maxRecDepth 10000 in
theorem canonicalCell_mem_iff : ∀ (q : Color) (v : Vertex),
    canonicalCell v = some (palette q) ↔ v ∈ rootBlocks q := by decide

theorem physicalTag_root {v : Vertex} (h : physicalTag v = physicalTag 0) : v = 0 := by
  have hc := congrArg Prod.fst h
  exact (canonicalCell_none v).mp hc

theorem physicalTag_marked {v : Vertex} (h : physicalTag v = physicalTag 33) : v = 33 := by
  have hm := congrArg Prod.snd h
  simpa [physicalTag] using hm

/-- The global extension retains the exact normalized root conditions and
the marked endpoint's actual high degree. -/
theorem physical_extension_preserves_host (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (hroot : RootConditions c)
    (hmarked : 15 ≤ colorDegree c (palette 2) 33)
    (e : Vertex ≃ Vertex) (htags : ∀ v, physicalTag (e v) = physicalTag v) :
    NoMonochromaticTriangle (relabel c e (Equiv.refl _)) ∧
    SelectorX (relabel c e (Equiv.refl _)) ∧
    RootConditions (relabel c e (Equiv.refl _)) ∧
    15 ≤ colorDegree (relabel c e (Equiv.refl _)) (palette 2) 33 := by
  have he0 : e 0 = 0 := physicalTag_root (htags 0)
  have he33 : e 33 = 33 := physicalTag_marked (htags 33)
  refine ⟨relabel_noMono c hc e _, relabel_selector c selectors e _, ?_, ?_⟩
  · constructor
    · intro q v hv
      have hvtag : canonicalCell (e v) = canonicalCell v := congrArg Prod.fst (htags v)
      have hev : e v ∈ rootBlocks q := (canonicalCell_mem_iff q (e v)).mp
        (hvtag.trans ((canonicalCell_mem_iff q v).mpr hv))
      change c (e 0) (e v) = palette q
      rw [he0]; exact hroot.1 q (e v) hev
    · simpa only [relabel_H, he0] using hroot.2
  · simpa only [relabel_degree, Equiv.refl_apply, he33] using hmarked

/-- Surjectivity on an included physical neighborhood also determines its
complement after extension. This is needed for all seed nonmembership units,
including vertices outside the explicitly mapped templates. -/
theorem extended_map_exact_subset {V : Type*} [DecidableEq V]
    (D S T : Finset V) (hSD : S ⊆ D) (f : {v // v ∈ D} → V)
    (e : V ≃ V) (he : ∀ v : {v // v ∈ D}, e v.val = f v)
    (hinto : ∀ s (hs : s ∈ S), f ⟨s, hSD hs⟩ ∈ T)
    (honto : ∀ t ∈ T, ∃ s, ∃ hs : s ∈ S, f ⟨s, hSD hs⟩ = t) :
    ∀ v, e v ∈ T ↔ v ∈ S := by
  intro v
  constructor
  · intro hv
    obtain ⟨s, hs, hf⟩ := honto (e v) hv
    have hev : e s = e v := (he ⟨s, hSD hs⟩).trans hf
    simpa only [e.injective hev] using hs
  · intro hv
    rw [he ⟨v, hSD hv⟩]
    exact hinto v hv

/-- Assemble compatible physical template maps into a single normalized host.
The marked neighborhood is exact even on the unassigned exterior vertices;
therefore both positive membership and negative nonmembership units follow.
All other seed edges retain their local mapped colors. -/
theorem physical_partial_map_supplies_base (c : Host)
    (hc : NoMonochromaticTriangle c) (selectors : SelectorX c)
    (hroot : RootConditions c) (hmarked : 15 ≤ colorDegree c (palette 2) 33)
    (D S : Finset Vertex) (hSD : S ⊆ D) (f : {v // v ∈ D} → Vertex)
    (hf : Function.Injective f) (htags : ∀ v, physicalTag (f v) = physicalTag v.val)
    (hinto : ∀ s (hs : s ∈ S), f ⟨s, hSD hs⟩ ∈ colorNeighborhood c (palette 2) 33)
    (honto : ∀ t ∈ colorNeighborhood c (palette 2) 33,
      ∃ s, ∃ hs : s ∈ S, f ⟨s, hSD hs⟩ = t) :
    ∃ e : Vertex ≃ Vertex,
      (∀ v : {v // v ∈ D}, e v.val = f v) ∧
      NoMonochromaticTriangle (relabel c e (Equiv.refl _)) ∧
      SelectorX (relabel c e (Equiv.refl _)) ∧
      RootConditions (relabel c e (Equiv.refl _)) ∧
      15 ≤ colorDegree (relabel c e (Equiv.refl _)) (palette 2) 33 ∧
      colorNeighborhood (relabel c e (Equiv.refl _)) (palette 2) 33 = S ∧
      (∀ u v : {v // v ∈ D},
        relabel c e (Equiv.refl _) u.val v.val = c (f u) (f v)) ∧
      DenseCounter.FormulaSat (baseValuation (relabel c e (Equiv.refl _))) broaderBaseCNF := by
  obtain ⟨e, he, hl⟩ := extend_labelled_injection physicalTag D f hf htags
  obtain ⟨hgood, hsel, hnorm, hhigh⟩ :=
    physical_extension_preserves_host c hc selectors hroot hmarked e hl
  have he33 : e 33 = 33 := physicalTag_marked (hl 33)
  have hexact := extended_map_exact_subset D S (colorNeighborhood c (palette 2) 33)
    hSD f e he hinto honto
  refine ⟨e, he, hgood, hsel, hnorm, hhigh, ?_, ?_,
    coloring_satisfies_broaderBase _ hgood hsel hnorm⟩
  · ext v
    rw [← hexact v]
    simp only [mem_colorNeighborhood, relabel, Equiv.refl_symm, Equiv.refl_apply]
    have hne : e v ≠ 33 ↔ v ≠ 33 := by
      have hh : e v ≠ e (33 : Vertex) ↔ v ≠ (33 : Vertex) := e.injective.ne_iff
      simpa only [he33] using hh
    simpa only [he33, hne]
  · intro u v
    change c (e u.val) (e v.val) = c (f u) (f v)
    rw [he u, he v]

end PricingIntegration
