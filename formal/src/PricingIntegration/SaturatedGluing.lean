import PricingIntegration.PhysicalGluing

namespace PricingIntegration

/-- A union of complete label classes contains every point with the same
label as one of its points. -/
def LabelSaturated {V L : Type*} [DecidableEq V]
    (label : V → L) (D : Finset V) : Prop :=
  ∀ x ∈ D, ∀ y, label y = label x → y ∈ D

theorem labelSaturated_union {V L : Type*} [DecidableEq V]
    (label : V → L) (D E : Finset V)
    (hD : LabelSaturated label D) (hE : LabelSaturated label E) :
    LabelSaturated label (D ∪ E) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left E (hD x hx y hy)
  · exact Finset.mem_union_right D (hE x hx y hy)

/-- Complete root color cells force cross-injectivity. Thus compatible
scope maps need no extra global disjoint-image premise. -/
theorem glue_saturated_partial_injections {V L : Type*} [DecidableEq V]
    (label : V → L) (D E : Finset V) (f g : V → V)
    (hD : LabelSaturated label D)
    (hf : Set.InjOn f D) (hg : Set.InjOn g E)
    (hagree : ∀ x ∈ D, x ∈ E → f x = g x)
    (hfl : ∀ x ∈ D, label (f x) = label x)
    (hgl : ∀ x ∈ E, label (g x) = label x) :
    ∃ h : V → V, Set.InjOn h (D ∪ E : Finset V) ∧
      (∀ x ∈ D, h x = f x) ∧ (∀ x ∈ E, h x = g x) ∧
      ∀ x ∈ D ∪ E, label (h x) = label x := by
  apply glue_two_partial_injections label D E f g hf hg hagree
  · intro x hx y hy heq
    have hlabel : label y = label x :=
      (hgl y hy).symm.trans ((congrArg label heq).symm.trans (hfl x hx))
    have hyD := hD x hx y hlabel
    apply hf hx hyD
    exact heq.trans (hagree y hyD hy).symm
  · exact hfl
  · exact hgl

/-- Three physical scopes, the first two covering entire root cells, glue
using only their pairwise agreement. This handles the full X/Y blocks and
the overlapping, possibly punctured S block in the C census. -/
theorem glue_three_physical_scopes {V L : Type*} [DecidableEq V]
    (label : V → L) (X Y S : Finset V) (fx fy fs : V → V)
    (hX : LabelSaturated label X) (hY : LabelSaturated label Y)
    (hfx : Set.InjOn fx X) (hfy : Set.InjOn fy Y) (hfs : Set.InjOn fs S)
    (hxy : ∀ x ∈ X, x ∈ Y → fx x = fy x)
    (hxs : ∀ x ∈ X, x ∈ S → fx x = fs x)
    (hys : ∀ x ∈ Y, x ∈ S → fy x = fs x)
    (htx : ∀ x ∈ X, label (fx x) = label x)
    (hty : ∀ x ∈ Y, label (fy x) = label x)
    (hts : ∀ x ∈ S, label (fs x) = label x) :
    ∃ f : V → V, Set.InjOn f ((X ∪ Y) ∪ S : Finset V) ∧
      (∀ x ∈ X, f x = fx x) ∧ (∀ x ∈ Y, f x = fy x) ∧
      (∀ x ∈ S, f x = fs x) ∧
      ∀ x ∈ (X ∪ Y) ∪ S, label (f x) = label x := by
  obtain ⟨fxy,hinj,hx,hy,ht⟩ := glue_saturated_partial_injections
    label X Y fx fy hX hfx hfy hxy htx hty
  have hagree : ∀ x ∈ X ∪ Y, x ∈ S → fxy x = fs x := by
    intro x hmem hs
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · exact (hx x hmem).trans (hxs x hmem hs)
    · exact (hy x hmem).trans (hys x hmem hs)
  obtain ⟨f,hf,hxy',hs,htags⟩ := glue_saturated_partial_injections
    label (X ∪ Y) S fxy fs (labelSaturated_union label X Y hX hY)
      hinj hfs hagree ht hts
  exact ⟨f,hf,fun x hx' => (hxy' x (Finset.mem_union_left Y hx')).trans (hx x hx'),
    fun x hy' => (hxy' x (Finset.mem_union_right X hy')).trans (hy x hy'),hs,htags⟩

#print axioms glue_three_physical_scopes
end PricingIntegration
