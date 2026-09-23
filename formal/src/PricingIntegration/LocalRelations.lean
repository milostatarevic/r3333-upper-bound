import PricingIntegration.LocalProjection

namespace PricingIntegration.LocalRelations
open Ramsey61 Ramsey61.CEncodingCore PricingC PricingG.Completion72

structure ScopeSpec where
  roles : Fin 10 → Fin 16
  colors : Fin 3 → Color
  observed : Fin 10 → Fin 10 → Option Color

def predicted (s : ScopeSpec) (i : Fin 72) (a b : Fin 10) : Color :=
  s.colors (referenceColor i (s.roles a) (s.roles b))

def Allows : Option Color → Color → Prop
  | some old, value => value = old
  | none, value => value = 2 ∨ value = 3

instance (old : Option Color) (value : Color) : Decidable (Allows old value) := by
  cases old <;> unfold Allows <;> infer_instance

/-- Filter the complete72state relation by every actual observed physical
edge. Unknown cross edges retain exactly the two allowed low colors. -/
def Compatible (s : ScopeSpec) (i : Fin 72) : Prop :=
  ∀ a b : Fin 10, a < b → Allows (s.observed a b) (predicted s i a b)

instance (s : ScopeSpec) (i : Fin 72) : Decidable (Compatible s i) :=
  inferInstanceAs (Decidable (∀ a b : Fin 10, a < b → Allows (s.observed a b) (predicted s i a b)))

def rows (s : ScopeSpec) : List (Fin 72) := (List.finRange 72).filter (fun i => decide (Compatible s i))

def ObservedBy (c : Host) (phys : Fin 10 ↪ Vertex) (s : ScopeSpec) : Prop :=
  ∀ a b : Fin 10, a < b →
    match s.observed a b with
    | some old => c (phys a) (phys b) = palette old
    | none => c (phys a) (phys b) = palette 2 ∨ c (phys a) (phys b) = palette 3

/-- Concrete geometric hypotheses of one opposite-color K10 restriction.
Each field is an actual host incidence or a finite role/palette identity;
there is no assumed local-completion or relation-membership statement. -/
structure PhysicalScope (c : Host) (s : ScopeSpec) where
  owner : Vertex
  omitted : FourColor
  high : 15 ≤ colorDegree c omitted owner
  pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}
  palette_match : ∀ q, (pal q).val = palette (s.colors q)
  phys : Fin 10 ↪ Vertex
  mem_scope : ∀ k, phys k ∈ colorNeighborhood c omitted owner
  anchor : Fin 5 ↪ Fin 10
  independent : ∀ j k, j ≠ k → c (phys (anchor j)) (phys (anchor k)) ≠ (pal 0).val
  anchor_roles : ∀ j, s.roles (anchor j) = generators j
  outside_roles : ∀ k, (∀ j, k ≠ anchor j) → ∀ j, s.roles k ≠ generators j
  mask : ∀ k, (∀ j, k ≠ anchor j) → ∀ j,
    (c (phys (anchor j)) (phys k) = (pal 0).val ↔ xorGraph.Adj (generators j) (s.roles k))
  observed : ObservedBy c phys s

theorem actual_scope_supplies_retained_row (c : Host) (hc : NoMonochromaticTriangle c)
    (s : ScopeSpec) (g : PhysicalScope c s) :
    ∃ i ∈ rows s, ∀ a b : Fin 10, a ≠ b →
      c (g.phys a) (g.phys b) = palette (predicted s i a b) := by
  obtain ⟨i,hi⟩ := LocalProjection.physical_scope_projection c hc g.owner g.omitted
    g.high g.pal g.phys g.mem_scope g.anchor s.roles g.independent
    g.anchor_roles g.outside_roles g.mask
  have hcolors : ∀ a b : Fin 10, a ≠ b →
      c (g.phys a) (g.phys b) = palette (predicted s i a b) := by
    intro a b hab
    exact (hi a b hab).trans (g.palette_match _)
  have hcomp : Compatible s i := by
    intro a b hab
    have ho := g.observed a b hab
    have hp := hcolors a b (Fin.ne_of_lt hab)
    cases h : s.observed a b with
    | none =>
      simp only [h] at ho
      rcases ho with ho | ho
      · exact Or.inl (palette_injective (hp.symm.trans ho))
      · exact Or.inr (palette_injective (hp.symm.trans ho))
    | some old =>
      simp only [h] at ho
      exact palette_injective (hp.symm.trans ho)
  exact ⟨i,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa using hcomp⟩,hcolors⟩

def emptyCheck (s : ScopeSpec) : Bool := (rows s).isEmpty

def forcedCheck (s : ScopeSpec) (a b : Fin 10) (q : Color) : Bool :=
  (rows s).all fun i => predicted s i a b == q

/-- Soundness of the retained EMPTY_SCOPE witnesses. The only finite
computation premise is the explicit Boolean check of the literal relation. -/
theorem empty_check_excludes (c : Host) (hc : NoMonochromaticTriangle c)
    (s : ScopeSpec) (g : PhysicalScope c s) (hempty : emptyCheck s = true) : False := by
  obtain ⟨i,hi,_⟩ := actual_scope_supplies_retained_row c hc s g
  have he : rows s = [] := List.isEmpty_iff.mp hempty
  simpa only [he,List.not_mem_nil] using hi

theorem forced_check_color (c : Host) (hc : NoMonochromaticTriangle c)
    (s : ScopeSpec) (g : PhysicalScope c s) (a b : Fin 10) (hne : a ≠ b) (q : Color)
    (hforced : forcedCheck s a b q = true) : c (g.phys a) (g.phys b) = palette q := by
  obtain ⟨i,hi,hc'⟩ := actual_scope_supplies_retained_row c hc s g
  have h := List.all_eq_true.mp hforced i hi
  exact (hc' a b hne).trans (congrArg palette (beq_iff_eq.mp h))

/-- Soundness of a forced-color conflict on the same physical edge, including
opposite local endpoint order. No global diagonal enumeration is needed. -/
theorem forced_conflict_excludes (c : Host) (hc : NoMonochromaticTriangle c)
    (s t : ScopeSpec) (gs : PhysicalScope c s) (gt : PhysicalScope c t)
    (a b d e : Fin 10) (hab : a ≠ b) (hde : d ≠ e)
    (q r : Color) (hqr : q ≠ r)
    (hfirst : forcedCheck s a b q = true) (hsecond : forcedCheck t d e r = true)
    (hedge : (gs.phys a = gt.phys d ∧ gs.phys b = gt.phys e) ∨
      (gs.phys a = gt.phys e ∧ gs.phys b = gt.phys d)) : False := by
  have hs := forced_check_color c hc s gs a b hab q hfirst
  have ht := forced_check_color c hc t gt d e hde r hsecond
  apply hqr
  apply palette_injective
  rcases hedge with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb] at hs
    exact hs.symm.trans ht
  · rw [ha,hb,c.color_symm] at hs
    exact hs.symm.trans ht

#print axioms actual_scope_supplies_retained_row
#print axioms empty_check_excludes
#print axioms forced_conflict_excludes
end PricingIntegration.LocalRelations
