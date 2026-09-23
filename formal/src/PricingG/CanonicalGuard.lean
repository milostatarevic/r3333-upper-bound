import PricingG.GuardedClassification
import Ramsey61.CPhysicalNormalization

namespace PricingG
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization

set_option maxRecDepth 100000 in
private theorem two_colors_palette : ∀ p q : FourColor, p ≠ q →
    ∃ σ : Equiv.Perm FourColor, σ (palette 0) = p ∧ σ (palette 1) = q := by decide

noncomputable def colorRelabel (c : Host) (σ : Equiv.Perm FourColor) : Host :=
  relabel c (Equiv.refl _) σ

theorem colorRelabel_neighborhood (c : Host) (σ : Equiv.Perm FourColor)
    (a : FourColor) (v : Vertex) :
    colorNeighborhood (colorRelabel c σ) a v = colorNeighborhood c (σ a) v := by
  ext u
  simp [mem_colorNeighborhood,colorRelabel,relabel,Equiv.symm_apply_eq]

theorem regular_guard_relabel (c : Host) (r : Vertex) (p q : FourColor)
    (h : RegularOverlapGuard c r p q) (σ : Equiv.Perm FourColor)
    (hp : σ (palette 0) = p) (hq : σ (palette 1) = q) :
    RegularOverlapGuard (colorRelabel c σ) r (palette 0) (palette 1) where
  colors_distinct := by decide
  first_root_degree := by
    change colorDegree (relabel c (Equiv.refl _) σ) _ _ = _
    rw [relabel_degree,hp]; exact h.first_root_degree
  second_root_degree := by
    change colorDegree (relabel c (Equiv.refl _) σ) _ _ = _
    rw [relabel_degree,hq]; exact h.second_root_degree
  other_root_degrees a ha0 ha1 := by
    change colorDegree (relabel c (Equiv.refl _) σ) _ _ = _
    rw [relabel_degree]
    exact h.other_root_degrees (σ a) (fun he => ha0 (σ.injective (he.trans hp.symm)))
      (fun he => ha1 (σ.injective (he.trans hq.symm)))
  eligible_root := by
    change 32 ≤ H (relabel c (Equiv.refl _) σ) r
    rw [relabel_H]; exact h.eligible_root
  first_fibers := by
    intro x hx
    rw [colorRelabel_neighborhood,hp] at hx
    rw [colorRelabel_neighborhood,colorRelabel_neighborhood,hp,hq]
    exact h.first_fibers x hx
  second_fibers := by
    intro x hx
    rw [colorRelabel_neighborhood,hq] at hx
    rw [colorRelabel_neighborhood,colorRelabel_neighborhood,hp,hq]
    exact h.second_fibers x hx
  first_opposite_high := by
    intro x hx
    rw [colorRelabel_neighborhood,hp] at hx
    change 15 ≤ colorDegree (relabel c (Equiv.refl _) σ) _ _
    rw [relabel_degree,hq]
    exact h.first_opposite_high x hx
  second_opposite_high := by
    intro x hx
    rw [colorRelabel_neighborhood,hq] at hx
    change 15 ≤ colorDegree (relabel c (Equiv.refl _) σ) _ _
    rw [relabel_degree,hp]
    exact h.second_opposite_high x hx

/-- A single global palette change puts any genuine G entrance into the
literal encoder's color convention; it preserves the same physical vertices. -/
theorem exists_canonical_guard (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (p q : FourColor) (hG : RegularOverlapGuard c r p q) :
    ∃ σ : Equiv.Perm FourColor, σ (palette 0) = p ∧ σ (palette 1) = q ∧
      NoMonochromaticTriangle (colorRelabel c σ) ∧
      RegularOverlapGuard (colorRelabel c σ) r (palette 0) (palette 1) := by
  obtain ⟨σ,hp,hq⟩ := two_colors_palette p q hG.colors_distinct
  exact ⟨σ,hp,hq,relabel_noMono c hc (Equiv.refl _) σ,regular_guard_relabel c r p q hG σ hp hq⟩

#print axioms exists_canonical_guard
end PricingG
