import UniformK61.BalancedEncodingValuation
import UniformK61.BalancedAnchorCoverage

set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedVisible UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

/-- Exactly the visible part of an actual opposite critical neighborhood. -/
def visible (c : Host) (s : Scope) : Finset Vertex :=
  (X ∪ Y) ∩ colorNeighborhood c (palette (scopeColor s)) (ownVertex s (center s))

theorem visible_embeds {c : Host} (h : Conditions c) (s : Scope) : Embeds c (visible c s) (scopeColor s) := by
  by_cases hs : side s = 0
  · simpa only [visible,scopeColor,ownVertex,hs,if_true,row] using h.row_embeddings (center s)
  · simpa only [visible,scopeColor,ownVertex,hs,if_false,column] using h.column_embeddings (center s)

theorem own_injective (s : Scope) : Function.Injective (ownVertex s) := by
  by_cases hs : side s = 0
  · simpa [Function.Injective,ownVertex,hs] using x_injective
  · simpa [Function.Injective,ownVertex,hs] using y_injective

theorem other_injective (s : Scope) : Function.Injective (otherVertex s) := by
  by_cases hs : side s = 0
  · simpa [Function.Injective,otherVertex,hs] using y_injective
  · simpa [Function.Injective,otherVertex,hs] using x_injective

theorem own_mem_union (s : Scope) (m : Fin 16) : ownVertex s m ∈ X ∪ Y := by
  by_cases hs : side s = 0 <;> simp [ownVertex,hs,X,Y]

theorem other_mem_union (s : Scope) (m : Fin 16) : otherVertex s m ∈ X ∪ Y := by
  by_cases hs : side s = 0 <;> simp [otherVertex,hs,X,Y]

theorem own_template {c : Host} {o : Owner} (h : Normalized c o.left o.right)
    (s : Scope) (a b : Fin 16) (hab : a ≠ b) :
    c (ownVertex s a) (ownVertex s b) = palette (foreign (guardColor s) (R4333.k16Template (ownKind o s) a b)) := by
  by_cases hs : side s = 0
  · simpa [ownVertex,guardColor,ownKind,hs] using h.left_template a b hab
  · simpa [ownVertex,guardColor,ownKind,hs] using h.right_template a b hab

theorem other_template {c : Host} {o : Owner} (h : Normalized c o.left o.right)
    (s : Scope) (a b : Fin 16) (hab : a ≠ b) :
    c (otherVertex s a) (otherVertex s b) = palette (foreign (scopeColor s) (memberColor o s a b)) := by
  by_cases hs : side s = 0
  · simpa [otherVertex,scopeColor,memberColor,otherKind,hs] using h.right_template a b hab
  · simpa [otherVertex,scopeColor,memberColor,otherKind,hs] using h.left_template a b hab

set_option maxRecDepth 10000 in
theorem reference_palette : ∀ s a b, a≠b →
    foreign (guardColor s) (BalancedAnchor.reference a b)=foreign (scopeColor s) (BalancedAnchor.reference a b) := by decide
set_option maxRecDepth 10000 in
theorem own_zero_color : ∀ s, foreign (guardColor s) 0=scopeColor s := by decide
set_option maxRecDepth 10000 in
theorem other_zero_color : ∀ s, foreign (scopeColor s) 0=guardColor s := by decide

theorem foreign_injective (q : Color) : Function.Injective (foreign q) := by
  intro a b h
  have he : foreignEquiv q a=foreignEquiv q b := Subtype.ext (congrArg palette h)
  exact (foreignEquiv q).injective he

theorem anchor_injective (o : Owner) (s : Scope) : Function.Injective (anchorVertex o s) := by
  intro a b h
  exact BalancedAnchor.anchor_injective_check _ _ _ _ ((own_injective s) h)

theorem anchor_mem_visible {c : Host} {o : Owner} (h : Normalized c o.left o.right) (s : Scope) (a : Fin 5) :
    anchorVertex o s a ∈ visible c s := by
  have ha := (BalancedAnchor.anchor_members (ownKind o s) (center s) (anchor (ownKind o s) (center s) a)).mpr ⟨a,rfl⟩
  apply Finset.mem_inter.mpr
  refine ⟨own_mem_union s _,(mem_colorNeighborhood _ _ _ _).mpr ⟨(own_injective s).ne ha.1,?_⟩⟩
  change c (ownVertex s (center s)) (ownVertex s (anchor (ownKind o s) (center s) a)) = _
  rw [own_template h s _ _ ha.1.symm,ha.2,own_zero_color]

theorem anchor_edge {c : Host} {o : Owner} (h : Normalized c o.left o.right)
    (s : Scope) (a b : Fin 5) (hab : a≠b) :
    c (anchorVertex o s a) (anchorVertex o s b) =
      palette (foreign (scopeColor s) (BalancedAnchor.reference a b)) := by
  have hne := (Function.Injective.ne (BalancedAnchor.anchor_injective_check (ownKind o s) (center s))) hab
  rw [anchorVertex,anchorVertex,own_template h s _ _ hne,BalancedAnchor.anchor_colors _ _ _ _ hab,reference_palette s a b hab]

theorem other_mem_visible {c : Host} (s : Scope) (m : Fin 16) :
    otherVertex s m ∈ visible c s ↔
      c (ownVertex s (center s)) (otherVertex s m) = palette (scopeColor s) := by
  simp only [visible,Finset.mem_inter,other_mem_union,true_and,mem_colorNeighborhood]
  exact and_iff_right ((own_other_ne s _ _).symm)

end UniformK61.BalancedEncoding
