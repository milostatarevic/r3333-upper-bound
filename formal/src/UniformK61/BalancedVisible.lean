import Ramsey61.GuardedEntrance
import UniformK61.BalancedHostOwners

/-! The ordinary color-preserving embedding condition on the visible part
of each actual opposite critical neighborhood. All sets use physical vertices. -/

set_option autoImplicit false
namespace UniformK61.BalancedVisible
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization Finset
open Ramsey61.ClassificationAdapter PricingIntegration.BActualFrame
open PricingIntegration.FixedPhysicalNeighborhood UniformK61.BalancedHost

def X : Finset Vertex := Finset.univ.image xVertex
def Y : Finset Vertex := Finset.univ.image yVertex

set_option maxRecDepth 20000 in
theorem canonical_x : ∀ v, canonicalCell v = some (palette 0) ↔ v ∈ X := by decide
set_option maxRecDepth 20000 in
theorem canonical_y : ∀ v, canonicalCell v = some (palette 1) ↔ v ∈ Y := by decide

theorem x_ne_zero (i : Fin 16) : xVertex i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp only [xVertex,Fin.val_zero] at this; omega
theorem y_ne_zero (i : Fin 16) : yVertex i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp only [yVertex,Fin.val_zero] at this; omega

theorem X_neighborhood (c : Host) (hs : Spokes c) : X = colorNeighborhood c (palette 0) 0 := by
  ext v
  rw [←canonical_x v,←spokes_rootCell c hs v]
  exact rootCell_some c 0 v (Equiv.refl _) _

theorem Y_neighborhood (c : Host) (hs : Spokes c) : Y = colorNeighborhood c (palette 1) 0 := by
  ext v
  rw [←canonical_y v,←spokes_rootCell c hs v]
  exact rootCell_some c 0 v (Equiv.refl _) _

def row (c : Host) (i : Fin 16) : Finset Vertex := (X ∪ Y) ∩ colorNeighborhood c (palette 1) (xVertex i)
def column (c : Host) (i : Fin 16) : Finset Vertex := (X ∪ Y) ∩ colorNeighborhood c (palette 0) (yVertex i)

/-- An injection preserving every edge of the entire observed colored graph.
There are no centers or independently recolored physical edges. -/
def Embeds (c : Host) (S : Finset Vertex) (omitted : Color) : Prop :=
  ∃ t : Bool, ∃ e : S ↪ Fin 16,
    ∀ u v : S, u ≠ v → c u.val v.val = palette (foreign omitted (R4333.k16Template t (e u) (e v)))

theorem actual_subset_embeds (c : Host) (hc : NoMonochromaticTriangle c)
    (center : Vertex) (omitted : Color) (hd : colorDegree c (palette omitted) center = 16)
    (S : Finset Vertex) (hS : S ⊆ colorNeighborhood c (palette omitted) center) :
    Embeds c S omitted := by
  classical
  obtain ⟨t,m,hpal⟩ := physical_k16_fixed_palette c hc center (palette omitted) hd (foreignEquiv omitted)
  have hcover (u : S) : ∃ i : Fin 16, m.vertex i = u.val :=
    m.covers_neighborhood u.val (hS u.property)
  let position : S → Fin 16 := fun u => Classical.choose (hcover u)
  have hposition (u : S) : m.vertex (position u) = u.val := Classical.choose_spec (hcover u)
  have hinj : Function.Injective position := by
    intro u v h
    apply Subtype.ext
    exact (hposition u).symm.trans ((congrArg m.vertex h).trans (hposition v))
  refine ⟨t,⟨position,hinj⟩,?_⟩
  intro u v huv
  change c u.val v.val = palette (foreign omitted (R4333.k16Template t (position u) (position v)))
  rw [←hposition u,←hposition v,m.map_color _ _ (hinj.ne huv),hpal]
  rfl

theorem rows_embed (c : Host) (hc : NoMonochromaticTriangle c) (hn : Named c) (i : Fin 16) :
    Embeds c (row c i) 1 :=
  actual_subset_embeds c hc (xVertex i) 1 (hn _ 1) _ Finset.inter_subset_right

theorem columns_embed (c : Host) (hc : NoMonochromaticTriangle c) (hn : Named c) (i : Fin 16) :
    Embeds c (column c i) 0 :=
  actual_subset_embeds c hc (yVertex i) 0 (hn _ 0) _ Finset.inter_subset_right

theorem row_guard (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : Named c) (hs : Spokes c) (i : Fin 16) :
    (colorNeighborhood c (palette 0) (xVertex i) ∩ Y).card = 5 := by
  rw [Y_neighborhood c hs]
  apply degree_sixteen_cross_intersection c hc (palette 0) 0 (xVertex i)
  · exact (mem_colorNeighborhood _ _ _ _).mpr ⟨x_ne_zero i,spoke_x c hs i⟩
  · exact hn _ 0
  · decide

theorem column_guard (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : Named c) (hs : Spokes c) (i : Fin 16) :
    (colorNeighborhood c (palette 1) (yVertex i) ∩ X).card = 5 := by
  rw [X_neighborhood c hs]
  apply degree_sixteen_cross_intersection c hc (palette 1) 0 (yVertex i)
  · exact (mem_colorNeighborhood _ _ _ _).mpr ⟨y_ne_zero i,spoke_y c hs i⟩
  · exact hn _ 1
  · decide

/-- Complete normalized physical host interface for the finite table encoder.
Every local injection is supplied by an actual16-neighborhood in this host. -/
structure Conditions (c : Host) : Prop where
  row_embeddings : ∀ i, Embeds c (row c i) 1
  column_embeddings : ∀ i, Embeds c (column c i) 0
  row_five : ∀ i, (colorNeighborhood c (palette 0) (xVertex i) ∩ Y).card = 5
  column_five : ∀ i, (colorNeighborhood c (palette 1) (yVertex i) ∩ X).card = 5

theorem normalized_conditions {c : Host} {tx ty : Bool}
    (hc : NoMonochromaticTriangle c) (h : Normalized c tx ty) : Conditions c :=
  ⟨rows_embed c hc h.named,columns_embed c hc h.named,
    row_guard c hc h.named h.spokes,column_guard c hc h.named h.spokes⟩

theorem actual_three_owner_conditions (c : Host) (hc : NoMonochromaticTriangle c)
    (hu : UniformCommonHighPair c) :
    ∃ d : Host, NoMonochromaticTriangle d ∧ ∃ o : Owner,
      Normalized d o.left o.right ∧ Conditions d := by
  obtain ⟨d,hd,o,h⟩ := uniform_to_three_owners c hc hu
  exact ⟨d,hd,o,h,normalized_conditions hd h⟩

#print axioms actual_subset_embeds
#print axioms actual_three_owner_conditions
end UniformK61.BalancedVisible
