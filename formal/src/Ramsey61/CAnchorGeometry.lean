import Ramsey61.CPhysicalNormalization
import Ramsey61.ABDExtraction

namespace Ramsey61.CAnchorGeometry
open Finset CEncodingCore CEncodingBase CPhysicalNormalization

/-- Actual marked color-2 neighbors in one actual root cell. -/
def anchorSupport (c : Host) (q : Color) : Finset Vertex :=
  colorNeighborhood c (palette 2) 33 ∩ colorNeighborhood c (palette q) 0

def anchorSize (c : Host) (q : Color) : Nat := (anchorSupport c q).card

theorem marked_in_root_low_cell (c : Host) (hroot : RootConditions c) :
    (33 : Vertex) ∈ colorNeighborhood c (palette 2) 0 := by
  apply (mem_colorNeighborhood c _ _ _).mpr
  exact ⟨by decide, hroot.1 2 33 (by decide)⟩

/-- The four size patterns concern physical intersections, not freely chosen
abstract supports or independently completed neighborhoods. -/
theorem normalized_marked_anchor_patterns (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (hmarked : 15 ≤ colorDegree c (palette 2) 33) :
    FourFivePattern (anchorSize c 0) (anchorSize c 1) (anchorSize c 3) := by
  have hx := marked_in_root_low_cell c hroot
  have hsum := attachingSupport_partition c hc 0 (palette 2) 33 hx
  have hcolors : (univ : Finset FourColor).erase (palette 2) =
      {palette 0, palette 1, palette 3} := by decide
  rw [hcolors] at hsum
  simp only [sum_insert, mem_insert, mem_singleton,
    show palette 0 ≠ palette 1 by decide, show palette 0 ≠ palette 3 by decide,
    show palette 1 ≠ palette 3 by decide, false_or, not_false_eq_true, sum_singleton] at hsum
  have hupper := fourColor_colorDegree_le_sixteen c hc (palette 2) 33
  have h0 : anchorSize c 0 ≤ 5 :=
    different_color_intersection_le_five c hc (palette 2) (palette 0) (by decide) 33 0
  have h1 : anchorSize c 1 ≤ 5 :=
    different_color_intersection_le_five c hc (palette 2) (palette 1) (by decide) 33 0
  have h3 : anchorSize c 3 ≤ 5 :=
    different_color_intersection_le_five c hc (palette 2) (palette 3) (by decide) 33 0
  change colorDegree c (palette 2) 33 - 1 = anchorSize c 0 + (anchorSize c 1 + anchorSize c 3) at hsum
  unfold FourFivePattern
  omega

/-- A single bijection transports intersection cardinalities with both
colors and both centers, including overlaps. -/
theorem relabel_intersection_card (c : Host) (e : Vertex ≃ Vertex)
    (σ : FourColor ≃ FourColor) (p q : FourColor) (x r : Vertex) :
    (colorNeighborhood (relabel c e σ) p x ∩ colorNeighborhood (relabel c e σ) q r).card =
      (colorNeighborhood c (σ p) (e x) ∩ colorNeighborhood c (σ q) (e r)).card := by
  apply Finset.card_bij (fun u _ => e u)
  · intro u hu
    simpa [mem_inter, mem_colorNeighborhood, relabel, Equiv.symm_apply_eq] using hu
  · intro u hu v hv h; exact e.injective h
  · intro u hu
    refine ⟨e.symm u, ?_, by simp⟩
    simpa [mem_inter, mem_colorNeighborhood, relabel, Equiv.symm_apply_eq] using hu

def swapHighVertexFn (v : Vertex) : Vertex :=
  ⟨if v.val = 0 then 0 else if v.val ≤ 16 then v.val + 16
    else if v.val ≤ 32 then v.val - 16 else v.val, by
    have hv := v.isLt
    split_ifs <;> omega⟩

def swapHighVertices : Vertex ≃ Vertex where
  toFun := swapHighVertexFn
  invFun := swapHighVertexFn
  left_inv := by decide
  right_inv := by decide

def swapHighPalette : FourColor ≃ FourColor := Equiv.swap (palette 0) (palette 1)

def swapHighIndex (q : Color) : Color := if q = 0 then 1 else if q = 1 then 0 else q

set_option maxRecDepth 10000 in
theorem swapHigh_preserves_blocks : ∀ q v, v ∈ rootBlocks q →
    swapHighVertices v ∈ rootBlocks (swapHighIndex q) := by decide

theorem swapHigh_palette_index : ∀ q, swapHighPalette (palette q) = palette (swapHighIndex q) := by decide

@[simp] theorem swapHigh_zero : swapHighVertices 0 = 0 := by decide
@[simp] theorem swapHigh_marked : swapHighVertices 33 = 33 := by decide
@[simp] theorem swapHigh_palette_zero : swapHighPalette (palette 0) = palette 1 := by decide
@[simp] theorem swapHigh_palette_one : swapHighPalette (palette 1) = palette 0 := by decide
@[simp] theorem swapHigh_palette_two : swapHighPalette (palette 2) = palette 2 := by decide
@[simp] theorem swapHigh_palette_three : swapHighPalette (palette 3) = palette 3 := by decide

theorem swapHigh_root_conditions (c : Host) (hroot : RootConditions c) :
    RootConditions (relabel c swapHighVertices swapHighPalette) := by
  constructor
  · intro q v hv
    change swapHighPalette.symm (c (swapHighVertices 0) (swapHighVertices v)) = palette q
    rw [swapHigh_zero, hroot.1 (swapHighIndex q) (swapHighVertices v)
      (swapHigh_preserves_blocks q v hv), ← swapHigh_palette_index q,
      swapHighPalette.symm_apply_apply]
  · simpa only [relabel_H, swapHigh_zero] using hroot.2

theorem swapHigh_marked_degree (c : Host) :
    colorDegree (relabel c swapHighVertices swapHighPalette) (palette 2) 33 =
      colorDegree c (palette 2) 33 := by
  rw [relabel_degree, swapHigh_palette_two, swapHigh_marked]

theorem swapHigh_anchor_sizes (c : Host) :
    anchorSize (relabel c swapHighVertices swapHighPalette) 0 = anchorSize c 1 ∧
    anchorSize (relabel c swapHighVertices swapHighPalette) 1 = anchorSize c 0 ∧
    anchorSize (relabel c swapHighVertices swapHighPalette) 3 = anchorSize c 3 := by
  simp [anchorSize, anchorSupport, relabel_intersection_card]

def ThreeAnchorShapes (c : Host) : Prop :=
  anchorSize c 0 = 5 ∧
    ((anchorSize c 1 = 5 ∧ anchorSize c 3 = 5) ∨
     (anchorSize c 1 = 5 ∧ anchorSize c 3 = 4) ∨
     (anchorSize c 1 = 4 ∧ anchorSize c 3 = 5))

/-- One simultaneous high-cell/color exchange suffices for the exact physical
555/554/545 entrance. This theorem makes no matrix, orbit or seed-cover claim. -/
theorem normalized_host_has_three_anchor_shapes (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (hroot : RootConditions c)
    (hmarked : 15 ≤ colorDegree c (palette 2) 33) :
    ∃ (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor),
      NoMonochromaticTriangle (relabel c e σ) ∧ SelectorX (relabel c e σ) ∧
      RootConditions (relabel c e σ) ∧ 15 ≤ colorDegree (relabel c e σ) (palette 2) 33 ∧
      ThreeAnchorShapes (relabel c e σ) := by
  have h := normalized_marked_anchor_patterns c hc hroot hmarked
  by_cases hfirst : anchorSize c 0 = 4
  · refine ⟨swapHighVertices, swapHighPalette, relabel_noMono c hc _ _,
      relabel_selector c selectors _ _, swapHigh_root_conditions c hroot, ?_, ?_⟩
    · simpa only [swapHigh_marked_degree] using hmarked
    · have hs := swapHigh_anchor_sizes c
      unfold ThreeAnchorShapes
      rw [hs.1, hs.2.1, hs.2.2]
      unfold FourFivePattern at h
      omega
  · refine ⟨Equiv.refl _, Equiv.refl _, ?_⟩
    have heq : relabel c (Equiv.refl _) (Equiv.refl _) = c := rfl
    rw [heq]
    refine ⟨hc, selectors, hroot, hmarked, ?_⟩
    unfold ThreeAnchorShapes FourFivePattern at *
    omega

/-- The actual C exterior witness supplies the three physical anchor shapes
and the same normalized host's base valuation, under one composed global
vertex bijection and one composed global palette permutation. -/
theorem exterior_witness_supplies_three_anchor_base (c : Host) (hc : NoMonochromaticTriangle c)
    (selectors : SelectorX c) (witness : CExteriorWitness c) :
    ∃ (e : Vertex ≃ Vertex) (σ : FourColor ≃ FourColor),
      NoMonochromaticTriangle (relabel c e σ) ∧ SelectorX (relabel c e σ) ∧
      RootConditions (relabel c e σ) ∧ 15 ≤ colorDegree (relabel c e σ) (palette 2) 33 ∧
      ThreeAnchorShapes (relabel c e σ) ∧
      DenseCounter.FormulaSat (baseValuation (relabel c e σ)) broaderBaseCNF := by
  obtain ⟨e₁, σ₁, hgood₁, hselector₁, hroot₁, hmarked₁⟩ :=
    exterior_witness_normalized c hc selectors witness
  obtain ⟨e₂, σ₂, hgood₂, hselector₂, hroot₂, hmarked₂, hshapes⟩ :=
    normalized_host_has_three_anchor_shapes (relabel c e₁ σ₁)
      hgood₁ hselector₁ hroot₁ hmarked₁
  have heq : relabel (relabel c e₁ σ₁) e₂ σ₂ = relabel c (e₂.trans e₁) (σ₂.trans σ₁) := rfl
  refine ⟨e₂.trans e₁, σ₂.trans σ₁, ?_⟩
  rw [← heq]
  exact ⟨hgood₂, hselector₂, hroot₂, hmarked₂, hshapes,
    coloring_satisfies_broaderBase _ hgood₂ hselector₂ hroot₂⟩

end Ramsey61.CAnchorGeometry
