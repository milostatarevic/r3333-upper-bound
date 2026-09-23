import PricingC.SharedAnchor
import Ramsey61.CAnchorGeometry

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase Ramsey61.CAnchorGeometry

noncomputable def paletteX : Fin 3 ≃ {q : FourColor // q ≠ palette 0} :=
  Equiv.ofBijective (fun i => ⟨(![palette 2,palette 1,palette 3] : Fin 3 → FourColor) i,
    by fin_cases i <;> decide⟩) (by decide)
noncomputable def paletteS : Fin 3 ≃ {q : FourColor // q ≠ palette 2} :=
  Equiv.ofBijective (fun i => ⟨(![palette 0,palette 1,palette 3] : Fin 3 → FourColor) i,
    by fin_cases i <;> decide⟩) (by decide)
noncomputable def paletteY : Fin 3 ≃ {q : FourColor // q ≠ palette 1} :=
  Equiv.ofBijective (fun i => ⟨(![palette 2,palette 0,palette 3] : Fin 3 → FourColor) i,
    by fin_cases i <;> decide⟩) (by decide)

@[simp] theorem paletteX_zero : (paletteX 0).val = palette 2 := rfl
@[simp] theorem paletteS_zero : (paletteS 0).val = palette 0 := rfl
@[simp] theorem paletteY_zero : (paletteY 0).val = palette 2 := rfl

 theorem paletteXS_cycle : ∀ j k : Fin 5, j ≠ k →
    (paletteX (AnchorTables.cycleColor j k)).val = (paletteS (AnchorTables.cycleColor j k)).val := by decide

 theorem physical_root_block_cover : ∀ v : Vertex, v ≠ 0 → ∃ q : Color, v ∈ rootBlocks q := by decide

 theorem root_block_nonzero : ∀ (q : Color) (v : Vertex), v ∈ rootBlocks q → v ≠ 0 := by decide

 theorem normalized_root_neighborhood (c : Host) (hroot : RootConditions c) (q : Color) :
    colorNeighborhood c (palette q) 0 = (rootBlocks q).toFinset := by
  ext v
  constructor
  · intro hv
    have hv' := (mem_colorNeighborhood c _ _ _).mp hv
    obtain ⟨r,hr⟩ := physical_root_block_cover v hv'.1
    have heq : r = q := palette_injective ((hroot.1 r v hr).symm.trans hv'.2)
    simpa only [heq,List.mem_toFinset] using hr
  · intro hv
    have hv := List.mem_toFinset.mp hv
    exact (mem_colorNeighborhood c _ _ _).mpr ⟨root_block_nonzero q v hv,hroot.1 q v hv⟩

 theorem normalized_root_degree (c : Host) (hroot : RootConditions c) (q : Color) :
    colorDegree c (palette q) 0 = if q.val < 2 then 16 else 14 := by
  change (colorNeighborhood c (palette q) 0).card = _
  rw [normalized_root_neighborhood c hroot q]
  fin_cases q <;> decide

 theorem neighborhood_pair_avoids (c : Host) (hc : NoMonochromaticTriangle c)
    (p : Vertex) (q : FourColor) (u v : Vertex)
    (hu : u ∈ colorNeighborhood c q p) (hv : v ∈ colorNeighborhood c q p)
    (huv : u ≠ v) : c u v ≠ q := by
  have hu' := (mem_colorNeighborhood c _ _ _).mp hu
  have hv' := (mem_colorNeighborhood c _ _ _).mp hv
  intro hcol
  exact hc p u v ⟨Ne.symm hu'.1,Ne.symm hv'.1,huv⟩ ⟨hu'.2.trans hv'.2.symm,hv'.2.trans hcol.symm⟩

 theorem root_in_marked_scope (c : Host) (hroot : RootConditions c) :
    (0 : Vertex) ∈ colorNeighborhood c (palette 2) 33 := by
  apply (mem_colorNeighborhood c _ _ _).mpr
  refine ⟨by decide,?_⟩
  rw [c.color_symm]
  exact hroot.1 2 33 (by decide)

/-- Inside S, the full actual five-anchor is exactly the designated
neighborhood of the actual root, even if S has one formal missing point. -/
theorem full_anchor_root_center (c : Host) (hroot : RootConditions c)
    (ms : CompletedScope c 33 (palette 2) paletteS)
    (a : Fin 5 ↪ ms.present)
    (ha : ∀ j, ms.vertex (a j) ∈ colorNeighborhood c (palette 0) 0)
    (rs : ms.present) (hrs : ms.vertex rs = 0) :
    referenceAnchor ms a = R4333.colorNeighborhood ms.model 0 rs.val := by
  have hsub : referenceAnchor ms a ⊆ R4333.colorNeighborhood ms.model 0 rs.val := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    have hp := (mem_colorNeighborhood c _ _ _).mp (ha j)
    have hne : a j ≠ rs := by
      intro e
      exact hp.1 ((congrArg ms.vertex e).trans hrs)
    apply (R4333.mem_colorNeighborhood ms.model 0 rs.val (a j).val).mpr
    refine ⟨fun e => hne (Subtype.ext e),?_⟩
    have hm := ms.map_color rs (a j) (Ne.symm hne)
    rw [hrs] at hm
    have he : (paletteS (ms.model rs.val (a j).val)).val = (paletteS 0).val := hm.symm.trans hp.2
    exact paletteS.injective (Subtype.ext he)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [referenceAnchor_card]
  exact le_of_eq (R4333.threeColor_degree_eq_five_at_16 ms.model ms.good 0 rs.val)

#print axioms full_anchor_root_center
#print axioms normalized_root_degree
end PricingC
