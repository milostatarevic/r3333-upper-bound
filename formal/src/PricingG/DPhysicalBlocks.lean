import PricingIntegration.BSupportedBlocks
import PricingC.MixedUTFrame

set_option autoImplicit false
namespace PricingG.DPhysicalBlocks
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingIntegration.FixedPhysicalNeighborhood PricingIntegration.ABDRootPalette
open PricingIntegration.BActualFrame

/-- Complete physical critical cells of a supplied D root. The free block is
exactly its selected endpoint's actual low-cell attaching support. -/
structure Blocks (c : Host) (r : Vertex) (k : Nat) where
  free : Fin k ↪ Vertex
  mType : Bool
  xType : Bool
  qType : Bool
  m : PhysicalNeighborhoodMap c r (palette 1) (R4333.k15Template mType)
  x : PhysicalNeighborhoodMap c r (palette 2) (R4333.k15Template xType)
  q : PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template qType)
  free_mem : ∀ i, free i ∈ colorNeighborhood c (palette 0) r
  m_palette : m.colors = foreignEquiv 1
  x_palette : x.colors = foreignEquiv 2
  q_palette : q.colors = foreignEquiv 3
  marked_high : 15 ≤ colorDegree c (palette 3) (q.vertex 15)
  free_own : ∀ i, c (q.vertex 15) (free i) = palette 3
  free_exact : ∀ v, v ∈ attachingSupport c r (palette 3) (q.vertex 15) (palette 0) ↔ ∃ i, free i = v

/-- Same-host construction with a supplied high mark. All cell maps use the
native increasing foreign palettes, and marked label15 is the supplied mark. -/
theorem supported_D_blocks (c : Host) (hc : NoMonochromaticTriangle c)
    (r mark : Vertex) (hd : ∀ q : Color, colorDegree c (palette q) r = shape 2 q)
    (hm : mark ∈ colorNeighborhood c (palette 3) r) (hhigh : 15 ≤ colorDegree c (palette 3) mark)
    (k : Nat) (hcard : (attachingSupport c r (palette 3) mark (palette 0)).card = k) :
    ∃ b : Blocks c r k, b.q.vertex 15 = mark := by
  classical
  let S := attachingSupport c r (palette 3) mark (palette 0)
  let se : S ≃ Fin k := Fintype.equivFinOfCardEq (by simpa [S] using hcard)
  let free : Fin k ↪ Vertex := ⟨fun i => (se.symm i).val,fun i j he => se.symm.injective (Subtype.ext he)⟩
  obtain ⟨mt,m,hmp⟩ := physical_k15_fixed_palette c hc r (palette 1) (hd 1) (foreignEquiv 1)
  obtain ⟨xt,x,hxp⟩ := physical_k15_fixed_palette c hc r (palette 2) (hd 2) (foreignEquiv 2)
  obtain ⟨qt,q,hqp,hmarked⟩ := physical_k16_marked_fixed_palette c hc r (palette 3) (hd 3) mark hm (foreignEquiv 3)
  refine ⟨⟨free,mt,xt,qt,m,x,q,?_,hmp,hxp,hqp,?_,?_,?_⟩,hmarked⟩
  · intro i
    exact (mem_inter.mp (se.symm i).property).2
  · simpa only [hmarked] using hhigh
  · intro i
    rw [hmarked]
    exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (se.symm i).property).1).2
  · intro v
    rw [hmarked]
    constructor
    · intro hv
      refine ⟨se ⟨v,hv⟩,?_⟩
      change (se.symm (se ⟨v,hv⟩)).val = v
      simp
    · rintro ⟨i,rfl⟩
      exact (se.symm i).property

/-- The actual ordered root supplies a complete physical4/5 support split;
no U/T kind is chosen prematurely. -/
theorem ordered_D_has_supported_blocks (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : ∀ q : Color, colorDegree c (palette q) r = shape 2 q)
    (hh : 46 ≤ H c r) :
    ∃ k : Nat, (k = 4 ∨ k = 5) ∧ Nonempty (Blocks c r k) := by
  obtain ⟨mark,hm,hhigh,_⟩ := supplied_ABD_has_attaching_mark c hc r (palette 3) (hd 3) hh
  have hcard := PricingIntegration.BSupportedBlocks.low_support_four_or_five c hc r mark hm hhigh
  rcases hcard with hfour | hfive
  · obtain ⟨b,_⟩ := supported_D_blocks c hc r mark hd hm hhigh 4 hfour
    exact ⟨4,Or.inl rfl,⟨b⟩⟩
  · obtain ⟨b,_⟩ := supported_D_blocks c hc r mark hd hm hhigh 5 hfive
    exact ⟨5,Or.inr rfl,⟨b⟩⟩

/-- Actual D selection to complete actual-cell maps and exact attaching
supports, under one global palette permutation preserving root and H. -/
theorem actual_D_physical_blocks (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r = 46) (hh : 46 ≤ H c r) :
    ∃ σ : FourColor ≃ FourColor,
      let d := Ramsey61.CPhysicalNormalization.relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r = H c r ∧
      (∀ q : Color,colorDegree d (palette q) r = shape 2 q) ∧
      ∃ k : Nat,(k = 4 ∨ k = 5) ∧ Nonempty (Blocks d r k) := by
  obtain ⟨σ,hc',hd,hH⟩ := actual_ABD_root_ordered 2 c hc r hw
  refine ⟨σ,hc',hH,hd,?_⟩
  apply ordered_D_has_supported_blocks _ hc' r hd
  simpa only [hH] using hh

private theorem m_palette_eq (a : Fin 3) : (foreignEquiv 1 a).val = PricingC.MixedUT.mPalette a := by fin_cases a <;> rfl
private theorem x_palette_eq (a : Fin 3) : (foreignEquiv 2 a).val = PricingC.MixedUT.xPalette a := by fin_cases a <;> rfl
private theorem q_palette_eq (a : Fin 3) : (foreignEquiv 3 a).val = PricingC.MixedUT.qPalette a := by fin_cases a <;> rfl

/-- Adapter for the mixed U/T owner, keeping exactly the original61 vertices
and the entire maps, rather than assuming an unrelated canonical frame. -/
noncomputable def Blocks.mixedUT {c : Host} {r : Vertex} {k : Nat} (b : Blocks c r k)
    (hm : b.mType = false) (hx : b.xType = true) : PricingC.MixedUT.Frame c k b.qType where
  root := r
  free := b.free
  left := b.m.vertex
  right := b.x.vertex
  marked := b.q.vertex
  free_mem := b.free_mem
  left_mem := b.m.mem_neighborhood
  right_mem := b.x.mem_neighborhood
  marked_mem := b.q.mem_neighborhood
  left_edges a d had := by
    have h := b.m.map_color a d had
    rw [b.m_palette,m_palette_eq] at h
    simpa [hm,R4333.k15Template] using h
  right_edges a d had := by
    have h := b.x.map_color a d had
    rw [b.x_palette,x_palette_eq] at h
    simpa [hx,R4333.k15Template] using h
  marked_edges a d had := by
    have h := b.q.map_color a d had
    rw [b.q_palette,q_palette_eq] at h
    exact h

#print axioms supported_D_blocks
#print axioms actual_D_physical_blocks
#print axioms Blocks.mixedUT
end PricingG.DPhysicalBlocks
