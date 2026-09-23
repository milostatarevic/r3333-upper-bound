import PricingIntegration.BActualGeometry

set_option autoImplicit false
namespace PricingIntegration.BSupportedBlocks
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter Finset
open PricingIntegration.FixedPhysicalNeighborhood PricingIntegration.ABDRootPalette
open PricingIntegration.BActualFrame PricingIntegration.BActualGeometry

/-- Every actual high marked endpoint has exactly four or five attachments
in the low root cell. No zero-covered cases are omitted. -/
theorem low_support_four_or_five (c : Host) (hc : NoMonochromaticTriangle c)
    (r mark : Vertex) (hm : mark∈colorNeighborhood c (palette 3) r)
    (hh : 15≤colorDegree c (palette 3) mark) :
    (attachingSupport c r (palette 3) mark (palette 0)).card=4 ∨
      (attachingSupport c r (palette 3) mark (palette 0)).card=5 := by
  obtain ⟨p0,p1,p2,_,_,_,heq,hpat⟩ := genuine_high_attaching_support_geometry c hc r (palette 3) mark hm hh
  have hmem : palette 0∈({p0,p1,p2} : Finset FourColor) := by rw [←heq];decide
  simp only [mem_insert,mem_singleton] at hmem
  unfold FourFivePattern at hpat
  rcases hmem with he|he|he <;> subst_vars <;> rcases hpat with h|h|h|h <;> omega

/-- For the five-support branch, the retained free block is the entire
actual attaching support, while every foreign critical cell is complete. -/
theorem supported_B_blocks (c : Host) (hc : NoMonochromaticTriangle c)
    (r mark : Vertex) (hd : ∀ q : Color,colorDegree c (palette q) r=shape 1 q)
    (hm : mark∈colorNeighborhood c (palette 3) r) (hhigh : 15≤colorDegree c (palette 3) mark)
    (hcard : (attachingSupport c r (palette 3) mark (palette 0)).card=5) :
    ∃ b : Blocks c r,b.q.vertex 15=mark ∧
      (∀ i,c (b.q.vertex 15) (b.free i)=palette 3) ∧
      (∀ v,v∈attachingSupport c r (palette 3) mark (palette 0) ↔ ∃ i,b.free i=v) := by
  classical
  let S := attachingSupport c r (palette 3) mark (palette 0)
  let se : S ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa [S] using hcard)
  let free : Fin 5 ↪ Vertex := ⟨fun i => (se.symm i).val,fun i j he => se.symm.injective (Subtype.ext he)⟩
  obtain ⟨mt,m,hmp⟩ := physical_k15_fixed_palette c hc r (palette 1) (hd 1) (foreignEquiv 1)
  obtain ⟨xt,x,hxp⟩ := physical_k16_fixed_palette c hc r (palette 2) (hd 2) (foreignEquiv 2)
  obtain ⟨qt,q,hqp,hmarked⟩ := physical_k16_marked_fixed_palette c hc r (palette 3) (hd 3) mark hm (foreignEquiv 3)
  have hfree : ∀ i,free i∈colorNeighborhood c (palette 0) r := by
    intro i
    exact (mem_inter.mp (se.symm i).property).2
  have hmark : q.vertex 15∈Incoming c r := by
    rw [hmarked]
    have hz := (mem_colorNeighborhood _ _ _ _).mp hm
    exact (mem_highOwnNeighborSupport c r mark).mpr ⟨hz.1,by simpa only [hz.2] using hhigh⟩
  let b : Blocks c r := ⟨free,mt,xt,qt,m,x,q,hfree,hmp,hxp,hqp,hmark⟩
  refine ⟨b,hmarked,?_,?_⟩
  · intro i
    change c (q.vertex 15) (free i)=palette 3
    rw [hmarked]
    exact ((mem_colorNeighborhood _ _ _ _).mp (mem_inter.mp (se.symm i).property).1).2
  · intro v
    constructor
    · intro hv
      refine ⟨se ⟨v,hv⟩,?_⟩
      change (se.symm (se ⟨v,hv⟩)).val=v
      simp
    · rintro ⟨i,rfl⟩
      exact (se.symm i).property

/-- The actual suppliedB root reaches the complete marked-support split
under one global palette permutation. -/
theorem actual_B_support_split (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r=47) (hh : 47≤H c r) :
    ∃ σ : FourColor ≃ FourColor,
      let d := Ramsey61.CPhysicalNormalization.relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧
      (∀ q : Color,colorDegree d (palette q) r=shape 1 q) ∧
      ∃ mark,mark∈colorNeighborhood d (palette 3) r ∧ 15≤colorDegree d (palette 3) mark ∧
       ((attachingSupport d r (palette 3) mark (palette 0)).card=4 ∨
        (attachingSupport d r (palette 3) mark (palette 0)).card=5) := by
  obtain ⟨σ,hc',hd,hH⟩ := actual_ABD_root_ordered 1 c hc r hw
  let d := Ramsey61.CPhysicalNormalization.relabel c (Equiv.refl _) σ
  have hh' : 46≤H d r := by rw [hH];omega
  obtain ⟨mark,hm,hhigh,_⟩ := supplied_ABD_has_attaching_mark d hc' r (palette 3) (hd 3) hh'
  exact ⟨σ,hc',hH,hd,mark,hm,hhigh,low_support_four_or_five d hc' r mark hm hhigh⟩

#print axioms supported_B_blocks
#print axioms actual_B_support_split
end PricingIntegration.BSupportedBlocks
