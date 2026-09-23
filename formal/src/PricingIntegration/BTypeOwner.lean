import PricingIntegration.ABTypeOwner
set_option autoImplicit false
namespace PricingIntegration.BTypeOwner
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open Ramsey61.CPhysicalNormalization PricingIntegration.FixedPhysicalNeighborhood
open PricingIntegration.ABDRootPalette PricingIntegration.BActualFrame
open PricingIntegration.PhysicalTypeTransport PricingIntegration.ABTypeOwner

structure Cells (c : Host) (r : Vertex) where
  mt : Bool
  xt : Bool
  qt : Bool
  m : PhysicalNeighborhoodMap c r (palette 1) (R4333.k15Template mt)
  x : PhysicalNeighborhoodMap c r (palette 2) (R4333.k16Template xt)
  q : PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template qt)
  mp : m.colors=foreignEquiv 1
  xp : x.colors=foreignEquiv 2
  qp : q.colors=foreignEquiv 3

@[simp] theorem global_one_1 : globalPalette 1 (palette 1)=palette 1 := by rw [globalPalette_apply];rfl
@[simp] theorem global_one_2 : globalPalette 1 (palette 2)=palette 3 := by rw [globalPalette_apply];rfl
@[simp] theorem global_one_3 : globalPalette 1 (palette 3)=palette 2 := by rw [globalPalette_apply];rfl

theorem Cells.exchange {c : Host} {r : Vertex} (b : Cells c r) :
    ∃n : Cells (relabel c (Equiv.refl _) (globalPalette 1)) r,
      n.mt=b.mt ∧ n.xt=b.qt ∧ n.qt=b.xt := by
  have mm : PhysicalNeighborhoodMap c r (globalPalette 1 (palette 1)) (R4333.k15Template b.mt) := by rw [global_one_1];exact b.m
  have xx : PhysicalNeighborhoodMap c r (globalPalette 1 (palette 2)) (R4333.k16Template b.qt) := by rw [global_one_2];exact b.q
  have qq : PhysicalNeighborhoodMap c r (globalPalette 1 (palette 3)) (R4333.k16Template b.xt) := by rw [global_one_3];exact b.x
  obtain ⟨m,hm⟩ := k15_repalette (physical_relabel (globalPalette 1) (palette 1) mm) (foreignEquiv 1)
  obtain ⟨x,hx⟩ := k16_repalette (physical_relabel (globalPalette 1) (palette 2) xx) (foreignEquiv 2)
  obtain ⟨q,hq⟩ := k16_repalette (physical_relabel (globalPalette 1) (palette 3) qq) (foreignEquiv 3)
  exact ⟨⟨b.mt,b.qt,b.xt,m,x,q,hm,hx,hq⟩,rfl,rfl,rfl⟩

theorem cells_of_ordered (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : ∀q : Color,colorDegree c (palette q) r=shape 1 q) :
    Nonempty (Cells c r) := by
  obtain ⟨mt,m,hm⟩ := physical_k15_fixed_palette c hc r (palette 1) (hd 1) (foreignEquiv 1)
  obtain ⟨xt,x,hx⟩ := physical_k16_fixed_palette c hc r (palette 2) (hd 2) (foreignEquiv 2)
  obtain ⟨qt,q,hq⟩ := physical_k16_fixed_palette c hc r (palette 3) (hd 3) (foreignEquiv 3)
  exact ⟨⟨mt,xt,qt,m,x,q,hm,hx,hq⟩⟩

theorem high_mark_in_same_type {c : Host} (hc : NoMonochromaticTriangle c)
    {r : Vertex} (b : Cells c r) (hd : colorDegree c (palette 3) r=16) (hh : 47≤H c r) :
    ∃m : PhysicalNeighborhoodMap c r (palette 3) (R4333.k16Template b.qt),
      m.colors=foreignEquiv 3 ∧ 15≤colorDegree c (palette 3) (m.vertex 15) := by
  obtain ⟨mark,hm,hhigh,_⟩ := supplied_ABD_has_attaching_mark c hc r (palette 3) hd (by omega)
  obtain ⟨m,hpal,hmark⟩ := k16_remark b.q mark hm
  exact ⟨m,hpal.trans b.qp,by rw [hmark];exact hhigh⟩

/-- Every orderedB root reaches oneof the six retainedtype owners, followed
by a genuinehigh mark in its actual16cell. No marking-independenttype assumption. -/
theorem ordered_B_native_owner (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : ∀q : Color,colorDegree c (palette q) r=shape 1 q)
    (hh : 47≤H c r) :
    ∃σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧ W d r=W c r ∧
      (∀q : Color,colorDegree d (palette q) r=shape 1 q) ∧
      ∃b : Cells d r,(b.xt=false ∨ b.qt=true) ∧
      ∃m : PhysicalNeighborhoodMap d r (palette 3) (R4333.k16Template b.qt),
        m.colors=foreignEquiv 3 ∧ 15≤colorDegree d (palette 3) (m.vertex 15) := by
  obtain ⟨b⟩ := cells_of_ordered c hc r hd
  by_cases ho : b.xt=false ∨ b.qt=true
  · have he : relabel c (Equiv.refl _) (Equiv.refl _)=c := by cases c;rfl
    refine ⟨Equiv.refl _,?_⟩
    rw [he]
    exact ⟨hc,rfl,rfl,hd,b,ho,high_mark_in_same_type hc b (hd 3) hh⟩
  · have hxt : b.xt=true := by cases h:b.xt <;> simp_all
    have hqt : b.qt=false := by cases h:b.qt <;> simp_all
    obtain ⟨n,hm,hx,hq⟩ := b.exchange
    let d := relabel c (Equiv.refl _) (globalPalette 1)
    have good : NoMonochromaticTriangle d := relabel_noMono c hc _ _
    have hH : H d r=H c r := relabel_H c _ _ _
    have hW : W d r=W c r := relabel_W c _ _ _
    have hdegree : ∀q : Color,colorDegree d (palette q) r=shape 1 q := by
      intro q
      simp only [d,relabel_degree,Equiv.refl_apply,globalPalette_apply]
      rw [hd]
      fin_cases q <;> rfl
    refine ⟨globalPalette 1,good,hH,hW,hdegree,n,Or.inl (hx.trans hqt),?_⟩
    exact high_mark_in_same_type good n (hdegree 3) (by rw [hH];exact hh)

#print axioms ordered_B_native_owner
end PricingIntegration.BTypeOwner
