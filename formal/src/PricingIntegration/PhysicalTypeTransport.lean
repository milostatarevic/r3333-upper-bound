import PricingIntegration.BActualFrame

set_option autoImplicit false
namespace PricingIntegration.PhysicalTypeTransport
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open Ramsey61.CPhysicalNormalization PricingIntegration.FixedPhysicalNeighborhood

/-- Transport foreign colors by the one global palette permutation. -/
def foreignTransport (σ : FourColor ≃ FourColor) (q : FourColor) :
    {a : FourColor // a ≠ σ q} ≃ {a : FourColor // a ≠ q} where
  toFun a := ⟨σ.symm a.val,by intro h;apply a.property;simpa using congrArg σ h⟩
  invFun a := ⟨σ a.val,by intro h;exact a.property (σ.injective h)⟩
  left_inv a := by apply Subtype.ext;exact σ.apply_symm_apply a.val
  right_inv a := by apply Subtype.ext;exact σ.symm_apply_apply a.val

noncomputable def physical_relabel {n : Nat} {c : Host} {r : Vertex}
    {t : R4333.EdgeColoring (Fin n) (Fin 3)} (σ : FourColor ≃ FourColor) (q : FourColor)
    (m : PhysicalNeighborhoodMap c r (σ q) t) :
    PhysicalNeighborhoodMap (relabel c (Equiv.refl _) σ) r q t where
  vertex := m.vertex
  colors := m.colors.trans (foreignTransport σ q)
  mem_neighborhood i := by
    simpa [mem_colorNeighborhood,relabel,Equiv.symm_apply_eq] using m.mem_neighborhood i
  covers_neighborhood v hv := by
    apply m.covers_neighborhood v
    simpa [mem_colorNeighborhood,relabel,Equiv.symm_apply_eq] using hv
  map_color a b hab := congrArg σ.symm (m.map_color a b hab)

/-- Fixing the displayed local palette never changes the critical type. -/
theorem k16_repalette {c : Host} {r : Vertex} {q : FourColor} {t : Bool}
    (m : PhysicalNeighborhoodMap c r q (R4333.k16Template t))
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ n : PhysicalNeighborhoodMap c r q (R4333.k16Template t),n.colors=pal := by
  let e := m.colors.trans pal.symm
  obtain ⟨v,hv⟩ := R4333.k16Template_fullPaletteSymmetry t e.symm
  refine ⟨mapOfNormalization m pal v ?_,rfl⟩
  intro a b hab
  change e (R4333.k16Template t (v a) (v b))=R4333.k16Template t a b
  rw [hv a b hab,Equiv.apply_symm_apply]

theorem k15_repalette {c : Host} {r : Vertex} {q : FourColor} {t : Bool}
    (m : PhysicalNeighborhoodMap c r q (R4333.k15Template t))
    (pal : Fin 3 ≃ {a : FourColor // a ≠ q}) :
    ∃ n : PhysicalNeighborhoodMap c r q (R4333.k15Template t),n.colors=pal := by
  let e := m.colors.trans pal.symm
  obtain ⟨v,hv⟩ := R4333.k15Template_fullPaletteSymmetry t e.symm
  refine ⟨mapOfNormalization m pal v ?_,rfl⟩
  intro a b hab
  change e (R4333.k15Template t (v a) (v b))=R4333.k15Template t a b
  rw [hv a b hab,Equiv.apply_symm_apply]

/-- A chosen physical high endpoint is moved to15 with the same U/T type,
all colors unchanged, and a bijection of the whole critical cell. -/
theorem k16_remark {c : Host} {r : Vertex} {q : FourColor} {t : Bool}
    (m : PhysicalNeighborhoodMap c r q (R4333.k16Template t))
    (mark : Vertex) (hm : mark∈colorNeighborhood c q r) :
    ∃ n : PhysicalNeighborhoodMap c r q (R4333.k16Template t),
      n.colors=m.colors ∧ n.vertex 15=mark := by
  obtain ⟨i,hi⟩ := m.covers_neighborhood mark hm
  let a := R4333.k16TemplateToLastEquiv t i
  have hai : a i=15 := R4333.k16TemplateToLastMap_deleted t i
  have har : a.symm 15=i := by rw [←hai];simp
  have hp : ∀ u v,u≠v → modelInPalette m m.colors (a.symm u) (a.symm v)=R4333.k16Template t u v := by
    intro u v huv
    change m.colors.symm (m.colors (R4333.k16Template t (a.symm u) (a.symm v)))=_
    rw [Equiv.symm_apply_apply]
    have h := R4333.k16TemplateToLastMap_preserves t i (a.symm u) (a.symm v) (a.symm.injective.ne huv)
    change R4333.k16Template t (a.symm u) (a.symm v)=R4333.k16Template t (a (a.symm u)) (a (a.symm v)) at h
    simpa only [Equiv.apply_symm_apply] using h
  refine ⟨mapOfNormalization m m.colors a.symm hp,rfl,?_⟩
  change m.vertex (a.symm 15)=mark
  rw [har,hi]

#print axioms physical_relabel
#print axioms k16_repalette
#print axioms k16_remark
end PricingIntegration.PhysicalTypeTransport
