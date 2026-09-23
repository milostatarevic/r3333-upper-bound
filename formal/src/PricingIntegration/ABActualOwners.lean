import PricingIntegration.BTypeOwner
set_option autoImplicit false
namespace PricingIntegration.ABActualOwners
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open Ramsey61.CPhysicalNormalization PricingIntegration.FixedPhysicalNeighborhood
open PricingIntegration.ABDRootPalette PricingIntegration.BActualFrame
open PricingIntegration.ABTypeOwner PricingIntegration.BTypeOwner

/-- Two coordinate changes compose to exactly one global palette change. -/
theorem relabel_comp (c : Host) (σ τ : FourColor ≃ FourColor) :
    relabel (relabel c (Equiv.refl _) σ) (Equiv.refl _) τ =
      relabel c (Equiv.refl _) (τ.trans σ) := rfl

theorem actual_A_native_owner (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r=48) (hh : 48≤H c r) :
    ∃σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧ W d r=W c r ∧
      (∀q : Color,colorDegree d (palette q) r=shape 0 q) ∧
      ∃b : ABlocks d r,(b.types 0=false ∨ b.types 1=true) ∧ (b.types 1=false ∨ b.types 2=true) ∧
      ∃m : PhysicalNeighborhoodMap d r (palette 3) (R4333.k16Template (b.types 2)),
        m.colors=foreignEquiv 3 ∧ 15≤colorDegree d (palette 3) (m.vertex 15) ∧
        ((attachingSupport d r (palette 3) (m.vertex 15) (palette 0)).card=4 ∨
         (attachingSupport d r (palette 3) (m.vertex 15) (palette 0)).card=5) := by
  obtain ⟨σ,good,hd,hH⟩ := actual_ABD_root_ordered 0 c hc r hw
  obtain ⟨code,good',hH',hW',hd',b,h0,h1,m,hpal,hmark⟩ :=
    ordered_A_native_owner _ good r hd (by rw [hH];exact hh)
  let τ := globalPalette code
  refine ⟨τ.trans σ,good',?_,?_,hd',b,h0,h1,m,hpal,hmark,?_⟩
  · exact relabel_H c _ _ _
  · exact relabel_W c _ _ _
  · exact PricingIntegration.BSupportedBlocks.low_support_four_or_five _ good' r (m.vertex 15) (m.mem_neighborhood 15) hmark

theorem actual_B_native_owner (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r=47) (hh : 47≤H c r) :
    ∃σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r=H c r ∧ W d r=W c r ∧
      (∀q : Color,colorDegree d (palette q) r=shape 1 q) ∧
      ∃b : Cells d r,(b.xt=false ∨ b.qt=true) ∧
      ∃m : PhysicalNeighborhoodMap d r (palette 3) (R4333.k16Template b.qt),
        m.colors=foreignEquiv 3 ∧ 15≤colorDegree d (palette 3) (m.vertex 15) ∧
        ((attachingSupport d r (palette 3) (m.vertex 15) (palette 0)).card=4 ∨
         (attachingSupport d r (palette 3) (m.vertex 15) (palette 0)).card=5) := by
  obtain ⟨σ,good,hd,hH⟩ := actual_ABD_root_ordered 1 c hc r hw
  obtain ⟨τ,good',hH',hW',hd',b,horder,m,hpal,hmark⟩ :=
    ordered_B_native_owner _ good r hd (by rw [hH];exact hh)
  refine ⟨τ.trans σ,good',?_,?_,hd',b,horder,m,hpal,hmark,?_⟩
  · exact relabel_H c _ _ _
  · exact relabel_W c _ _ _
  · exact PricingIntegration.BSupportedBlocks.low_support_four_or_five _ good' r (m.vertex 15) (m.mem_neighborhood 15) hmark

#print axioms actual_A_native_owner
#print axioms actual_B_native_owner
end PricingIntegration.ABActualOwners
