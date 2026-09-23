import PricingG.DPhysicalExchange

set_option autoImplicit false
namespace PricingG.DPhysicalBlocks
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open PricingIntegration.ABDRootPalette PricingABD.TTExchange

/-- Complete physical entrance to the six native D owners. All maps and
supports refer to the same61vertices; the only recoloring is one explicitly
composed global palette permutation, preserving the supplied root and H. -/
theorem actual_D_native_physical (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r = 46) (hh : 46 ≤ H c r) :
    ∃ σ : FourColor ≃ FourColor,
      let d := relabel c (Equiv.refl _) σ
      NoMonochromaticTriangle d ∧ H d r = H c r ∧
      (∀ q : Color,colorDegree d (palette q) r = shape 2 q) ∧
      ∃ k : Nat,(k = 4 ∨ k = 5) ∧ ∃ b : Blocks d r k,
        b.mType = false ∨ b.xType = true := by
  obtain ⟨σ,hc',hH,hd,k,hk,⟨b⟩⟩ := actual_D_physical_blocks c hc r hw hh
  let d := relabel c (Equiv.refl _) σ
  rcases physical_native_owner b with hn | hs
  · exact ⟨σ,hc',hH,hd,k,hk,b,hn⟩
  · refine ⟨colorSwap.trans σ,?_,?_,?_,k,hk,b.exchange,Or.inl hs.1⟩
    · exact swappedHost_good d hc'
    · exact (swappedHost_H d r).trans hH
    · intro q
      change colorDegree (relabel d (Equiv.refl _) colorSwap) (palette q) r = _
      rw [relabel_degree]
      fin_cases q
      · exact hd 0
      · exact hd 2
      · exact hd 1
      · exact hd 3

#print axioms actual_D_native_physical
end PricingG.DPhysicalBlocks
