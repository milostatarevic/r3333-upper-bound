import PricingG.DHostSelected
import PricingIntegration.ABDRootPalette

namespace PricingG.DHostAdapter
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open R4333.ProfileDHighOwnFiveRowSplit61 R4333.ProfileDHighOwnFiveSupportC5CNF
open R4333.ProfileDHighOwnFiveSupportC5Formula

/-- Actual selected-D entrance. One global color permutation orders the
supplied root, and the same root and highness count are preserved before the
semantic four/five-support split. No ordered profile is assumed. -/
theorem actualD_supplies_preserved_branch (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hw : W c r = 46) (hh : 46 ≤ H c r) :
    ∃ σ : FourColor ≃ FourColor,
      NoMonochromaticTriangle (relabel c (Equiv.refl _) σ) ∧
      H (relabel c (Equiv.refl _) σ) r = H c r ∧
      ∃ (i : Fin 16) (kind : R4333.ProfileDTripleJoinReduction.Kind),
        (∃ b : FourSupportFiveRowExtension kind, b.block = 2 ∧ b.position.val = i.val) ∨
        (∃ b : R4333.ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension kind,
          b.block = 2 ∧ b.position.val = i.val ∧
          ∃ br : CanonicalBranch kind b.block b.position,
            (finalValuation br).satisfies_fmla (fmla kind b.block b.position)) := by
  obtain ⟨σ,hgood,horder,hH⟩ :=
    PricingIntegration.ABDRootPalette.actual_ABD_root_ordered 2 c hc r hw
  refine ⟨σ,hgood,hH,?_⟩
  apply selectedD_supplies_preserved_branch _ hgood r
  · intro q
    exact horder q
  · simpa only [hH] using hh

#print axioms actualD_supplies_preserved_branch
end PricingG.DHostAdapter
