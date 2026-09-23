import PricingG.DHostAdapter
import PricingG.DSelectedRowSplit

namespace PricingG.DHostAdapter
open Ramsey61 Ramsey61.CEncodingCore
open R4333.ProfileDHighOwnFiveRowSplit61 R4333.ProfileDHighOwnFiveSupportC5CNF
open R4333.ProfileDHighOwnFiveSupportC5Formula

/-- The selected Q16 index is retained through the four/five-support split.
The five-support side already has a constructed satisfying valuation of the
reused exact C5 formula. Its equivalence to a native campaign leaf is a
separate remaining data-binding obligation. -/
theorem selectedD_supplies_preserved_branch (c : Host) (hc : NoMonochromaticTriangle c)
    (r : Vertex) (hd : OrderedD c r) (hh : 46 ≤ H c r) :
    ∃ (i : Fin 16) (kind : R4333.ProfileDTripleJoinReduction.Kind),
      (∃ b : FourSupportFiveRowExtension kind, b.block = 2 ∧ b.position.val = i.val) ∨
      (∃ b : R4333.ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension kind,
        b.block = 2 ∧ b.position.val = i.val ∧
        ∃ br : CanonicalBranch kind b.block b.position,
          (finalValuation br).satisfies_fmla (fmla kind b.block b.position)) := by
  obtain ⟨i,hi⟩ := orderedD_has_high_last_block c hc r hd hh
  let w := orderedStar c hc r hd
  let ext := R4333.ProfileDRowExtension.extensionOfStar w
  have he : 14 ≤ R4333.colorDegree (R4333.ProfileDRowSupportBounds61.fullJoinedColoring ext)
      (R4333.ProfileDColumnOwnColorIncidence61.blockRootColor 2)
      (.inr (R4333.ProfileDTripleJoinReduction.blockVertex 2 i.val)) := by
    change 14 ≤ R4333.colorDegree
      (R4333.ProfileDRowSupportBounds61.fullJoinedColoring (R4333.ProfileDRowExtension.extensionOfStar w))
      (3 : Fin 4) (.inr (R4333.ProfileDTripleJoinReduction.blockVertex 2 i.val))
    rw [extension_endpoint_degree w i]
    exact hi
  refine ⟨i,R4333.ProfileDTripleJoinReduction.kindOfWitness w,?_⟩
  rcases DSelectedRowSplit.exists_selected_high_row_split ext 2 i he with ⟨_,b,hb,hp⟩ | ⟨_,b,hb,hp⟩
  · exact Or.inl ⟨b,hb,hp⟩
  · obtain ⟨br,hbr⟩ := fiveSupport_yields_satisfying_branch b
    exact Or.inr ⟨b,hb,hp,br,hbr⟩

#print axioms selectedD_supplies_preserved_branch
end PricingG.DHostAdapter
