import PricingG.DKindReduction

namespace PricingG.DKindReduction
open Ramsey61
open R4333
open ProfileDHighOwnFiveRowSplit61
open ProfileDUUUFourSupportPositionSymmetry61 ProfileDUUUFiveSupportPositionSymmetry
open DGenericSelectedNormalization

private theorem four_to_selected {kind : DKind} (b : FourSupportFiveRowExtension kind)
    (hb : b.block = 2) : Nonempty (SelectedBranch kind) := by
  rcases b with ⟨degree,block,position,first,fifth,tail⟩
  change block = 2 at hb
  subst block
  let p : PositionedFourSupport kind 2 position := ⟨degree,first,fifth,tail⟩
  exact ⟨.inl (normalizeFourSupport position p)⟩

private theorem five_to_selected {kind : DKind}
    (b : ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension kind)
    (hb : b.block = 2) : Nonempty (SelectedBranch kind) := by
  rcases b with ⟨degree,block,position,all,lower,upper⟩
  change block = 2 at hb
  subst block
  let p : PositionedFiveSupport kind 2 position := ⟨degree,all,lower,upper⟩
  exact ⟨.inr (normalizeFiveSupport position p)⟩

/-- The complete actual-D entrance to the six native owner kinds, with the
selected Q16 endpoint normalized to15 and every retained row/cross edge still
part of a full compatible semantic extension. No finite leaf cover is assumed. -/
theorem actual_D_six_owner (c : Host) (hc : Ramsey61.NoMonochromaticTriangle c)
    (r : Ramsey61.CEncodingCore.Vertex) (hw : W c r = 46) (hh : 46 ≤ H c r) :
    ∃ k : DKind, NativeKind k ∧ Nonempty (SelectedBranch k) := by
  obtain ⟨σ,hgood,hH,i,kind,hfour | hfive⟩ :=
    DHostAdapter.actualD_supplies_preserved_branch c hc r hw hh
  · obtain ⟨b,hb,_⟩ := hfour
    obtain ⟨selected⟩ := four_to_selected b hb
    exact selected_branch_native kind selected
  · obtain ⟨b,hb,_,_⟩ := hfive
    obtain ⟨selected⟩ := five_to_selected b hb
    exact selected_branch_native kind selected

#print axioms actual_D_six_owner
end PricingG.DKindReduction
