import PricingG.P15SeedSatisfaction
import PricingG.D9RestrictedSatisfaction
import PricingG.D10SeedSatisfaction
import PricingG.DSixOwnerEntrance

namespace PricingG.UUUSelectedSatisfaction
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61 ProfileDHighOwnFiveSupportC5CNF

abbrev Leaf := ProfileDUUUFourSupportP15SwapData61.SwapSeed ⊕
  (D9RestrictedSatisfaction.Leaf ⊕ ProfileDDegreeTenMatrixLeafDataUUU2P15.Leaf)

def formula : Leaf → Sat.Fmla
  | .inl i => ProfileDUUUFourSupportP15MatrixOnlyLeaves61.matrixLeafFmla
      (ProfileDUUUFourSupportP15SwapData61.seedLeaf i)
  | .inr (.inl i) => D9RestrictedSatisfaction.formula i
  | .inr (.inr i) => ProfileDDegreeTenMatrixLeafDataUUU2P15.formula i

theorem leaf_card : Fintype.card Leaf = 679 := by
  simp [Leaf, D9RestrictedSatisfaction.Leaf,
    ProfileDUUUFourSupportP15SwapData61.SwapSeed,
    ProfileDDegreeTenMatrixLeafDataUUU2P15.Leaf]

def SomeLeafSatisfiable : Prop :=
  ∃ leaf : Leaf, ∃ valuation : Sat.Valuation, valuation.satisfies_fmla (formula leaf)

/-- The four-support arm of the actual selected Q16 split reaches precisely
one of the 189 retained P15 formulas after a whole-tail position transport. -/
theorem four_support_supplies_leaf (b : FourSupportFiveRowExtension .uuu)
    (hb : b.block = 2) : SomeLeafSatisfiable := by
  rcases b with ⟨degree,block,position,first,fifth,tail⟩
  change block = 2 at hb
  subst block
  let positioned : ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport
      .uuu 2 position := ⟨degree,first,fifth,tail⟩
  obtain ⟨seed,v,hv⟩ := P15SeedSatisfaction.branch_supplies_seed
    (ProfileDUUUFourSupportPositionSymmetry61.normalizeFourSupportBlockTwo position positioned)
  exact ⟨.inl seed,v,hv⟩

/-- The five-support arm first transports the selected endpoint to15 and
normalizes its retained C5, then the exact9/10 split reaches408 or82 leaves.
Every transformation carries the complete coloring and compatible rows. -/
theorem five_support_supplies_leaf
    (b : ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension .uuu)
    (hb : b.block = 2) : SomeLeafSatisfiable := by
  rcases b with ⟨degree,block,position,all,lower,upper⟩
  change block = 2 at hb
  subst block
  let positioned : ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport
      .uuu 2 position := ⟨degree,all,lower,upper⟩
  let normalized := ProfileDUUUFiveSupportPositionSymmetry.normalizeSupportBlockTwo position positioned
  obtain ⟨branch⟩ := exists_canonicalTransport normalized.toSemantic
  have hlo := branch.tailOwnDegreeLower
  have hhi := branch.tailOwnDegreeUpper
  have hcase : colorDegree branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor 2) (blockVertex 2 15) = 9 ∨
      colorDegree branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor 2) (blockVertex 2 15) = 10 := by
    change 9 ≤ colorDegree branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor 2) (blockVertex 2 15) at hlo
    change colorDegree branch.toDegreeFlooredFiveExtension.toFiveExtension.tail.coloring
      (blockRootColor 2) (blockVertex 2 15) ≤ 10 at hhi
    omega
  rcases hcase with hnine | hten
  · let final : ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport
        .uuu 2 (Fin.last 15) :=
      ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.ofSemantic branch.toFiveSupport
    obtain ⟨seed,v,hv⟩ := D9RestrictedSatisfaction.positioned_branch_supplies_leaf final hnine
    exact ⟨.inr (.inl seed),v,hv⟩
  · obtain ⟨seed,v,hv⟩ := D10SeedSatisfaction.branch_supplies_seed branch hten
    exact ⟨.inr (.inr seed),v,hv⟩

/-- The UUU arm of the actual six-owner entrance has no remaining
mathematical cover premise: a complete selected branch produces one of679
exact formula valuations. Native data binding remains a separate check. -/
theorem selected_branch_supplies_leaf
    (b : DKindReduction.SelectedBranch .uuu) : SomeLeafSatisfiable := by
  rcases b with b | b
  · exact four_support_supplies_leaf b.toSemantic rfl
  · exact five_support_supplies_leaf b.toSemantic rfl

/-- A genuine selected D root either supplies one of the exact679 UUU
formulas or retains a complete branch belonging to one of the other five
native owners. This does not identify UUT with UUU. -/
theorem actual_D_uuu_or_other (c : Ramsey61.Host)
    (hc : Ramsey61.NoMonochromaticTriangle c)
    (r : Ramsey61.CEncodingCore.Vertex) (hw : Ramsey61.W c r=46)
    (hh : 46≤Ramsey61.H c r) :
    SomeLeafSatisfiable ∨ ∃kind : DKindReduction.DKind,
      DKindReduction.NativeKind kind ∧ kind≠.uuu ∧
      Nonempty (DKindReduction.SelectedBranch kind) := by
  obtain ⟨kind,hkind,⟨b⟩⟩ := DKindReduction.actual_D_six_owner c hc r hw hh
  by_cases hu : kind=.uuu
  · subst kind
    exact Or.inl (selected_branch_supplies_leaf b)
  · exact Or.inr ⟨kind,hkind,hu,⟨b⟩⟩

#print axioms actual_D_uuu_or_other

#print axioms selected_branch_supplies_leaf

#print axioms four_support_supplies_leaf
#print axioms five_support_supplies_leaf
end PricingG.UUUSelectedSatisfaction
