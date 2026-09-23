import PricingG.UUTP15Seed
import PricingG.UUTD9Restricted
import PricingG.UUTD10Entrance
import PricingG.UUTFourPosition
import PricingG.UUTFivePosition
import PricingG.DSixOwnerEntrance

namespace PricingG.UUTSelectedSatisfaction
open R4333
open ProfileDTripleJoinReduction ProfileDColumnOwnColorIncidence61
open ProfileDHighOwnFiveRowSplit61 ProfileDHighOwnFiveSupportC5CNF

abbrev Leaf := ProfileDUUUFourSupportP15SwapData61.SwapSeed ⊕
  (UUTD9Restricted.Leaf ⊕ ProfileDDegreeTenMatrixLeafDataUUU2P15.Leaf)

def formula : Leaf → Sat.Fmla
  | .inl i => R4333.UUTP15Leaves.matrixLeafFmla
      (ProfileDUUUFourSupportP15SwapData61.seedLeaf i)
  | .inr (.inl i) => UUTD9Restricted.formula i
  | .inr (.inr i) => R4333.UUTD10Complete.formula i

theorem leaf_card : Fintype.card Leaf = 679 := by
  simp [Leaf, UUTD9Restricted.Leaf,
    ProfileDUUUFourSupportP15SwapData61.SwapSeed,
    ProfileDDegreeTenMatrixLeafDataUUU2P15.Leaf]

def SomeLeafSatisfiable : Prop :=
  ∃ leaf : Leaf, ∃ valuation : Sat.Valuation, valuation.satisfies_fmla (formula leaf)

/-- The four-support arm of the actual selected Q16 split reaches precisely
one of the 189 retained P15 formulas after a whole-tail position transport. -/
theorem four_support_supplies_leaf (b : FourSupportFiveRowExtension .uut)
    (hb : b.block = 2) : SomeLeafSatisfiable := by
  rcases b with ⟨degree,block,position,first,fifth,tail⟩
  change block = 2 at hb
  subst block
  let positioned : ProfileDUUUFourSupportPositionSymmetry61.PositionedFourSupport
      .uut 2 position := ⟨degree,first,fifth,tail⟩
  obtain ⟨seed,v,hv⟩ := UUTP15Seed.branch_supplies_seed
    (R4333.UUTFourPosition.normalizeFourSupportBlockTwo position positioned)
  exact ⟨.inl seed,v,hv⟩

/-- The five-support arm first transports the selected endpoint to15 and
normalizes its retained C5, then the exact9/10 split reaches408 or82 leaves.
Every transformation carries the complete coloring and compatible rows. -/
theorem five_support_supplies_leaf
    (b : ProfileDHighOwnFiveRowSplit61.FiveSupportFiveRowExtension .uut)
    (hb : b.block = 2) : SomeLeafSatisfiable := by
  rcases b with ⟨degree,block,position,all,lower,upper⟩
  change block = 2 at hb
  subst block
  let positioned : ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport
      .uut 2 position := ⟨degree,all,lower,upper⟩
  let normalized := R4333.UUTFivePosition.normalizeSupportBlockTwo position positioned
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
        .uut 2 (Fin.last 15) :=
      ProfileDUUUFiveSupportPositionSymmetry.PositionedFiveSupport.ofSemantic branch.toFiveSupport
    obtain ⟨seed,v,hv⟩ := UUTD9Restricted.positioned_branch_supplies_leaf final hnine
    exact ⟨.inr (.inl seed),v,hv⟩
  · obtain ⟨seed,v,hv⟩ := UUTD10Entrance.canonical_branch_supplies_leaf branch hten
    exact ⟨.inr (.inr seed),v,hv⟩

/-- The UUT arm of the actual six-owner entrance has no remaining
mathematical cover premise: a complete selected branch produces one of679
exact formula valuations. Native data binding remains a separate check. -/
theorem selected_branch_supplies_leaf
    (b : DKindReduction.SelectedBranch .uut) : SomeLeafSatisfiable := by
  rcases b with b | b
  · exact four_support_supplies_leaf b.toSemantic rfl
  · exact five_support_supplies_leaf b.toSemantic rfl


#print axioms selected_branch_supplies_leaf
#print axioms four_support_supplies_leaf
#print axioms five_support_supplies_leaf
end PricingG.UUTSelectedSatisfaction
