import PricingG.D9RestrictedSatisfaction

namespace PricingG.D9PhysicalClauseOrder
open R4333
set_option maxHeartbeats 0

/-- Exchanging two initial unit blocks preserves the exact same valuation;
this is clause permutation, not a change of mathematical constraints. -/
theorem satisfies_exchange_blocks (v : Sat.Valuation) (base first second rest : Sat.Fmla)
    (h : v.satisfies_fmla (base ++ first ++ second ++ rest)) :
    v.satisfies_fmla (base ++ second ++ first ++ rest) := by
  constructor
  intro cl hc
  apply h.prop cl
  simp only [List.mem_append] at hc ⊢
  tauto

def physicalUnits (large small freeLarge freeSmall cross : Sat.Fmla) : Sat.Fmla :=
  (small ++ large ++ freeLarge ++ freeSmall ++ cross).map fun cl => cl.tail

def formula : D9RestrictedSatisfaction.Leaf → Sat.Fmla
  | .inl i =>
      ProfileDUUUDegreeNineQuotientFormula61.strongBase ++
      physicalUnits
        (ProfileDUUUDegreeNineQuotientFormula61.quotientLargeSupportClauses i)
        (ProfileDUUUDegreeNineQuotientFormula61.quotientSmallSupportClauses i)
        (ProfileDUUUDegreeNineQuotientFormula61.quotientFreeLargeClauses i)
        (ProfileDUUUDegreeNineQuotientFormula61.quotientFreeSmallClauses i)
        (ProfileDUUUDegreeNineQuotientFormula61.quotientLargeSmallClauses i)
  | .inr (.inl i) =>
      ContinuationDegreeNineTwistedRoot1QuotientFormula61.strongBase ++
      physicalUnits
        (ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientLargeSupportClauses i)
        (ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientSmallSupportClauses i)
        (ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientFreeLargeClauses i)
        (ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientFreeSmallClauses i)
        (ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientLargeSmallClauses i)
  | .inr (.inr (.inl i)) =>
      ContinuationDegreeNineTwistedRoot4QuotientFormula61.strongBase ++
      physicalUnits
        (ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientLargeSupportClauses i)
        (ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientSmallSupportClauses i)
        (ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientFreeLargeClauses i)
        (ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientFreeSmallClauses i)
        (ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientLargeSmallClauses i)
  | .inr (.inr (.inr i)) =>
      ContinuationDegreeNineTwistedRoot12QuotientFormula61.strongBase ++
      physicalUnits
        (ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientLargeSupportClauses i)
        (ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientSmallSupportClauses i)
        (ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientFreeLargeClauses i)
        (ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientFreeSmallClauses i)
        (ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientLargeSmallClauses i)

/-- Every original408-leaf model supplies a model in physical support-block
order: small/block0 first, large/block1 second. Full archival byte binding is
still an independent data check; this theorem supplies its mathematical permutation step. -/
theorem original_model_physical_order (leaf : D9RestrictedSatisfaction.Leaf)
    (v : Sat.Valuation) (h : v.satisfies_fmla (D9RestrictedSatisfaction.formula leaf)) :
    v.satisfies_fmla (formula leaf) := by
  rcases leaf with i | i | i | i
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, D9RestrictedSatisfaction.formula,
      ProfileDUUUDegreeNineQuotientFormula61.quotientLeafFmla,
      ProfileDUUUDegreeNineQuotientFormula61.quotientRepresentativeUnitClauses,
      ProfileDUUUDegreeNineQuotientFormula61.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, D9RestrictedSatisfaction.formula,
      ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientLeafFmla,
      ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientRepresentativeUnitClauses,
      ContinuationDegreeNineTwistedRoot1QuotientFormula61.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, D9RestrictedSatisfaction.formula,
      ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientLeafFmla,
      ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientRepresentativeUnitClauses,
      ContinuationDegreeNineTwistedRoot4QuotientFormula61.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, D9RestrictedSatisfaction.formula,
      ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientLeafFmla,
      ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientRepresentativeUnitClauses,
      ContinuationDegreeNineTwistedRoot12QuotientFormula61.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto

#print axioms original_model_physical_order
end PricingG.D9PhysicalClauseOrder
