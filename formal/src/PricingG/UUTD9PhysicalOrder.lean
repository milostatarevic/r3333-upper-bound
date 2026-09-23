import PricingG.UUTD9Restricted

namespace PricingG.UUTD9PhysicalOrder
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

def formula : UUTD9Restricted.Leaf → Sat.Fmla
  | .inl i =>
      UUTD9StrongFormula.strongBase ++
      physicalUnits
        (UUTD9StrongFormula.quotientLargeSupportClauses i)
        (UUTD9StrongFormula.quotientSmallSupportClauses i)
        (UUTD9StrongFormula.quotientFreeLargeClauses i)
        (UUTD9StrongFormula.quotientFreeSmallClauses i)
        (UUTD9StrongFormula.quotientLargeSmallClauses i)
  | .inr (.inl i) =>
      UUTD9Root1Formula.strongBase ++
      physicalUnits
        (UUTD9Root1Formula.quotientLargeSupportClauses i)
        (UUTD9Root1Formula.quotientSmallSupportClauses i)
        (UUTD9Root1Formula.quotientFreeLargeClauses i)
        (UUTD9Root1Formula.quotientFreeSmallClauses i)
        (UUTD9Root1Formula.quotientLargeSmallClauses i)
  | .inr (.inr (.inl i)) =>
      UUTD9Root4Formula.strongBase ++
      physicalUnits
        (UUTD9Root4Formula.quotientLargeSupportClauses i)
        (UUTD9Root4Formula.quotientSmallSupportClauses i)
        (UUTD9Root4Formula.quotientFreeLargeClauses i)
        (UUTD9Root4Formula.quotientFreeSmallClauses i)
        (UUTD9Root4Formula.quotientLargeSmallClauses i)
  | .inr (.inr (.inr i)) =>
      UUTD9Root12Formula.strongBase ++
      physicalUnits
        (UUTD9Root12Formula.quotientLargeSupportClauses i)
        (UUTD9Root12Formula.quotientSmallSupportClauses i)
        (UUTD9Root12Formula.quotientFreeLargeClauses i)
        (UUTD9Root12Formula.quotientFreeSmallClauses i)
        (UUTD9Root12Formula.quotientLargeSmallClauses i)

/-- Every original408-leaf model supplies a model in physical support-block
order: small/block0 first, large/block1 second. Full archival byte binding is
still an independent data check; this theorem supplies its mathematical permutation step. -/
theorem original_model_physical_order (leaf : UUTD9Restricted.Leaf)
    (v : Sat.Valuation) (h : v.satisfies_fmla (UUTD9Restricted.formula leaf)) :
    v.satisfies_fmla (formula leaf) := by
  rcases leaf with i | i | i | i
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, UUTD9Restricted.formula,
      UUTD9StrongFormula.quotientLeafFmla,
      UUTD9StrongFormula.quotientRepresentativeUnitClauses,
      UUTD9StrongFormula.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, UUTD9Restricted.formula,
      UUTD9Root1Formula.quotientLeafFmla,
      UUTD9Root1Formula.quotientRepresentativeUnitClauses,
      UUTD9Root1Formula.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, UUTD9Restricted.formula,
      UUTD9Root4Formula.quotientLeafFmla,
      UUTD9Root4Formula.quotientRepresentativeUnitClauses,
      UUTD9Root4Formula.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto
  · constructor
    intro cl hc
    apply h.prop cl
    simp only [formula, physicalUnits, UUTD9Restricted.formula,
      UUTD9Root12Formula.quotientLeafFmla,
      UUTD9Root12Formula.quotientRepresentativeUnitClauses,
      UUTD9Root12Formula.quotientRepresentativeClauses,
      List.map_append, List.mem_append] at hc ⊢
    tauto

#print axioms original_model_physical_order
end PricingG.UUTD9PhysicalOrder
