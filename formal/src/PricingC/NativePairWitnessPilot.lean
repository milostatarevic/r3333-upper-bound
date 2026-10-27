import PricingC.NativePairActionData
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- Exact pair witnesses for the500-factor and200-factor entries used by
the complete finite table check. -/
theorem pilot_pair379 : (List.range (choiceCount (table ⟨379,by decide⟩))).all
 (fun j=>decide (PairWitness ⟨379,by decide⟩ j))=true:=by decide +kernel
theorem pilot_pair736 : (List.range (choiceCount (table ⟨736,by decide⟩))).all
 (fun j=>decide (PairWitness ⟨736,by decide⟩ j))=true:=by decide +kernel
#print axioms pilot_pair379
#print axioms pilot_pair736
end PricingC.NativePairActions
