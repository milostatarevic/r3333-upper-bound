import PricingC.NativePairActionData
import PricingC.NativePairWitnessPilot
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem pair_531 : (List.range (choiceCount (table ⟨531,by decide⟩))).all (fun j=>decide (PairWitness ⟨531,by decide⟩ j))=true := by decide +kernel
theorem pair_532 : (List.range (choiceCount (table ⟨532,by decide⟩))).all (fun j=>decide (PairWitness ⟨532,by decide⟩ j))=true := by decide +kernel
theorem pair_533 : (List.range (choiceCount (table ⟨533,by decide⟩))).all (fun j=>decide (PairWitness ⟨533,by decide⟩ j))=true := by decide +kernel
theorem pair_534 : (List.range (choiceCount (table ⟨534,by decide⟩))).all (fun j=>decide (PairWitness ⟨534,by decide⟩ j))=true := by decide +kernel
theorem pair_535 : (List.range (choiceCount (table ⟨535,by decide⟩))).all (fun j=>decide (PairWitness ⟨535,by decide⟩ j))=true := by decide +kernel
end PricingC.NativePairActions
