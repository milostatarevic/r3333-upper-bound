import PricingC.NativePairActionData
import PricingC.NativePairWitnessPilot
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem pair_536 : (List.range (choiceCount (table ⟨536,by decide⟩))).all (fun j=>decide (PairWitness ⟨536,by decide⟩ j))=true := by decide +kernel
theorem pair_537 : (List.range (choiceCount (table ⟨537,by decide⟩))).all (fun j=>decide (PairWitness ⟨537,by decide⟩ j))=true := by decide +kernel
theorem pair_538 : (List.range (choiceCount (table ⟨538,by decide⟩))).all (fun j=>decide (PairWitness ⟨538,by decide⟩ j))=true := by decide +kernel
theorem pair_539 : (List.range (choiceCount (table ⟨539,by decide⟩))).all (fun j=>decide (PairWitness ⟨539,by decide⟩ j))=true := by decide +kernel
theorem pair_540 : (List.range (choiceCount (table ⟨540,by decide⟩))).all (fun j=>decide (PairWitness ⟨540,by decide⟩ j))=true := by decide +kernel
end PricingC.NativePairActions
