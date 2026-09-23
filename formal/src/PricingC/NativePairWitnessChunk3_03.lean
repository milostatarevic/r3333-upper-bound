import PricingC.NativePairActionData
import PricingC.NativePairWitnessPilot
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem pair_733 : (List.range (choiceCount (table ⟨733,by decide⟩))).all (fun j=>decide (PairWitness ⟨733,by decide⟩ j))=true := by decide +kernel
theorem pair_734 : (List.range (choiceCount (table ⟨734,by decide⟩))).all (fun j=>decide (PairWitness ⟨734,by decide⟩ j))=true := by decide +kernel
theorem pair_735 : (List.range (choiceCount (table ⟨735,by decide⟩))).all (fun j=>decide (PairWitness ⟨735,by decide⟩ j))=true := by decide +kernel
theorem pair_736 : (List.range (choiceCount (table ⟨736,by decide⟩))).all (fun j=>decide (PairWitness ⟨736,by decide⟩ j))=true := pilot_pair736
end PricingC.NativePairActions
