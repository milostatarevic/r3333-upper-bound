import PricingC.NativePairActionData
import PricingC.NativePairWitnessPilot
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem pair_541 : (List.range (choiceCount (table ⟨541,by decide⟩))).all (fun j=>decide (PairWitness ⟨541,by decide⟩ j))=true := by decide +kernel
theorem pair_542 : (List.range (choiceCount (table ⟨542,by decide⟩))).all (fun j=>decide (PairWitness ⟨542,by decide⟩ j))=true := by decide +kernel
theorem pair_543 : (List.range (choiceCount (table ⟨543,by decide⟩))).all (fun j=>decide (PairWitness ⟨543,by decide⟩ j))=true := by decide +kernel
theorem pair_544 : (List.range (choiceCount (table ⟨544,by decide⟩))).all (fun j=>decide (PairWitness ⟨544,by decide⟩ j))=true := by decide +kernel
theorem pair_545 : (List.range (choiceCount (table ⟨545,by decide⟩))).all (fun j=>decide (PairWitness ⟨545,by decide⟩ j))=true := by decide +kernel
end PricingC.NativePairActions
