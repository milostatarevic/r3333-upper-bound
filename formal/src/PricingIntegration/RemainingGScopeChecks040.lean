import PricingIntegration.RemainingGScopeData

namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0640 : ∀ j : Fin 72,forcesOrRejects scope0465 3 8 2 j (hints0640 j) := by decide

theorem certificate0640 : forcedCheck scope0465 3 8 2=true := forced_from_hints scope0465 3 8 2 hints0640 hint0640

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0641 : ∀ j : Fin 72,forcesOrRejects scope0594 3 8 3 j (hints0641 j) := by decide

theorem certificate0641 : forcedCheck scope0594 3 8 3=true := forced_from_hints scope0594 3 8 3 hints0641 hint0641

end PricingIntegration.RemainingGWitnesses