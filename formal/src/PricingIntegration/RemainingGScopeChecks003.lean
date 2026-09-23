import PricingIntegration.RemainingGScopeData

namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0048 : ∀ j : Fin 72,forcesOrRejects scope0048 0 5 2 j (hints0048 j) := by decide

theorem certificate0048 : forcedCheck scope0048 0 5 2=true := forced_from_hints scope0048 0 5 2 hints0048 hint0048

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0049 : ∀ j : Fin 72,rejects scope0049 j (hints0049 j) := by decide

theorem certificate0049 : emptyCheck scope0049=true := empty_from_hints scope0049 hints0049 hint0049

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0050 : ∀ j : Fin 72,forcesOrRejects scope0032 1 6 3 j (hints0050 j) := by decide

theorem certificate0050 : forcedCheck scope0032 1 6 3=true := forced_from_hints scope0032 1 6 3 hints0050 hint0050

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0051 : ∀ j : Fin 72,forcesOrRejects scope0034 1 6 2 j (hints0051 j) := by decide

theorem certificate0051 : forcedCheck scope0034 1 6 2=true := forced_from_hints scope0034 1 6 2 hints0051 hint0051

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0052 : ∀ j : Fin 72,rejects scope0050 j (hints0052 j) := by decide

theorem certificate0052 : emptyCheck scope0050=true := empty_from_hints scope0050 hints0052 hint0052

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0053 : ∀ j : Fin 72,forcesOrRejects scope0051 0 5 3 j (hints0053 j) := by decide

theorem certificate0053 : forcedCheck scope0051 0 5 3=true := forced_from_hints scope0051 0 5 3 hints0053 hint0053

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0054 : ∀ j : Fin 72,forcesOrRejects scope0052 0 5 2 j (hints0054 j) := by decide

theorem certificate0054 : forcedCheck scope0052 0 5 2=true := forced_from_hints scope0052 0 5 2 hints0054 hint0054

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0055 : ∀ j : Fin 72,rejects scope0053 j (hints0055 j) := by decide

theorem certificate0055 : emptyCheck scope0053=true := empty_from_hints scope0053 hints0055 hint0055

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0056 : ∀ j : Fin 72,rejects scope0054 j (hints0056 j) := by decide

theorem certificate0056 : emptyCheck scope0054=true := empty_from_hints scope0054 hints0056 hint0056

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0057 : ∀ j : Fin 72,rejects scope0055 j (hints0057 j) := by decide

theorem certificate0057 : emptyCheck scope0055=true := empty_from_hints scope0055 hints0057 hint0057

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0058 : ∀ j : Fin 72,rejects scope0056 j (hints0058 j) := by decide

theorem certificate0058 : emptyCheck scope0056=true := empty_from_hints scope0056 hints0058 hint0058

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0059 : ∀ j : Fin 72,forcesOrRejects scope0057 0 5 2 j (hints0059 j) := by decide

theorem certificate0059 : forcedCheck scope0057 0 5 2=true := forced_from_hints scope0057 0 5 2 hints0059 hint0059

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0060 : ∀ j : Fin 72,forcesOrRejects scope0058 0 5 3 j (hints0060 j) := by decide

theorem certificate0060 : forcedCheck scope0058 0 5 3=true := forced_from_hints scope0058 0 5 3 hints0060 hint0060

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0061 : ∀ j : Fin 72,rejects scope0059 j (hints0061 j) := by decide

theorem certificate0061 : emptyCheck scope0059=true := empty_from_hints scope0059 hints0061 hint0061

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0062 : ∀ j : Fin 72,rejects scope0060 j (hints0062 j) := by decide

theorem certificate0062 : emptyCheck scope0060=true := empty_from_hints scope0060 hints0062 hint0062

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0063 : ∀ j : Fin 72,rejects scope0061 j (hints0063 j) := by decide

theorem certificate0063 : emptyCheck scope0061=true := empty_from_hints scope0061 hints0063 hint0063

end PricingIntegration.RemainingGWitnesses