import PricingIntegration.RemainingGScopeData

namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0064 : ∀ j : Fin 72,forcesOrRejects scope0062 0 5 3 j (hints0064 j) := by decide

theorem certificate0064 : forcedCheck scope0062 0 5 3=true := forced_from_hints scope0062 0 5 3 hints0064 hint0064

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0065 : ∀ j : Fin 72,forcesOrRejects scope0063 0 5 2 j (hints0065 j) := by decide

theorem certificate0065 : forcedCheck scope0063 0 5 2=true := forced_from_hints scope0063 0 5 2 hints0065 hint0065

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0066 : ∀ j : Fin 72,rejects scope0064 j (hints0066 j) := by decide

theorem certificate0066 : emptyCheck scope0064=true := empty_from_hints scope0064 hints0066 hint0066

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0067 : ∀ j : Fin 72,rejects scope0065 j (hints0067 j) := by decide

theorem certificate0067 : emptyCheck scope0065=true := empty_from_hints scope0065 hints0067 hint0067

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0068 : ∀ j : Fin 72,rejects scope0066 j (hints0068 j) := by decide

theorem certificate0068 : emptyCheck scope0066=true := empty_from_hints scope0066 hints0068 hint0068

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0069 : ∀ j : Fin 72,rejects scope0067 j (hints0069 j) := by decide

theorem certificate0069 : emptyCheck scope0067=true := empty_from_hints scope0067 hints0069 hint0069

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0070 : ∀ j : Fin 72,rejects scope0068 j (hints0070 j) := by decide

theorem certificate0070 : emptyCheck scope0068=true := empty_from_hints scope0068 hints0070 hint0070

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0071 : ∀ j : Fin 72,rejects scope0069 j (hints0071 j) := by decide

theorem certificate0071 : emptyCheck scope0069=true := empty_from_hints scope0069 hints0071 hint0071

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0072 : ∀ j : Fin 72,rejects scope0070 j (hints0072 j) := by decide

theorem certificate0072 : emptyCheck scope0070=true := empty_from_hints scope0070 hints0072 hint0072

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0073 : ∀ j : Fin 72,rejects scope0071 j (hints0073 j) := by decide

theorem certificate0073 : emptyCheck scope0071=true := empty_from_hints scope0071 hints0073 hint0073

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0074 : ∀ j : Fin 72,rejects scope0072 j (hints0074 j) := by decide

theorem certificate0074 : emptyCheck scope0072=true := empty_from_hints scope0072 hints0074 hint0074

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0075 : ∀ j : Fin 72,rejects scope0073 j (hints0075 j) := by decide

theorem certificate0075 : emptyCheck scope0073=true := empty_from_hints scope0073 hints0075 hint0075

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0076 : ∀ j : Fin 72,rejects scope0074 j (hints0076 j) := by decide

theorem certificate0076 : emptyCheck scope0074=true := empty_from_hints scope0074 hints0076 hint0076

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0077 : ∀ j : Fin 72,rejects scope0075 j (hints0077 j) := by decide

theorem certificate0077 : emptyCheck scope0075=true := empty_from_hints scope0075 hints0077 hint0077

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0078 : ∀ j : Fin 72,forcesOrRejects scope0076 1 6 2 j (hints0078 j) := by decide

theorem certificate0078 : forcedCheck scope0076 1 6 2=true := forced_from_hints scope0076 1 6 2 hints0078 hint0078

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0079 : ∀ j : Fin 72,forcesOrRejects scope0063 1 6 3 j (hints0079 j) := by decide

theorem certificate0079 : forcedCheck scope0063 1 6 3=true := forced_from_hints scope0063 1 6 3 hints0079 hint0079

end PricingIntegration.RemainingGWitnesses