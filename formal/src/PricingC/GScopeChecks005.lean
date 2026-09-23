import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint080 : ∀ j : Fin 72,forcesOrRejects scope080 0 6 3 j (hints080 j) := by decide

theorem certificate080 : forcedCheck scope080 0 6 3=true := forced_from_hints scope080 0 6 3 hints080 hint080

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint081 : ∀ j : Fin 72,forcesOrRejects scope081 0 7 3 j (hints081 j) := by decide

theorem certificate081 : forcedCheck scope081 0 7 3=true := forced_from_hints scope081 0 7 3 hints081 hint081

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint082 : ∀ j : Fin 72,forcesOrRejects scope082 0 7 2 j (hints082 j) := by decide

theorem certificate082 : forcedCheck scope082 0 7 2=true := forced_from_hints scope082 0 7 2 hints082 hint082

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint083 : ∀ j : Fin 72,rejects scope083 j (hints083 j) := by decide

theorem certificate083 : emptyCheck scope083=true := empty_from_hints scope083 hints083 hint083

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint084 : ∀ j : Fin 72,rejects scope084 j (hints084 j) := by decide

theorem certificate084 : emptyCheck scope084=true := empty_from_hints scope084 hints084 hint084

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint085 : ∀ j : Fin 72,forcesOrRejects scope085 2 5 3 j (hints085 j) := by decide

theorem certificate085 : forcedCheck scope085 2 5 3=true := forced_from_hints scope085 2 5 3 hints085 hint085

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint086 : ∀ j : Fin 72,forcesOrRejects scope086 2 5 2 j (hints086 j) := by decide

theorem certificate086 : forcedCheck scope086 2 5 2=true := forced_from_hints scope086 2 5 2 hints086 hint086

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint087 : ∀ j : Fin 72,forcesOrRejects scope087 0 6 2 j (hints087 j) := by decide

theorem certificate087 : forcedCheck scope087 0 6 2=true := forced_from_hints scope087 0 6 2 hints087 hint087

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint088 : ∀ j : Fin 72,forcesOrRejects scope088 0 6 3 j (hints088 j) := by decide

theorem certificate088 : forcedCheck scope088 0 6 3=true := forced_from_hints scope088 0 6 3 hints088 hint088

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint089 : ∀ j : Fin 72,rejects scope089 j (hints089 j) := by decide

theorem certificate089 : emptyCheck scope089=true := empty_from_hints scope089 hints089 hint089

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint090 : ∀ j : Fin 72,rejects scope090 j (hints090 j) := by decide

theorem certificate090 : emptyCheck scope090=true := empty_from_hints scope090 hints090 hint090

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint091 : ∀ j : Fin 72,forcesOrRejects scope091 0 7 2 j (hints091 j) := by decide

theorem certificate091 : forcedCheck scope091 0 7 2=true := forced_from_hints scope091 0 7 2 hints091 hint091

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint092 : ∀ j : Fin 72,forcesOrRejects scope092 0 6 3 j (hints092 j) := by decide

theorem certificate092 : forcedCheck scope092 0 6 3=true := forced_from_hints scope092 0 6 3 hints092 hint092

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint093 : ∀ j : Fin 72,forcesOrRejects scope093 0 6 2 j (hints093 j) := by decide

theorem certificate093 : forcedCheck scope093 0 6 2=true := forced_from_hints scope093 0 6 2 hints093 hint093

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint094 : ∀ j : Fin 72,forcesOrRejects scope094 0 6 3 j (hints094 j) := by decide

theorem certificate094 : forcedCheck scope094 0 6 3=true := forced_from_hints scope094 0 6 3 hints094 hint094

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint095 : ∀ j : Fin 72,rejects scope095 j (hints095 j) := by decide

theorem certificate095 : emptyCheck scope095=true := empty_from_hints scope095 hints095 hint095

end PricingC.GIsomorphic