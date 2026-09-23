import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint128 : ∀ j : Fin 72,forcesOrRejects scope128 0 9 3 j (hints128 j) := by decide

theorem certificate128 : forcedCheck scope128 0 9 3=true := forced_from_hints scope128 0 9 3 hints128 hint128

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint129 : ∀ j : Fin 72,forcesOrRejects scope129 0 9 2 j (hints129 j) := by decide

theorem certificate129 : forcedCheck scope129 0 9 2=true := forced_from_hints scope129 0 9 2 hints129 hint129

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint130 : ∀ j : Fin 72,forcesOrRejects scope130 0 9 2 j (hints130 j) := by decide

theorem certificate130 : forcedCheck scope130 0 9 2=true := forced_from_hints scope130 0 9 2 hints130 hint130

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint131 : ∀ j : Fin 72,forcesOrRejects scope131 0 9 3 j (hints131 j) := by decide

theorem certificate131 : forcedCheck scope131 0 9 3=true := forced_from_hints scope131 0 9 3 hints131 hint131

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint132 : ∀ j : Fin 72,rejects scope132 j (hints132 j) := by decide

theorem certificate132 : emptyCheck scope132=true := empty_from_hints scope132 hints132 hint132

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint133 : ∀ j : Fin 72,forcesOrRejects scope133 0 7 2 j (hints133 j) := by decide

theorem certificate133 : forcedCheck scope133 0 7 2=true := forced_from_hints scope133 0 7 2 hints133 hint133

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint134 : ∀ j : Fin 72,forcesOrRejects scope134 0 6 3 j (hints134 j) := by decide

theorem certificate134 : forcedCheck scope134 0 6 3=true := forced_from_hints scope134 0 6 3 hints134 hint134

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint135 : ∀ j : Fin 72,forcesOrRejects scope135 0 7 3 j (hints135 j) := by decide

theorem certificate135 : forcedCheck scope135 0 7 3=true := forced_from_hints scope135 0 7 3 hints135 hint135

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint136 : ∀ j : Fin 72,forcesOrRejects scope136 0 6 2 j (hints136 j) := by decide

theorem certificate136 : forcedCheck scope136 0 6 2=true := forced_from_hints scope136 0 6 2 hints136 hint136

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint137 : ∀ j : Fin 72,forcesOrRejects scope137 0 8 2 j (hints137 j) := by decide

theorem certificate137 : forcedCheck scope137 0 8 2=true := forced_from_hints scope137 0 8 2 hints137 hint137

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint138 : ∀ j : Fin 72,forcesOrRejects scope138 6 3 3 j (hints138 j) := by decide

theorem certificate138 : forcedCheck scope138 6 3 3=true := forced_from_hints scope138 6 3 3 hints138 hint138

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint139 : ∀ j : Fin 72,forcesOrRejects scope139 0 9 2 j (hints139 j) := by decide

theorem certificate139 : forcedCheck scope139 0 9 2=true := forced_from_hints scope139 0 9 2 hints139 hint139

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint140 : ∀ j : Fin 72,forcesOrRejects scope140 6 4 3 j (hints140 j) := by decide

theorem certificate140 : forcedCheck scope140 6 4 3=true := forced_from_hints scope140 6 4 3 hints140 hint140

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint141 : ∀ j : Fin 72,rejects scope141 j (hints141 j) := by decide

theorem certificate141 : emptyCheck scope141=true := empty_from_hints scope141 hints141 hint141

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint142 : ∀ j : Fin 72,rejects scope142 j (hints142 j) := by decide

theorem certificate142 : emptyCheck scope142=true := empty_from_hints scope142 hints142 hint142

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint143 : ∀ j : Fin 72,rejects scope143 j (hints143 j) := by decide

theorem certificate143 : emptyCheck scope143=true := empty_from_hints scope143 hints143 hint143

end PricingC.GIsomorphic