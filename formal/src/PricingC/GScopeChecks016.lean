import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint256 : ∀ j : Fin 72,rejects scope256 j (hints256 j) := by decide

theorem certificate256 : emptyCheck scope256=true := empty_from_hints scope256 hints256 hint256

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint257 : ∀ j : Fin 72,forcesOrRejects scope257 4 8 2 j (hints257 j) := by decide

theorem certificate257 : forcedCheck scope257 4 8 2=true := forced_from_hints scope257 4 8 2 hints257 hint257

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint258 : ∀ j : Fin 72,forcesOrRejects scope258 4 8 3 j (hints258 j) := by decide

theorem certificate258 : forcedCheck scope258 4 8 3=true := forced_from_hints scope258 4 8 3 hints258 hint258

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint259 : ∀ j : Fin 72,forcesOrRejects scope259 3 9 3 j (hints259 j) := by decide

theorem certificate259 : forcedCheck scope259 3 9 3=true := forced_from_hints scope259 3 9 3 hints259 hint259

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint260 : ∀ j : Fin 72,forcesOrRejects scope260 3 9 2 j (hints260 j) := by decide

theorem certificate260 : forcedCheck scope260 3 9 2=true := forced_from_hints scope260 3 9 2 hints260 hint260

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint261 : ∀ j : Fin 72,forcesOrRejects scope261 3 9 2 j (hints261 j) := by decide

theorem certificate261 : forcedCheck scope261 3 9 2=true := forced_from_hints scope261 3 9 2 hints261 hint261

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint262 : ∀ j : Fin 72,forcesOrRejects scope262 3 9 3 j (hints262 j) := by decide

theorem certificate262 : forcedCheck scope262 3 9 3=true := forced_from_hints scope262 3 9 3 hints262 hint262

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint263 : ∀ j : Fin 72,forcesOrRejects scope263 4 8 3 j (hints263 j) := by decide

theorem certificate263 : forcedCheck scope263 4 8 3=true := forced_from_hints scope263 4 8 3 hints263 hint263

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint264 : ∀ j : Fin 72,forcesOrRejects scope264 4 8 2 j (hints264 j) := by decide

theorem certificate264 : forcedCheck scope264 4 8 2=true := forced_from_hints scope264 4 8 2 hints264 hint264

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint265 : ∀ j : Fin 72,rejects scope265 j (hints265 j) := by decide

theorem certificate265 : emptyCheck scope265=true := empty_from_hints scope265 hints265 hint265

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint266 : ∀ j : Fin 72,rejects scope266 j (hints266 j) := by decide

theorem certificate266 : emptyCheck scope266=true := empty_from_hints scope266 hints266 hint266

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint267 : ∀ j : Fin 72,rejects scope267 j (hints267 j) := by decide

theorem certificate267 : emptyCheck scope267=true := empty_from_hints scope267 hints267 hint267

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint268 : ∀ j : Fin 72,rejects scope268 j (hints268 j) := by decide

theorem certificate268 : emptyCheck scope268=true := empty_from_hints scope268 hints268 hint268

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint269 : ∀ j : Fin 72,rejects scope269 j (hints269 j) := by decide

theorem certificate269 : emptyCheck scope269=true := empty_from_hints scope269 hints269 hint269

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint270 : ∀ j : Fin 72,rejects scope270 j (hints270 j) := by decide

theorem certificate270 : emptyCheck scope270=true := empty_from_hints scope270 hints270 hint270

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint271 : ∀ j : Fin 72,rejects scope271 j (hints271 j) := by decide

theorem certificate271 : emptyCheck scope271=true := empty_from_hints scope271 hints271 hint271

end PricingC.GIsomorphic