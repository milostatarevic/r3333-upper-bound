import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint400 : ∀ j : Fin 72,rejects scope399 j (hints400 j) := by decide

theorem certificate400 : emptyCheck scope399=true := empty_from_hints scope399 hints400 hint400

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint401 : ∀ j : Fin 72,forcesOrRejects scope400 3 9 2 j (hints401 j) := by decide

theorem certificate401 : forcedCheck scope400 3 9 2=true := forced_from_hints scope400 3 9 2 hints401 hint401

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint402 : ∀ j : Fin 72,forcesOrRejects scope401 3 9 3 j (hints402 j) := by decide

theorem certificate402 : forcedCheck scope401 3 9 3=true := forced_from_hints scope401 3 9 3 hints402 hint402

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint403 : ∀ j : Fin 72,forcesOrRejects scope402 4 8 2 j (hints403 j) := by decide

theorem certificate403 : forcedCheck scope402 4 8 2=true := forced_from_hints scope402 4 8 2 hints403 hint403

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint404 : ∀ j : Fin 72,forcesOrRejects scope403 2 5 2 j (hints404 j) := by decide

theorem certificate404 : forcedCheck scope403 2 5 2=true := forced_from_hints scope403 2 5 2 hints404 hint404

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint405 : ∀ j : Fin 72,forcesOrRejects scope001 2 5 3 j (hints405 j) := by decide

theorem certificate405 : forcedCheck scope001 2 5 3=true := forced_from_hints scope001 2 5 3 hints405 hint405

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint406 : ∀ j : Fin 72,forcesOrRejects scope003 1 5 3 j (hints406 j) := by decide

theorem certificate406 : forcedCheck scope003 1 5 3=true := forced_from_hints scope003 1 5 3 hints406 hint406

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint407 : ∀ j : Fin 72,forcesOrRejects scope404 1 5 2 j (hints407 j) := by decide

theorem certificate407 : forcedCheck scope404 1 5 2=true := forced_from_hints scope404 1 5 2 hints407 hint407

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint408 : ∀ j : Fin 72,forcesOrRejects scope006 2 5 2 j (hints408 j) := by decide

theorem certificate408 : forcedCheck scope006 2 5 2=true := forced_from_hints scope006 2 5 2 hints408 hint408

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint409 : ∀ j : Fin 72,forcesOrRejects scope007 1 5 2 j (hints409 j) := by decide

theorem certificate409 : forcedCheck scope007 1 5 2=true := forced_from_hints scope007 1 5 2 hints409 hint409

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint410 : ∀ j : Fin 72,forcesOrRejects scope169 1 5 3 j (hints410 j) := by decide

theorem certificate410 : forcedCheck scope169 1 5 3=true := forced_from_hints scope169 1 5 3 hints410 hint410

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint411 : ∀ j : Fin 72,forcesOrRejects scope405 0 7 3 j (hints411 j) := by decide

theorem certificate411 : forcedCheck scope405 0 7 3=true := forced_from_hints scope405 0 7 3 hints411 hint411

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint412 : ∀ j : Fin 72,forcesOrRejects scope402 0 7 2 j (hints412 j) := by decide

theorem certificate412 : forcedCheck scope402 0 7 2=true := forced_from_hints scope402 0 7 2 hints412 hint412

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint413 : ∀ j : Fin 72,forcesOrRejects scope406 0 6 3 j (hints413 j) := by decide

theorem certificate413 : forcedCheck scope406 0 6 3=true := forced_from_hints scope406 0 6 3 hints413 hint413

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint414 : ∀ j : Fin 72,forcesOrRejects scope407 0 6 2 j (hints414 j) := by decide

theorem certificate414 : forcedCheck scope407 0 6 2=true := forced_from_hints scope407 0 6 2 hints414 hint414

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint415 : ∀ j : Fin 72,rejects scope408 j (hints415 j) := by decide

theorem certificate415 : emptyCheck scope408=true := empty_from_hints scope408 hints415 hint415

end PricingC.GIsomorphic