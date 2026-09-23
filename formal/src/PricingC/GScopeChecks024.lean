import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint384 : ∀ j : Fin 72,forcesOrRejects scope383 0 7 3 j (hints384 j) := by decide

theorem certificate384 : forcedCheck scope383 0 7 3=true := forced_from_hints scope383 0 7 3 hints384 hint384

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint385 : ∀ j : Fin 72,rejects scope384 j (hints385 j) := by decide

theorem certificate385 : emptyCheck scope384=true := empty_from_hints scope384 hints385 hint385

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint386 : ∀ j : Fin 72,rejects scope385 j (hints386 j) := by decide

theorem certificate386 : emptyCheck scope385=true := empty_from_hints scope385 hints386 hint386

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint387 : ∀ j : Fin 72,rejects scope386 j (hints387 j) := by decide

theorem certificate387 : emptyCheck scope386=true := empty_from_hints scope386 hints387 hint387

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint388 : ∀ j : Fin 72,rejects scope387 j (hints388 j) := by decide

theorem certificate388 : emptyCheck scope387=true := empty_from_hints scope387 hints388 hint388

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint389 : ∀ j : Fin 72,rejects scope388 j (hints389 j) := by decide

theorem certificate389 : emptyCheck scope388=true := empty_from_hints scope388 hints389 hint389

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint390 : ∀ j : Fin 72,rejects scope389 j (hints390 j) := by decide

theorem certificate390 : emptyCheck scope389=true := empty_from_hints scope389 hints390 hint390

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint391 : ∀ j : Fin 72,rejects scope390 j (hints391 j) := by decide

theorem certificate391 : emptyCheck scope390=true := empty_from_hints scope390 hints391 hint391

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint392 : ∀ j : Fin 72,rejects scope391 j (hints392 j) := by decide

theorem certificate392 : emptyCheck scope391=true := empty_from_hints scope391 hints392 hint392

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint393 : ∀ j : Fin 72,rejects scope392 j (hints393 j) := by decide

theorem certificate393 : emptyCheck scope392=true := empty_from_hints scope392 hints393 hint393

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint394 : ∀ j : Fin 72,rejects scope393 j (hints394 j) := by decide

theorem certificate394 : emptyCheck scope393=true := empty_from_hints scope393 hints394 hint394

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint395 : ∀ j : Fin 72,rejects scope394 j (hints395 j) := by decide

theorem certificate395 : emptyCheck scope394=true := empty_from_hints scope394 hints395 hint395

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint396 : ∀ j : Fin 72,rejects scope395 j (hints396 j) := by decide

theorem certificate396 : emptyCheck scope395=true := empty_from_hints scope395 hints396 hint396

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint397 : ∀ j : Fin 72,forcesOrRejects scope396 2 5 2 j (hints397 j) := by decide

theorem certificate397 : forcedCheck scope396 2 5 2=true := forced_from_hints scope396 2 5 2 hints397 hint397

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint398 : ∀ j : Fin 72,forcesOrRejects scope397 0 6 2 j (hints398 j) := by decide

theorem certificate398 : forcedCheck scope397 0 6 2=true := forced_from_hints scope397 0 6 2 hints398 hint398

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint399 : ∀ j : Fin 72,rejects scope398 j (hints399 j) := by decide

theorem certificate399 : emptyCheck scope398=true := empty_from_hints scope398 hints399 hint399

end PricingC.GIsomorphic