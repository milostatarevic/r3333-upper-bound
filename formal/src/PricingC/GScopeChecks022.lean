import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint352 : ∀ j : Fin 72,forcesOrRejects scope351 2 8 2 j (hints352 j) := by decide

theorem certificate352 : forcedCheck scope351 2 8 2=true := forced_from_hints scope351 2 8 2 hints352 hint352

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint353 : ∀ j : Fin 72,forcesOrRejects scope352 7 3 3 j (hints353 j) := by decide

theorem certificate353 : forcedCheck scope352 7 3 3=true := forced_from_hints scope352 7 3 3 hints353 hint353

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint354 : ∀ j : Fin 72,rejects scope353 j (hints354 j) := by decide

theorem certificate354 : emptyCheck scope353=true := empty_from_hints scope353 hints354 hint354

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint355 : ∀ j : Fin 72,rejects scope354 j (hints355 j) := by decide

theorem certificate355 : emptyCheck scope354=true := empty_from_hints scope354 hints355 hint355

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint356 : ∀ j : Fin 72,rejects scope355 j (hints356 j) := by decide

theorem certificate356 : emptyCheck scope355=true := empty_from_hints scope355 hints356 hint356

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint357 : ∀ j : Fin 72,rejects scope356 j (hints357 j) := by decide

theorem certificate357 : emptyCheck scope356=true := empty_from_hints scope356 hints357 hint357

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint358 : ∀ j : Fin 72,rejects scope357 j (hints358 j) := by decide

theorem certificate358 : emptyCheck scope357=true := empty_from_hints scope357 hints358 hint358

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint359 : ∀ j : Fin 72,rejects scope358 j (hints359 j) := by decide

theorem certificate359 : emptyCheck scope358=true := empty_from_hints scope358 hints359 hint359

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint360 : ∀ j : Fin 72,rejects scope359 j (hints360 j) := by decide

theorem certificate360 : emptyCheck scope359=true := empty_from_hints scope359 hints360 hint360

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint361 : ∀ j : Fin 72,rejects scope360 j (hints361 j) := by decide

theorem certificate361 : emptyCheck scope360=true := empty_from_hints scope360 hints361 hint361

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint362 : ∀ j : Fin 72,rejects scope361 j (hints362 j) := by decide

theorem certificate362 : emptyCheck scope361=true := empty_from_hints scope361 hints362 hint362

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint363 : ∀ j : Fin 72,rejects scope362 j (hints363 j) := by decide

theorem certificate363 : emptyCheck scope362=true := empty_from_hints scope362 hints363 hint363

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint364 : ∀ j : Fin 72,rejects scope363 j (hints364 j) := by decide

theorem certificate364 : emptyCheck scope363=true := empty_from_hints scope363 hints364 hint364

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint365 : ∀ j : Fin 72,rejects scope364 j (hints365 j) := by decide

theorem certificate365 : emptyCheck scope364=true := empty_from_hints scope364 hints365 hint365

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint366 : ∀ j : Fin 72,rejects scope365 j (hints366 j) := by decide

theorem certificate366 : emptyCheck scope365=true := empty_from_hints scope365 hints366 hint366

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint367 : ∀ j : Fin 72,forcesOrRejects scope366 3 9 3 j (hints367 j) := by decide

theorem certificate367 : forcedCheck scope366 3 9 3=true := forced_from_hints scope366 3 9 3 hints367 hint367

end PricingC.GIsomorphic