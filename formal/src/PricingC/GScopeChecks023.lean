import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint368 : ∀ j : Fin 72,forcesOrRejects scope367 3 9 2 j (hints368 j) := by decide

theorem certificate368 : forcedCheck scope367 3 9 2=true := forced_from_hints scope367 3 9 2 hints368 hint368

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint369 : ∀ j : Fin 72,rejects scope368 j (hints369 j) := by decide

theorem certificate369 : emptyCheck scope368=true := empty_from_hints scope368 hints369 hint369

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint370 : ∀ j : Fin 72,rejects scope369 j (hints370 j) := by decide

theorem certificate370 : emptyCheck scope369=true := empty_from_hints scope369 hints370 hint370

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint371 : ∀ j : Fin 72,rejects scope370 j (hints371 j) := by decide

theorem certificate371 : emptyCheck scope370=true := empty_from_hints scope370 hints371 hint371

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint372 : ∀ j : Fin 72,rejects scope371 j (hints372 j) := by decide

theorem certificate372 : emptyCheck scope371=true := empty_from_hints scope371 hints372 hint372

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint373 : ∀ j : Fin 72,forcesOrRejects scope372 3 9 3 j (hints373 j) := by decide

theorem certificate373 : forcedCheck scope372 3 9 3=true := forced_from_hints scope372 3 9 3 hints373 hint373

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint374 : ∀ j : Fin 72,forcesOrRejects scope373 3 9 2 j (hints374 j) := by decide

theorem certificate374 : forcedCheck scope373 3 9 2=true := forced_from_hints scope373 3 9 2 hints374 hint374

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint375 : ∀ j : Fin 72,forcesOrRejects scope374 3 9 3 j (hints375 j) := by decide

theorem certificate375 : forcedCheck scope374 3 9 3=true := forced_from_hints scope374 3 9 3 hints375 hint375

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint376 : ∀ j : Fin 72,forcesOrRejects scope375 3 9 2 j (hints376 j) := by decide

theorem certificate376 : forcedCheck scope375 3 9 2=true := forced_from_hints scope375 3 9 2 hints376 hint376

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint377 : ∀ j : Fin 72,forcesOrRejects scope376 1 5 3 j (hints377 j) := by decide

theorem certificate377 : forcedCheck scope376 1 5 3=true := forced_from_hints scope376 1 5 3 hints377 hint377

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint378 : ∀ j : Fin 72,forcesOrRejects scope377 1 5 2 j (hints378 j) := by decide

theorem certificate378 : forcedCheck scope377 1 5 2=true := forced_from_hints scope377 1 5 2 hints378 hint378

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint379 : ∀ j : Fin 72,forcesOrRejects scope378 0 6 2 j (hints379 j) := by decide

theorem certificate379 : forcedCheck scope378 0 6 2=true := forced_from_hints scope378 0 6 2 hints379 hint379

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint380 : ∀ j : Fin 72,forcesOrRejects scope379 0 6 3 j (hints380 j) := by decide

theorem certificate380 : forcedCheck scope379 0 6 3=true := forced_from_hints scope379 0 6 3 hints380 hint380

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint381 : ∀ j : Fin 72,forcesOrRejects scope380 0 7 3 j (hints381 j) := by decide

theorem certificate381 : forcedCheck scope380 0 7 3=true := forced_from_hints scope380 0 7 3 hints381 hint381

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint382 : ∀ j : Fin 72,forcesOrRejects scope381 0 6 2 j (hints382 j) := by decide

theorem certificate382 : forcedCheck scope381 0 6 2=true := forced_from_hints scope381 0 6 2 hints382 hint382

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint383 : ∀ j : Fin 72,forcesOrRejects scope382 0 7 2 j (hints383 j) := by decide

theorem certificate383 : forcedCheck scope382 0 7 2=true := forced_from_hints scope382 0 7 2 hints383 hint383

end PricingC.GIsomorphic