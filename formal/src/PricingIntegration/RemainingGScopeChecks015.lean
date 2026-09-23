import PricingIntegration.RemainingGScopeData

namespace PricingIntegration.RemainingGWitnesses
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0240 : ∀ j : Fin 72,forcesOrRejects scope0237 3 8 3 j (hints0240 j) := by decide

theorem certificate0240 : forcedCheck scope0237 3 8 3=true := forced_from_hints scope0237 3 8 3 hints0240 hint0240

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0241 : ∀ j : Fin 72,forcesOrRejects scope0238 3 8 2 j (hints0241 j) := by decide

theorem certificate0241 : forcedCheck scope0238 3 8 2=true := forced_from_hints scope0238 3 8 2 hints0241 hint0241

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0242 : ∀ j : Fin 72,rejects scope0239 j (hints0242 j) := by decide

theorem certificate0242 : emptyCheck scope0239=true := empty_from_hints scope0239 hints0242 hint0242

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0243 : ∀ j : Fin 72,rejects scope0240 j (hints0243 j) := by decide

theorem certificate0243 : emptyCheck scope0240=true := empty_from_hints scope0240 hints0243 hint0243

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0244 : ∀ j : Fin 72,rejects scope0241 j (hints0244 j) := by decide

theorem certificate0244 : emptyCheck scope0241=true := empty_from_hints scope0241 hints0244 hint0244

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0245 : ∀ j : Fin 72,rejects scope0242 j (hints0245 j) := by decide

theorem certificate0245 : emptyCheck scope0242=true := empty_from_hints scope0242 hints0245 hint0245

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0246 : ∀ j : Fin 72,rejects scope0243 j (hints0246 j) := by decide

theorem certificate0246 : emptyCheck scope0243=true := empty_from_hints scope0243 hints0246 hint0246

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0247 : ∀ j : Fin 72,forcesOrRejects scope0244 0 5 3 j (hints0247 j) := by decide

theorem certificate0247 : forcedCheck scope0244 0 5 3=true := forced_from_hints scope0244 0 5 3 hints0247 hint0247

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0248 : ∀ j : Fin 72,forcesOrRejects scope0245 0 5 2 j (hints0248 j) := by decide

theorem certificate0248 : forcedCheck scope0245 0 5 2=true := forced_from_hints scope0245 0 5 2 hints0248 hint0248

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0249 : ∀ j : Fin 72,rejects scope0246 j (hints0249 j) := by decide

theorem certificate0249 : emptyCheck scope0246=true := empty_from_hints scope0246 hints0249 hint0249

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0250 : ∀ j : Fin 72,rejects scope0247 j (hints0250 j) := by decide

theorem certificate0250 : emptyCheck scope0247=true := empty_from_hints scope0247 hints0250 hint0250

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0251 : ∀ j : Fin 72,rejects scope0248 j (hints0251 j) := by decide

theorem certificate0251 : emptyCheck scope0248=true := empty_from_hints scope0248 hints0251 hint0251

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0252 : ∀ j : Fin 72,forcesOrRejects scope0249 0 5 3 j (hints0252 j) := by decide

theorem certificate0252 : forcedCheck scope0249 0 5 3=true := forced_from_hints scope0249 0 5 3 hints0252 hint0252

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0253 : ∀ j : Fin 72,forcesOrRejects scope0250 0 5 2 j (hints0253 j) := by decide

theorem certificate0253 : forcedCheck scope0250 0 5 2=true := forced_from_hints scope0250 0 5 2 hints0253 hint0253

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0254 : ∀ j : Fin 72,rejects scope0251 j (hints0254 j) := by decide

theorem certificate0254 : emptyCheck scope0251=true := empty_from_hints scope0251 hints0254 hint0254

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint0255 : ∀ j : Fin 72,rejects scope0252 j (hints0255 j) := by decide

theorem certificate0255 : emptyCheck scope0252=true := empty_from_hints scope0252 hints0255 hint0255

end PricingIntegration.RemainingGWitnesses