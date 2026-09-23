import PricingC.GScopeData

namespace PricingC.GIsomorphic
open PricingIntegration.LocalRelations PricingC.GRelations

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint000 : ∀ j : Fin 72,forcesOrRejects scope000 0 7 3 j (hints000 j) := by decide

theorem certificate000 : forcedCheck scope000 0 7 3=true := forced_from_hints scope000 0 7 3 hints000 hint000

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint001 : ∀ j : Fin 72,forcesOrRejects scope001 0 7 2 j (hints001 j) := by decide

theorem certificate001 : forcedCheck scope001 0 7 2=true := forced_from_hints scope001 0 7 2 hints001 hint001

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint002 : ∀ j : Fin 72,rejects scope002 j (hints002 j) := by decide

theorem certificate002 : emptyCheck scope002=true := empty_from_hints scope002 hints002 hint002

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint003 : ∀ j : Fin 72,forcesOrRejects scope003 0 6 2 j (hints003 j) := by decide

theorem certificate003 : forcedCheck scope003 0 6 2=true := forced_from_hints scope003 0 6 2 hints003 hint003

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint004 : ∀ j : Fin 72,forcesOrRejects scope004 0 6 3 j (hints004 j) := by decide

theorem certificate004 : forcedCheck scope004 0 6 3=true := forced_from_hints scope004 0 6 3 hints004 hint004

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint005 : ∀ j : Fin 72,forcesOrRejects scope005 0 7 2 j (hints005 j) := by decide

theorem certificate005 : forcedCheck scope005 0 7 2=true := forced_from_hints scope005 0 7 2 hints005 hint005

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint006 : ∀ j : Fin 72,forcesOrRejects scope006 0 7 3 j (hints006 j) := by decide

theorem certificate006 : forcedCheck scope006 0 7 3=true := forced_from_hints scope006 0 7 3 hints006 hint006

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint007 : ∀ j : Fin 72,forcesOrRejects scope007 0 6 3 j (hints007 j) := by decide

theorem certificate007 : forcedCheck scope007 0 6 3=true := forced_from_hints scope007 0 6 3 hints007 hint007

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint008 : ∀ j : Fin 72,forcesOrRejects scope008 0 6 2 j (hints008 j) := by decide

theorem certificate008 : forcedCheck scope008 0 6 2=true := forced_from_hints scope008 0 6 2 hints008 hint008

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint009 : ∀ j : Fin 72,rejects scope009 j (hints009 j) := by decide

theorem certificate009 : emptyCheck scope009=true := empty_from_hints scope009 hints009 hint009

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint010 : ∀ j : Fin 72,rejects scope010 j (hints010 j) := by decide

theorem certificate010 : emptyCheck scope010=true := empty_from_hints scope010 hints010 hint010

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint011 : ∀ j : Fin 72,rejects scope011 j (hints011 j) := by decide

theorem certificate011 : emptyCheck scope011=true := empty_from_hints scope011 hints011 hint011

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint012 : ∀ j : Fin 72,rejects scope012 j (hints012 j) := by decide

theorem certificate012 : emptyCheck scope012=true := empty_from_hints scope012 hints012 hint012

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint013 : ∀ j : Fin 72,forcesOrRejects scope013 2 9 3 j (hints013 j) := by decide

theorem certificate013 : forcedCheck scope013 2 9 3=true := forced_from_hints scope013 2 9 3 hints013 hint013

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint014 : ∀ j : Fin 72,forcesOrRejects scope014 7 4 2 j (hints014 j) := by decide

theorem certificate014 : forcedCheck scope014 7 4 2=true := forced_from_hints scope014 7 4 2 hints014 hint014

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem hint015 : ∀ j : Fin 72,forcesOrRejects scope015 0 6 2 j (hints015 j) := by decide

theorem certificate015 : forcedCheck scope015 0 6 2=true := forced_from_hints scope015 0 6 2 hints015 hint015

end PricingC.GIsomorphic