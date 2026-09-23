import PricingABD.Rooted455Catalogue

namespace PricingC.OwnFive15
open R4333 PricingABD.TemplateNormalization

def ownOrder (t : Bool) : Fin 15 → Fin 5 → Fin 15 := if t then ![![0,1,2,3,4],![0,11,9,14,13],![3,8,10,13,14],![0,1,2,3,4],![5,11,8,12,14],![0,1,2,3,4],![7,10,9,14,12],![0,1,2,3,4],![0,2,9,4,7],![1,3,8,6,5],![0,2,6,5,11],![1,3,4,7,10],![0,3,4,6,13],![1,2,12,7,5],![0,1,2,3,4]] else ![![0,1,2,3,4],![0,11,9,14,13],![3,8,10,13,14],![0,1,2,3,4],![5,8,11,12,14],![0,1,2,3,4],![7,10,9,14,12],![0,1,2,3,4],![0,2,9,4,7],![1,3,8,5,6],![0,2,5,6,11],![1,3,4,7,10],![0,3,4,6,13],![1,2,5,7,12],![0,1,2,3,4]]

def canonical (i j : Fin 5) : ThreeColor :=
 if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=4) ∨ (i.val=4 ∧ j.val=0) then 1 else 2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem ownOrder_properties : ∀ t : Bool,∀ r : Fin 15,colorDegree (k15Template t) 0 r=5 →
 Function.Injective (ownOrder t r) ∧
 (∀ x,x≠r → k15Template t r x=0 → ∃i,ownOrder t r i=x) ∧
 (∀ i j,i≠j → k15Template t (ownOrder t r i) (ownOrder t r j)=canonical i j) := by decide

end PricingC.OwnFive15
