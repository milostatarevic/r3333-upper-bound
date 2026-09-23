import PricingC.Rooted45PhysicalComplete
import PricingIntegration.FixedPhysicalNeighborhood
import PricingIntegration.BActualFrame
namespace PricingC.DegreeFourPath
open Finset

def localColor (q:Bool):Fin 3:=if q then 2 else 1
def PathAdjacent (i j:Fin 4):Prop:=i.val+1=j.val ∨ j.val+1=i.val
instance (i j:Fin 4):Decidable (PathAdjacent i j):=inferInstanceAs (Decidable (_ ∨ _))
def pathOrderData : Fin 2 → Fin 15 → Fin 2 → Fin 4 → Fin 15 := ![![![![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![5,4,8,7]],![![0,1,9,5],![0,1,2,3]],![![0,1,2,3],![0,1,2,3]],![![3,9,6,7],![0,1,2,3]],![![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![0,8,2,3]],![![0,1,2,3],![0,1,2,3]],![![3,11,10,5],![0,1,2,3]],![![0,1,2,3],![0,12,13,7]],![![0,1,2,3],![3,12,4,14]],![![0,1,2,3],![5,13,2,14]],![![7,11,1,14],![0,1,2,3]],![![0,10,6,14],![0,1,2,3]],![![0,1,2,3],![0,1,2,3]]],![![![0,1,2,3],![0,1,2,3]],![![3,2,10,5],![0,1,2,3]],![![0,1,2,3],![5,4,11,7]],![![0,1,2,3],![0,1,2,3]],![![3,9,6,7],![0,1,2,3]],![![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![0,1,11,3]],![![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![5,13,1,14]],![![0,1,2,3],![0,12,13,7]],![![0,1,2,3],![3,12,4,14]],![![0,8,9,5],![0,1,2,3]],![![7,8,2,14],![0,1,2,3]],![![0,10,6,14],![0,1,2,3]],![![0,1,2,3],![0,1,2,3]]]]
def pathOrder (t:Bool) (r:Fin 15) (q:Bool):Fin 4→Fin 15:=pathOrderData (if t then 1 else 0) r (if q then 1 else 0)
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem template_degree_four_path : ∀t:Bool,∀r:Fin 15,∀q:Bool,
 R4333.colorDegree (R4333.k15Template t) (localColor q) r=4 →
 Function.Injective (pathOrder t r q) ∧
 univ.image (pathOrder t r q)=R4333.colorNeighborhood (R4333.k15Template t) (localColor q) r ∧
 (∀i j:Fin 4,i≠j → (R4333.k15Template t (pathOrder t r q i) (pathOrder t r q j)=0 ↔ PathAdjacent i j)):=by decide +kernel

theorem sixteen_degrees : ∀t:Bool,∀r:Fin 16,∀q:Bool,
 R4333.colorDegree (R4333.k16Template t) (localColor q) r=5:=by decide +kernel

#print axioms template_degree_four_path
end PricingC.DegreeFourPath
