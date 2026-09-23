import PricingABD.Rooted455Entrance

namespace PricingC.Rooted555
open R4333 PricingABD.TemplateNormalization

def rootTwisted (r : Fin 2) : Bool := r.val=1
def rootVertex (_r : Fin 2) : Fin 16 := 15
def neighbor0 : Fin 2 → Fin 5 → Fin 16 := ![![0,3,5,7,14],![0,3,5,7,14]]
def iso0 : Fin 2 → Fin 10 → Fin 5 → Fin 16 := ![![![0,3,14,5,7],![0,7,5,14,3],![3,0,7,5,14],![3,14,5,7,0],![5,7,0,3,14],![5,14,3,0,7],![7,0,3,14,5],![7,5,14,3,0],![14,3,0,7,5],![14,5,7,0,3]],![![0,3,14,5,7],![0,7,5,14,3],![3,0,7,5,14],![3,14,5,7,0],![5,7,0,3,14],![5,14,3,0,7],![7,0,3,14,5],![7,5,14,3,0],![14,3,0,7,5],![14,5,7,0,3]]]
def canonical0 (i j : Fin 5) : ThreeColor := if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=4) ∨ (i.val=4 ∧ j.val=0) then 1 else 2
def neighbor1 : Fin 2 → Fin 5 → Fin 16 := ![![2,4,8,12,13],![1,4,11,12,13]]
def iso1 : Fin 2 → Fin 10 → Fin 5 → Fin 16 := ![![![2,8,4,12,13],![2,13,12,4,8],![4,8,2,13,12],![4,12,13,2,8],![8,2,13,12,4],![8,4,12,13,2],![12,4,8,2,13],![12,13,2,8,4],![13,2,8,4,12],![13,12,4,8,2]],![![1,11,4,12,13],![1,13,12,4,11],![4,11,1,13,12],![4,12,13,1,11],![11,1,13,12,4],![11,4,12,13,1],![12,4,11,1,13],![12,13,1,11,4],![13,1,11,4,12],![13,12,4,11,1]]]
def canonical1 (i j : Fin 5) : ThreeColor := if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=4) ∨ (i.val=4 ∧ j.val=0) then 0 else 2
def neighbor2 : Fin 2 → Fin 5 → Fin 16 := ![![1,6,9,10,11],![2,6,8,9,10]]
def iso2 : Fin 2 → Fin 10 → Fin 5 → Fin 16 := ![![![1,9,6,10,11],![1,11,10,6,9],![6,9,1,11,10],![6,10,11,1,9],![9,1,11,10,6],![9,6,10,11,1],![10,6,9,1,11],![10,11,1,9,6],![11,1,9,6,10],![11,10,6,9,1]],![![2,8,9,6,10],![2,10,6,9,8],![6,9,8,2,10],![6,10,2,8,9],![8,2,10,6,9],![8,9,6,10,2],![9,6,10,2,8],![9,8,2,10,6],![10,2,8,9,6],![10,6,9,8,2]]]
def canonical2 (i j : Fin 5) : ThreeColor := if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=4) ∨ (i.val=4 ∧ j.val=0) then 0 else 1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem neighbor0_complete : ∀ r : Fin 2, ∀ x : Fin 16,
 x≠rootVertex r → k16Template (rootTwisted r) (rootVertex r) x=0 → ∃i,neighbor0 r i=x := by decide
theorem neighbor0_injective : ∀ r,Function.Injective (neighbor0 r) := by decide
theorem iso0_complete : ∀ r : Fin 2, ∀ p : Fin 120,
 (∀ i j,i≠j → k16Template (rootTwisted r) (neighbor0 r (PricingABD.Rooted455Data.perm5 p i)) (neighbor0 r (PricingABD.Rooted455Data.perm5 p j))=canonical0 i j) →
 ∃a:Fin 10,∀i,neighbor0 r (PricingABD.Rooted455Data.perm5 p i)=iso0 r a i := by decide
theorem neighbor1_complete : ∀ r : Fin 2, ∀ x : Fin 16,
 x≠rootVertex r → k16Template (rootTwisted r) (rootVertex r) x=1 → ∃i,neighbor1 r i=x := by decide
theorem neighbor1_injective : ∀ r,Function.Injective (neighbor1 r) := by decide
theorem iso1_complete : ∀ r : Fin 2, ∀ p : Fin 120,
 (∀ i j,i≠j → k16Template (rootTwisted r) (neighbor1 r (PricingABD.Rooted455Data.perm5 p i)) (neighbor1 r (PricingABD.Rooted455Data.perm5 p j))=canonical1 i j) →
 ∃a:Fin 10,∀i,neighbor1 r (PricingABD.Rooted455Data.perm5 p i)=iso1 r a i := by decide
theorem neighbor2_complete : ∀ r : Fin 2, ∀ x : Fin 16,
 x≠rootVertex r → k16Template (rootTwisted r) (rootVertex r) x=2 → ∃i,neighbor2 r i=x := by decide
theorem neighbor2_injective : ∀ r,Function.Injective (neighbor2 r) := by decide
theorem iso2_complete : ∀ r : Fin 2, ∀ p : Fin 120,
 (∀ i j,i≠j → k16Template (rootTwisted r) (neighbor2 r (PricingABD.Rooted455Data.perm5 p i)) (neighbor2 r (PricingABD.Rooted455Data.perm5 p j))=canonical2 i j) →
 ∃a:Fin 10,∀i,neighbor2 r (PricingABD.Rooted455Data.perm5 p i)=iso2 r a i := by decide

#print axioms iso0_complete
end PricingC.Rooted555
