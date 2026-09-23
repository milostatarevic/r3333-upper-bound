import PricingABD.TemplateNormalization
import PricingABD.P15MatrixTransport
import Mathlib.Data.Fintype.Perm

namespace PricingABD.Rooted455Data
open R4333
open PricingABD.P15PairOrbit PricingABD.P15MatrixTransport

def rootTwisted (r : Fin 10) : Bool := r.val ≥ 5
def rootVertex : Fin 10 → Fin 15 := ![0,3,5,7,14,0,3,5,7,14]

def neighbor0 : Fin 10 → Fin 4 → Fin 15 := ![![1,8,10,12],![2,9,11,12],![4,9,10,13],![6,8,11,13],![1,2,4,6],![1,8,10,12],![2,9,11,12],![4,9,10,13],![6,8,11,13],![1,2,4,6]]

def neighbor1 : Fin 10 → Fin 5 → Fin 15 := ![![2,3,7,11,13],![0,1,4,8,14],![2,6,7,8,14],![0,4,5,10,12],![3,5,9,12,13],![2,3,7,11,13],![0,1,4,8,14],![1,6,7,11,14],![0,4,5,10,12],![3,5,9,12,13]]

def neighbor2 : Fin 10 → Fin 5 → Fin 15 := ![![4,5,6,9,14],![5,6,7,10,13],![0,1,3,11,12],![1,2,3,9,14],![0,7,8,10,11],![4,5,6,9,14],![5,6,7,10,13],![0,2,3,8,12],![1,2,3,9,14],![0,7,8,10,11]]

def iso0 : Fin 10 → Fin 2 → Fin 4 → Fin 15 := ![![![8,10,1,12],![12,1,10,8]],![![2,9,11,12],![12,11,9,2]],![![4,9,10,13],![13,10,9,4]],![![8,11,6,13],![13,6,11,8]],![![2,1,6,4],![4,6,1,2]],![![1,10,8,12],![12,8,10,1]],![![11,9,2,12],![12,2,9,11]],![![4,9,10,13],![13,10,9,4]],![![11,8,6,13],![13,6,8,11]],![![1,2,6,4],![4,6,2,1]]]

def iso1 : Fin 10 → Fin 10 → Fin 5 → Fin 15 := ![![![2,3,11,7,13],![2,13,7,11,3],![3,2,13,7,11],![3,11,7,13,2],![7,11,3,2,13],![7,13,2,3,11],![11,3,2,13,7],![11,7,13,2,3],![13,2,3,11,7],![13,7,11,3,2]],![![0,1,14,4,8],![0,8,4,14,1],![1,0,8,4,14],![1,14,4,8,0],![4,8,0,1,14],![4,14,1,0,8],![8,0,1,14,4],![8,4,14,1,0],![14,1,0,8,4],![14,4,8,0,1]],![![2,8,7,6,14],![2,14,6,7,8],![6,7,8,2,14],![6,14,2,8,7],![7,6,14,2,8],![7,8,2,14,6],![8,2,14,6,7],![8,7,6,14,2],![14,2,8,7,6],![14,6,7,8,2]],![![0,10,5,4,12],![0,12,4,5,10],![4,5,10,0,12],![4,12,0,10,5],![5,4,12,0,10],![5,10,0,12,4],![10,0,12,4,5],![10,5,4,12,0],![12,0,10,5,4],![12,4,5,10,0]],![![3,9,5,13,12],![3,12,13,5,9],![5,9,3,12,13],![5,13,12,3,9],![9,3,12,13,5],![9,5,13,12,3],![12,3,9,5,13],![12,13,5,9,3],![13,5,9,3,12],![13,12,3,9,5]],![![2,3,11,7,13],![2,13,7,11,3],![3,2,13,7,11],![3,11,7,13,2],![7,11,3,2,13],![7,13,2,3,11],![11,3,2,13,7],![11,7,13,2,3],![13,2,3,11,7],![13,7,11,3,2]],![![0,1,14,4,8],![0,8,4,14,1],![1,0,8,4,14],![1,14,4,8,0],![4,8,0,1,14],![4,14,1,0,8],![8,0,1,14,4],![8,4,14,1,0],![14,1,0,8,4],![14,4,8,0,1]],![![1,11,7,6,14],![1,14,6,7,11],![6,7,11,1,14],![6,14,1,11,7],![7,6,14,1,11],![7,11,1,14,6],![11,1,14,6,7],![11,7,6,14,1],![14,1,11,7,6],![14,6,7,11,1]],![![0,10,5,4,12],![0,12,4,5,10],![4,5,10,0,12],![4,12,0,10,5],![5,4,12,0,10],![5,10,0,12,4],![10,0,12,4,5],![10,5,4,12,0],![12,0,10,5,4],![12,4,5,10,0]],![![3,9,5,13,12],![3,12,13,5,9],![5,9,3,12,13],![5,13,12,3,9],![9,3,12,13,5],![9,5,13,12,3],![12,3,9,5,13],![12,13,5,9,3],![13,5,9,3,12],![13,12,3,9,5]]]

def iso2 : Fin 10 → Fin 10 → Fin 5 → Fin 15 := ![![![4,5,9,6,14],![4,14,6,9,5],![5,4,14,6,9],![5,9,6,14,4],![6,9,5,4,14],![6,14,4,5,9],![9,5,4,14,6],![9,6,14,4,5],![14,4,5,9,6],![14,6,9,5,4]],![![5,10,6,7,13],![5,13,7,6,10],![6,7,13,5,10],![6,10,5,13,7],![7,6,10,5,13],![7,13,5,10,6],![10,5,13,7,6],![10,6,7,13,5],![13,5,10,6,7],![13,7,6,10,5]],![![0,1,11,3,12],![0,12,3,11,1],![1,0,12,3,11],![1,11,3,12,0],![3,11,1,0,12],![3,12,0,1,11],![11,1,0,12,3],![11,3,12,0,1],![12,0,1,11,3],![12,3,11,1,0]],![![1,9,3,2,14],![1,14,2,3,9],![2,3,9,1,14],![2,14,1,9,3],![3,2,14,1,9],![3,9,1,14,2],![9,1,14,2,3],![9,3,2,14,1],![14,1,9,3,2],![14,2,3,9,1]],![![0,8,7,11,10],![0,10,11,7,8],![7,8,0,10,11],![7,11,10,0,8],![8,0,10,11,7],![8,7,11,10,0],![10,0,8,7,11],![10,11,7,8,0],![11,7,8,0,10],![11,10,0,8,7]],![![4,5,9,6,14],![4,14,6,9,5],![5,4,14,6,9],![5,9,6,14,4],![6,9,5,4,14],![6,14,4,5,9],![9,5,4,14,6],![9,6,14,4,5],![14,4,5,9,6],![14,6,9,5,4]],![![5,10,6,7,13],![5,13,7,6,10],![6,7,13,5,10],![6,10,5,13,7],![7,6,10,5,13],![7,13,5,10,6],![10,5,13,7,6],![10,6,7,13,5],![13,5,10,6,7],![13,7,6,10,5]],![![0,8,2,3,12],![0,12,3,2,8],![2,3,12,0,8],![2,8,0,12,3],![3,2,8,0,12],![3,12,0,8,2],![8,0,12,3,2],![8,2,3,12,0],![12,0,8,2,3],![12,3,2,8,0]],![![1,9,3,2,14],![1,14,2,3,9],![2,3,9,1,14],![2,14,1,9,3],![3,2,14,1,9],![3,9,1,14,2],![9,1,14,2,3],![9,3,2,14,1],![14,1,9,3,2],![14,2,3,9,1]],![![0,8,7,11,10],![0,10,11,7,8],![7,8,0,10,11],![7,11,10,0,8],![8,0,10,11,7],![8,7,11,10,0],![10,0,8,7,11],![10,11,7,8,0],![11,7,8,0,10],![11,10,0,8,7]]]

def perms4 := permsOfList ([0,1,2,3] : List (Fin 4))
def perms5 := permsOfList ([0,1,2,3,4] : List (Fin 5))

theorem perms4_length : perms4.length = 24 := by decide
theorem perms5_length : perms5.length = 120 := by decide

def perm4 (i : Fin 24) : Equiv.Perm (Fin 4) := perms4.get ⟨i.val,by rw [perms4_length];exact i.isLt⟩
def perm5 (i : Fin 120) : Equiv.Perm (Fin 5) := perms5.get ⟨i.val,by rw [perms5_length];exact i.isLt⟩

theorem perm4_complete (p : Equiv.Perm (Fin 4)) : ∃ i,perm4 i = p := by
  have hp : p ∈ perms4 := by
    apply mem_permsOfList_of_mem
    intro x _;fin_cases x <;> simp
  exact ⟨⟨perms4.idxOf p,by rw [←perms4_length];exact List.idxOf_lt_length_of_mem hp⟩,by apply List.getElem_idxOf⟩

theorem perm5_complete (p : Equiv.Perm (Fin 5)) : ∃ i,perm5 i = p := by
  have hp : p ∈ perms5 := by
    apply mem_permsOfList_of_mem
    intro x _;fin_cases x <;> simp
  exact ⟨⟨perms5.idxOf p,by rw [←perms5_length];exact List.idxOf_lt_length_of_mem hp⟩,by apply List.getElem_idxOf⟩

def canonical0 (i j : Fin 4) : ThreeColor := if i.val+1=j.val ∨ j.val+1=i.val then 1 else 2
def canonical1 (i j : Fin 5) : ThreeColor := if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=4) ∨ (i.val=4 ∧ j.val=0) then 0 else 2
def canonical2 (i j : Fin 5) : ThreeColor := if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=4) ∨ (i.val=4 ∧ j.val=0) then 0 else 1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem roots_complete : ∀ t : Bool, ∀ r : Fin 15,
  colorDegree (k15Template t) 0 r = 4 → ∃ i,rootTwisted i=t ∧ rootVertex i=r := by decide +kernel

theorem neighbor0_complete : ∀ r : Fin 10, ∀ x : Fin 15,
  x ≠ rootVertex r → k15Template (rootTwisted r) (rootVertex r) x=0 → ∃ i,neighbor0 r i=x := by decide +kernel

theorem neighbor1_complete : ∀ r : Fin 10, ∀ x : Fin 15,
  x ≠ rootVertex r → k15Template (rootTwisted r) (rootVertex r) x=1 → ∃ i,neighbor1 r i=x := by decide +kernel

theorem neighbor2_complete : ∀ r : Fin 10, ∀ x : Fin 15,
  x ≠ rootVertex r → k15Template (rootTwisted r) (rootVertex r) x=2 → ∃ i,neighbor2 r i=x := by decide +kernel

theorem neighbor0_injective : ∀ r,Function.Injective (neighbor0 r) := by decide +kernel
theorem neighbor1_injective : ∀ r,Function.Injective (neighbor1 r) := by decide +kernel
theorem neighbor2_injective : ∀ r,Function.Injective (neighbor2 r) := by decide +kernel

theorem iso0_complete_at : ∀ r : Fin 10, ∀ p : Fin 24,
  (∀ i j,i ≠ j → k15Template (rootTwisted r) (neighbor0 r (perm4 p i)) (neighbor0 r (perm4 p j))=canonical0 i j) →
  ∃ a : Fin 2, ∀ i,neighbor0 r (perm4 p i)=iso0 r a i := by decide +kernel

theorem iso1_complete_at : ∀ r : Fin 10, ∀ p : Fin 120,
  (∀ i j,i ≠ j → k15Template (rootTwisted r) (neighbor1 r (perm5 p i)) (neighbor1 r (perm5 p j))=canonical1 i j) →
  ∃ a : Fin 10, ∀ i,neighbor1 r (perm5 p i)=iso1 r a i := by decide +kernel

theorem iso2_complete_at : ∀ r : Fin 10, ∀ p : Fin 120,
  (∀ i j,i ≠ j → k15Template (rootTwisted r) (neighbor2 r (perm5 p i)) (neighbor2 r (perm5 p j))=canonical2 i j) →
  ∃ a : Fin 10, ∀ i,neighbor2 r (perm5 p i)=iso2 r a i := by decide +kernel

#print axioms roots_complete
#print axioms iso0_complete_at
#print axioms iso1_complete_at
#print axioms iso2_complete_at
end PricingABD.Rooted455Data
