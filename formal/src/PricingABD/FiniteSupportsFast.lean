import Ramsey61.ABDExtraction
import R4333Lean.CriticalTemplateDeletion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Sublists

namespace PricingABD.FiniteSupportsFast
open Finset
abbrev V := Fin 15
abbrev K := R4333.ThreeColor

def T (a b : V) : K := R4333.k15Twisted a b

/-- The nontrivial color-preserving automorphism of the actual T15 template. -/
def swapMap : V → V := ![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7]

theorem swapMap_involutive : Function.Involutive swapMap := by
  unfold Function.Involutive
  decide

def swap : V ≃ V :=
  { toFun := swapMap, invFun := swapMap,
    left_inv := swapMap_involutive, right_inv := swapMap_involutive }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem swap_preserves : ∀ a b, a ≠ b → T (swap a) (swap b) = T a b := by decide

/-- Actual colored P4 support predicate, rather than arbitrary independent four-set. -/
def ProperFour (s : Finset V) : Prop :=
  (∀ a ∈ s, ∀ b ∈ s, a ≠ b → T a b ≠ 2) ∧
  (∀ a ∈ s, (s.filter fun b => b ≠ a ∧ T a b = 0).card = 1 ∨
    (s.filter fun b => b ≠ a ∧ T a b = 0).card = 2) ∧
  (s.filter fun a => (s.filter fun b => b ≠ a ∧ T a b = 0).card = 1).card = 2

def ProperFive (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → T a b ≠ 2

instance (s : Finset V) : Decidable (ProperFour s) := inferInstanceAs (Decidable (_ ∧ _))
instance (s : Finset V) : Decidable (ProperFive s) := inferInstanceAs (Decidable (∀ a ∈ s, ∀ b ∈ s, _))

def representatives4 : List (Finset V) := [
  {0,1,2,10},
  {0,1,2,13},
  {0,1,3,11},
  {0,1,10,13},
  {0,2,3,8},
  {0,2,3,12},
  {0,2,8,12},
  {0,2,10,13},
  {0,2,12,13},
  {0,7,8,10},
  {0,7,8,11},
  {0,7,8,12},
  {0,7,10,11},
  {0,7,12,13},
  {0,8,10,11},
  {1,2,9,14},
  {1,2,10,13},
  {1,5,9,10},
  {1,5,9,11},
  {1,5,9,14},
  {1,5,10,13},
  {1,5,13,14},
  {1,9,10,11},
  {2,6,8,9},
  {2,6,9,10},
  {2,6,9,14},
  {2,6,10,13},
  {2,6,12,13},
  {2,6,12,14},
  {2,6,13,14},
  {2,8,9,10},
  {2,12,13,14},
  {4,5,6,9},
  {4,5,6,14},
  {4,5,9,14},
  {4,6,7,12},
  {4,6,9,14},
  {5,6,7,10}]

def physicalOrders4 : Fin 38 → Fin 4 → V := ![
  ![1,0,10,2],
  ![0,1,13,2],
  ![0,1,11,3],
  ![10,0,1,13],
  ![0,8,2,3],
  ![0,12,3,2],
  ![12,0,8,2],
  ![0,10,2,13],
  ![0,12,13,2],
  ![10,0,8,7],
  ![0,8,7,11],
  ![12,0,8,7],
  ![0,10,11,7],
  ![0,12,13,7],
  ![8,0,10,11],
  ![9,1,14,2],
  ![1,13,2,10],
  ![1,9,5,10],
  ![11,1,9,5],
  ![14,1,9,5],
  ![1,13,5,10],
  ![14,1,13,5],
  ![9,1,11,10],
  ![2,8,9,6],
  ![2,10,6,9],
  ![2,14,6,9],
  ![13,2,10,6],
  ![2,13,12,6],
  ![2,14,6,12],
  ![13,2,14,6],
  ![10,2,8,9],
  ![14,2,13,12],
  ![4,5,9,6],
  ![5,4,14,6],
  ![14,4,5,9],
  ![4,12,6,7],
  ![4,14,6,9],
  ![5,10,6,7]]

def representatives5 : List (Finset V) := [
  {0,1,2,10,13},
  {0,2,3,8,12},
  {0,7,8,10,11},
  {1,5,9,10,11},
  {2,6,8,9,10},
  {2,6,12,13,14},
  {4,5,6,9,14}]

def physicalOrders5 : Fin 7 → Fin 5 → V := ![
  ![0,1,13,2,10],
  ![0,8,2,3,12],
  ![0,8,7,11,10],
  ![1,9,5,10,11],
  ![2,10,6,9,8],
  ![2,14,6,12,13],
  ![4,5,9,6,14]]

def Covered (representatives : List (Finset V)) (s : Finset V) : Prop :=
  s ∈ representatives ∨ s.image swap ∈ representatives
instance (representatives : List (Finset V)) (s : Finset V) :
    Decidable (Covered representatives s) := inferInstanceAs (Decidable (_ ∨ _))

/-- Every finite support occurs as a literal sublist of the full15-label list. -/
theorem support_as_sublist (s : Finset V) (k : Nat) (hk : s.card = k) :
    ∃ xs ∈ (List.finRange 15).sublistsLen k, xs.toFinset = s := by
  let xs := (List.finRange 15).filter fun v => v ∈ s
  have hsub : List.Sublist xs (List.finRange 15) := List.filter_sublist
  have hnd : xs.Nodup := (List.nodup_finRange 15).sublist hsub
  have hset : xs.toFinset = s := by ext v; simp [xs]
  have hlen : xs.length = k := by
    rw [←List.toFinset_card_of_nodup hnd,hset,hk]
  exact ⟨xs,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,hset⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem all_five_sublists_checked :
    ((List.finRange 15).sublistsLen 5).all
      (fun xs => decide (ProperFive xs.toFinset → Covered representatives5 xs.toFinset)) = true := by decide +kernel

theorem five_support_cover (s : Finset V) (hcard : s.card = 5) (hs : ProperFive s) :
    ∃ r ∈ representatives5, ∃ e : V ≃ V,
      (∀ a b, a ≠ b → T (e a) (e b) = T a b) ∧ s.image e = r := by
  obtain ⟨xs,hxs,hset⟩ := support_as_sublist s 5 hcard
  have ht := (List.all_eq_true.mp all_five_sublists_checked) xs hxs
  have hc : Covered representatives5 s := by
    have hh := of_decide_eq_true ht
    rw [hset] at hh
    exact hh hs
  rcases hc with hc | hc
  · exact ⟨s,hc,Equiv.refl _,by simp,by simp⟩
  · exact ⟨s.image swap,hc,swap,swap_preserves,rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem all_four_sublists_checked :
    ((List.finRange 15).sublistsLen 4).all
      (fun xs => decide (ProperFour xs.toFinset → Covered representatives4 xs.toFinset)) = true := by decide +kernel

theorem four_support_cover (s : Finset V) (hcard : s.card = 4) (hs : ProperFour s) :
    ∃ r ∈ representatives4, ∃ e : V ≃ V,
      (∀ a b, a ≠ b → T (e a) (e b) = T a b) ∧ s.image e = r := by
  obtain ⟨xs,hxs,hset⟩ := support_as_sublist s 4 hcard
  have ht := (List.all_eq_true.mp all_four_sublists_checked) xs hxs
  have hc : Covered representatives4 s := by
    have hh := of_decide_eq_true ht
    rw [hset] at hh
    exact hh hs
  rcases hc with hc | hc
  · exact ⟨s,hc,Equiv.refl _,by simp,by simp⟩
  · exact ⟨s.image swap,hc,swap,swap_preserves,rfl⟩

#print axioms five_support_cover
#print axioms four_support_cover
#check five_support_cover
#check four_support_cover
end PricingABD.FiniteSupportsFast
