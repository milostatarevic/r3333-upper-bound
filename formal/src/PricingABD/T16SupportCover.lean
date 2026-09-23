import PricingABD.FiniteSupportsFast
namespace PricingABD.T16SupportCover
open Finset
abbrev V := Fin 16
abbrev K := R4333.ThreeColor
 def T (a b : V) : K := R4333.k16Twisted a b
 def autoMap : Fin 32 → V → V := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![0,8,11,3,14,6,5,13,1,9,10,2,15,7,4,12],![1,0,3,2,6,7,4,5,9,8,11,10,14,15,12,13],![1,9,10,2,12,4,7,15,0,8,11,3,13,5,6,14],![2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14],![2,10,9,1,15,7,4,12,3,11,8,0,14,6,5,13],![3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12],![3,11,8,0,13,5,6,14,2,10,9,1,12,4,7,15],![4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11],![4,12,15,7,10,2,1,9,5,13,14,6,11,3,0,8],![5,4,7,6,2,3,0,1,13,12,15,14,10,11,8,9],![5,13,14,6,8,0,3,11,4,12,15,7,9,1,2,10],![6,7,4,5,1,0,3,2,14,15,12,13,9,8,11,10],![6,14,13,5,11,3,0,8,7,15,12,4,10,2,1,9],![7,6,5,4,3,2,1,0,15,14,13,12,11,10,9,8],![7,15,12,4,9,1,2,10,6,14,13,5,8,0,3,11],![8,0,3,11,5,13,14,6,9,1,2,10,4,12,15,7],![8,9,10,11,15,14,13,12,0,1,2,3,7,6,5,4],![9,1,2,10,7,15,12,4,8,0,3,11,6,14,13,5],![9,8,11,10,13,12,15,14,1,0,3,2,5,4,7,6],![10,2,1,9,4,12,15,7,11,3,0,8,5,13,14,6],![10,11,8,9,14,15,12,13,2,3,0,1,6,7,4,5],![11,3,0,8,6,14,13,5,10,2,1,9,7,15,12,4],![11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7],![12,4,7,15,1,9,10,2,13,5,6,14,0,8,11,3],![12,13,14,15,11,10,9,8,4,5,6,7,3,2,1,0],![13,5,6,14,3,11,8,0,12,4,7,15,2,10,9,1],![13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2],![14,6,5,13,0,8,11,3,15,7,4,12,1,9,10,2],![14,15,12,13,10,11,8,9,6,7,4,5,2,3,0,1],![15,7,4,12,2,10,9,1,14,6,5,13,3,11,8,0],![15,14,13,12,8,9,10,11,7,6,5,4,0,1,2,3]]
 set_option maxRecDepth 1000000
 set_option maxHeartbeats 0
 theorem auto_bijective : ∀ i,Function.Bijective (autoMap i) := by decide +kernel
 theorem auto_preserves : ∀ i,∀ a b,a≠b → T (autoMap i a) (autoMap i b)=T a b := by decide +kernel
 noncomputable def autoEquiv (i : Fin 32) : V ≃ V := Equiv.ofBijective (autoMap i) (auto_bijective i)
 def ProperFour (s : Finset V) : Prop :=
  (∀ a ∈ s,∀ b ∈ s,a≠b → T a b≠2) ∧
  (∀ a ∈ s,(s.filter fun b => b≠a ∧ T a b=0).card=1 ∨ (s.filter fun b => b≠a ∧ T a b=0).card=2) ∧
  (s.filter fun a => (s.filter fun b => b≠a ∧ T a b=0).card=1).card=2
 def ProperFive (s : Finset V) : Prop := ∀ a ∈ s,∀ b ∈ s,a≠b → T a b≠2
 instance (s : Finset V) : Decidable (ProperFour s) := inferInstanceAs (Decidable (_ ∧ _))
 instance (s : Finset V) : Decidable (ProperFive s) := inferInstanceAs (Decidable (∀ a ∈ s,∀ b ∈ s,_))
 def representatives4 : List (Finset V) := [{0,1,2,10},{0,1,2,13},{0,1,10,13},{0,1,13,15}]
 def representatives5 : List (Finset V) := [{0,1,2,10,13}]
 def Covered (rs : List (Finset V)) (s : Finset V) : Prop := ∃ i : Fin 32,s.image (autoMap i) ∈ rs
 instance (rs : List (Finset V)) (s : Finset V) : Decidable (Covered rs s) := inferInstanceAs (Decidable (∃ i : Fin 32,_))
 theorem support_as_sublist (s : Finset V) (k : Nat) (hk : s.card=k) :
    ∃ xs ∈ (List.finRange 16).sublistsLen k,xs.toFinset=s := by
  let xs := (List.finRange 16).filter fun v => v ∈ s
  have hsub : List.Sublist xs (List.finRange 16) := List.filter_sublist
  have hnd : xs.Nodup := (List.nodup_finRange 16).sublist hsub
  have hset : xs.toFinset=s := by ext v;simp [xs]
  have hlen : xs.length=k := by rw [←List.toFinset_card_of_nodup hnd,hset,hk]
  exact ⟨xs,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,hset⟩
 theorem all_four_checked : ((List.finRange 16).sublistsLen 4).all
    (fun xs => decide (ProperFour xs.toFinset → Covered representatives4 xs.toFinset))=true := by decide +kernel
 theorem all_five_checked : ((List.finRange 16).sublistsLen 5).all
    (fun xs => decide (ProperFive xs.toFinset → Covered representatives5 xs.toFinset))=true := by decide +kernel
 theorem four_support_cover (s : Finset V) (hc : s.card=4) (hp : ProperFour s) :
    ∃ r ∈ representatives4,∃ e : V ≃ V,(∀ a b,a≠b → T (e a) (e b)=T a b) ∧ s.image e=r := by
  obtain ⟨xs,hxs,hset⟩ := support_as_sublist s 4 hc
  have hh := of_decide_eq_true ((List.all_eq_true.mp all_four_checked) xs hxs)
  rw [hset] at hh
  obtain ⟨i,hi⟩ := hh hp
  exact ⟨s.image (autoMap i),hi,autoEquiv i,auto_preserves i,rfl⟩
 theorem five_support_cover (s : Finset V) (hc : s.card=5) (hp : ProperFive s) :
    ∃ r ∈ representatives5,∃ e : V ≃ V,(∀ a b,a≠b → T (e a) (e b)=T a b) ∧ s.image e=r := by
  obtain ⟨xs,hxs,hset⟩ := support_as_sublist s 5 hc
  have hh := of_decide_eq_true ((List.all_eq_true.mp all_five_checked) xs hxs)
  rw [hset] at hh
  obtain ⟨i,hi⟩ := hh hp
  exact ⟨s.image (autoMap i),hi,autoEquiv i,auto_preserves i,rfl⟩
#print axioms four_support_cover
#print axioms five_support_cover
end PricingABD.T16SupportCover
