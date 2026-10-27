import UniformK61.BalancedAnchorData
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UniformK61.BalancedAnchor
open UniformK61.BalancedEncodingData

def Independent (t : Bool) (S : Finset (Fin 16)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a≠b → R4333.k16Template t a b≠0
instance (t : Bool) (S : Finset (Fin 16)) : Decidable (Independent t S) :=
  inferInstanceAs (Decidable (∀ a ∈ S, ∀ b ∈ S, a≠b → R4333.k16Template t a b≠0))

def supportIndex (t : Bool) (S : Finset (Fin 16)) : Fin 16 :=
  ⟨((List.finRange 16).findIdx (fun i => decide (support t i=S))) % 16,Nat.mod_lt _ (by decide)⟩

def checkSupport (t : Bool) (S : Finset (Fin 16)) : Bool :=
  if Independent t S then decide (support t (supportIndex t S)=S) else true

def checkList (t : Bool) (l : List (Fin 16)) : Bool := checkSupport t l.toFinset

theorem support_check : ∀ t : Bool,
  ((List.finRange 16).sublistsLen 5).all (checkList t)=true := by decide +kernel

/-- All independent five-subsets are covered, rather than only those listed. -/
theorem support_complete (t : Bool) (S : Finset (Fin 16)) (hc : S.card=5)
    (hi : Independent t S) : ∃ i : Fin 16,support t i=S := by
  let l := (List.finRange 16).filter (fun v => decide (v ∈ S))
  have hs : l.toFinset=S := by ext v;simp [l]
  have hn : l.Nodup := (List.nodup_finRange 16).filter _
  have hl : l.length=5 := by rw [←List.toFinset_card_of_nodup hn,hs,hc]
  have hm : l ∈ (List.finRange 16).sublistsLen 5 :=
    List.mem_sublistsLen.mpr ⟨List.filter_sublist,hl⟩
  have hh := List.all_eq_true.mp (support_check t) l hm
  refine ⟨supportIndex t S,?_⟩
  simpa only [checkList,hs,checkSupport,if_pos hi,decide_eq_true_eq] using hh

#print axioms support_complete
end UniformK61.BalancedAnchor
