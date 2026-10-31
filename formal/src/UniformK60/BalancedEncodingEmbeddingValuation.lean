import UniformK60.BalancedEncodingBlocks
import UniformK60.BalancedEncodingGuardValuation

/-! Disjoint pentagon auxiliaries extend all physical and degree/guard
variables. Each scope is interpreted inside the same actual host. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.BalancedHost UniformK60.BalancedEncoding
open UniformK61.BalancedEncoding (sat_flatMap)

def embeddingBlock (o : Owner) (s : Scope) : Block where
  lower := embeddingStart o s
  upper := embeddingStart o s+embeddingWidth o s
  clauses := []

theorem embeddingBlocks_separate (o : Owner) (s t : Scope) (a : Nat)
    (hs : (embeddingBlock o s).owns a) (ht : (embeddingBlock o t).owns a) : s=t := by
  change embeddingStart o s<a ∧ a≤embeddingStart o s+embeddingWidth o s at hs
  change embeddingStart o t<a ∧ a≤embeddingStart o t+embeddingWidth o t at ht
  rcases lt_trichotomy s t with h | h | h
  · have hh := embedding_separated o s t h;omega
  · exact h
  · have hh := embedding_separated o t s h;omega

theorem embedding_slot_owns (o : Owner) (s : Scope) (h : AnchorReady o (scope s))
    (a : LocalSlot (otherSize (scope s))) :
    (embeddingBlock o s).owns (slotAtom (embeddingGeometry o s h) a) := by
  unfold Block.owns embeddingBlock
  rw [embeddingWidth,if_pos h]
  cases a with
  | inl a =>
    change embeddingStart o s<embeddingStart o s+11*a.1.val+a.2.val+1 ∧
      embeddingStart o s+11*a.1.val+a.2.val+1≤embeddingStart o s+(11*otherSize (scope s)+6)
    have hm := a.1.isLt
    have ht := a.2.isLt
    constructor <;> omega
  | inr k =>
    change embeddingStart o s<embeddingStart o s+11*otherSize (scope s)+k.val+1 ∧
      embeddingStart o s+11*otherSize (scope s)+k.val+1≤embeddingStart o s+(11*otherSize (scope s)+6)
    have hk := k.isLt
    constructor <;> omega

theorem embedding_slot_fresh (o : Owner) (s : Scope) (h : AnchorReady o (scope s))
    (a : LocalSlot (otherSize (scope s))) :
    guardTop o<slotAtom (embeddingGeometry o s h) a := by
  have hs := (embedding_intervals o s).1
  have ha := (embedding_slot_owns o s h a).1
  exact lt_of_le_of_lt hs ha

theorem actual_embedding_family_extension {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o)
    (old : Valuation) (hp : PhysicalMatches old c) :
    ∃ v : Valuation,FormulaSat v (embeddings o) ∧
      ∀ a,a≤guardTop o → v a=old a := by
  classical
  have existsWitness (s : Scope) (h : AnchorReady o (scope s)) :
      Nonempty (LocalWitness c (embeddingGeometry o s h)) :=
    normalized_local_witness hc hn (scope s) h
      (embeddingGeometry o s h).roleAtom (embeddingGeometry o s h).stateAtom
  let witness (s : Scope) (h : AnchorReady o (scope s)) := Classical.choice (existsWitness s h)
  let locals (s : Scope) : Valuation :=
    if h : AnchorReady o (scope s) then extendLocal old (witness s h) else old
  have agree (s : Scope) (a : Nat) (ha : a≤guardTop o) : locals s a=old a := by
    by_cases h : AnchorReady o (scope s)
    · simp only [locals,dif_pos h]
      exact extendLocal_below old (witness s h) (guardTop o) (embedding_slot_fresh o s h) a ha
    · simp only [locals,dif_neg h]
  let v := mergeBlocks (embeddingBlock o) old locals (guardTop o)
  have preserve (a : Nat) (ha : a≤guardTop o) : v a=old a :=
    mergeBlocks_physical (embeddingBlock o) old locals (guardTop o) a ha
  have phys : PhysicalMatches v c := by
    intro a b hab q
    have hb := (edgeVar_bounds a b q hab).2
    have htop := guardTop_lower o
    change 122259≤guardTop o at htop
    exact (preserve _ (by omega)).trans (hp a b hab q)
  have at_slot (s : Scope) (h : AnchorReady o (scope s))
      (a : LocalSlot (otherSize (scope s))) :
      v (slotAtom (embeddingGeometry o s h) a)=slotValue (witness s h) a := by
    have hm := mergeBlocks_local (embeddingBlock o) old locals (guardTop o)
      (embeddingBlocks_separate o) agree s (slotAtom (embeddingGeometry o s h) a)
      (Or.inr (embedding_slot_owns o s h a))
    change v (slotAtom (embeddingGeometry o s h) a)=_ at hm
    rw [hm]
    simp only [locals,dif_pos h]
    exact extendLocal_at old (witness s h) (embedding_slot_injective o s h) a
  refine ⟨v,?_,preserve⟩
  apply sat_flatMap
  intro s _
  split_ifs with h
  · apply embedding_sat v (witness s h) phys
    · intro m t
      exact at_slot s h (.inl (m,t))
    · intro k
      exact at_slot s h (.inr k)
  · intro clause hcl
    exact False.elim (List.not_mem_nil hcl)

#print axioms actual_embedding_family_extension
end UniformK60.BalancedEncodingData
