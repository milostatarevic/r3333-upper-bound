import UniformK60.BalancedEncodingAllFiveLocal
import UniformK60.BalancedEncodingLinear
import UniformK60.BalancedEncodingMerge
import UniformK60.BalancedEncodingGuardBounds

set_option autoImplicit false
namespace UniformK60.BalancedEncodingAllFive
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.BalancedHost UniformK60.BalancedEncoding

theorem otherSize_eq (s : Scope) : otherSize (scope s)=16 := by cases scope s <;> rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem guard_ranges : ∀ o s, 7080≤guardStart o s ∧ guardStart o s+guardCount o s≤guardTop o := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem guard_separated : ∀ o (s t : Scope),s<t → guardStart o s+guardCount o s≤guardStart o t := by decide

def guardBlock (o : Owner) (s : Scope) : Block where
  lower := guardStart o s
  upper := guardStart o s+guardCount o s
  clauses := guardClauses (guardGeometry o s)

def embeddingStart (o : Owner) (s : Scope) : Nat := guardTop o+182*s.val

def embeddingBlock (o : Owner) (s : Scope) : Block where
  lower := embeddingStart o s
  upper := embeddingStart o s+182
  clauses := []

theorem guardBlocks_separate (o : Owner) (s t : Scope) (a : Nat)
    (hs : (guardBlock o s).owns a) (ht : (guardBlock o t).owns a) : s=t := by
  change guardStart o s<a ∧ a≤guardStart o s+guardCount o s at hs
  change guardStart o t<a ∧ a≤guardStart o t+guardCount o t at ht
  rcases lt_trichotomy s t with h | h | h
  · have hh := guard_separated o s t h;omega
  · exact h
  · have hh := guard_separated o t s h;omega

theorem embeddingBlocks_separate (o : Owner) (s t : Scope) (a : Nat)
    (hs : (embeddingBlock o s).owns a) (ht : (embeddingBlock o t).owns a) : s=t := by
  change guardTop o+182*s.val<a ∧ a≤guardTop o+182*s.val+182 at hs
  change guardTop o+182*t.val<a ∧ a≤guardTop o+182*t.val+182 at ht
  apply Fin.ext
  omega

theorem embedding_slot_linear (o : Owner) (s : Scope) :
    slotAtom (embeddingGeometry o s)=linearSlot (otherSize (scope s)) (embeddingStart o s) := by
  funext a
  cases a with
  | inl a => rfl
  | inr k =>
    change guardTop o+182*s.val+176+k.val+1=embeddingStart o s+11*otherSize (scope s)+k.val+1
    rw [otherSize_eq]
    rfl

theorem embedding_slot_injective (o : Owner) (s : Scope) :
    Function.Injective (slotAtom (embeddingGeometry o s)) := by
  rw [embedding_slot_linear]
  exact linearSlot_injective _ _

theorem embedding_slot_owns (o : Owner) (s : Scope) (a : LocalSlot (otherSize (scope s))) :
    (embeddingBlock o s).owns (slotAtom (embeddingGeometry o s) a) := by
  have h := linearSlot_bounds (otherSize (scope s)) (embeddingStart o s) a
  rw [←embedding_slot_linear] at h
  have hn := otherSize_eq s
  refine ⟨h.1,?_⟩
  change slotAtom (embeddingGeometry o s) a≤embeddingStart o s+182
  omega

theorem embedding_slot_fresh (o : Owner) (s : Scope) (a : LocalSlot (otherSize (scope s))) :
    guardTop o<slotAtom (embeddingGeometry o s) a := by
  have h := (embedding_slot_owns o s a).1
  change embeddingStart o s<_ at h
  unfold embeddingStart at h
  omega

theorem guardTop_lower (o : Owner) : 7080≤guardTop o := by
  have h := guard_ranges o 0
  omega

end UniformK60.BalancedEncodingAllFive
