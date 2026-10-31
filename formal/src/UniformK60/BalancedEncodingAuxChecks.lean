import UniformK60.BalancedEncodingData
import Mathlib.Order.Fin.Basic

/-! Ordinary-kernel checks of the finite auxiliary allocation. These check
counter sizes and separated numeric ranges, not SAT or mathematical coverage. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 UniformK60.Physical UniformK60.BalancedHost

abbrev DegreeIndex := Fin 240

def degreeIndex (v : Vertex) (q : Color) : DegreeIndex := ⟨4*v.val+q.val,by omega⟩
def degreeStartAt (o : Owner) (i : DegreeIndex) : Nat :=
  (BalancedAuxData.degreeStarts[BalancedAuxData.ownerIndex o]!)[i.val]!
def degreeEndAt (o : Owner) (i : DegreeIndex) : Nat :=
  (BalancedAuxData.degreeEnds[BalancedAuxData.ownerIndex o]!)[i.val]!

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem degree_counter_end : ∀ (o : Owner) (v : Vertex) (q : Color),
    SequentialCounter.finalTop (unknownNeighbors o v).length (degreeBound o v q)
      (degreeStart o (v,q)) = degreeEnd o (v,q) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degree_interval_bounds : ∀ (o : Owner) (i : DegreeIndex),
    7080 ≤ degreeStartAt o i ∧ degreeStartAt o i ≤ degreeEndAt o i ∧ degreeEndAt o i ≤ degreeTop o := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degree_adjacent : ∀ (o : Owner) (i : Fin 239),
    degreeEndAt o i.castSucc ≤ degreeStartAt o i.succ := by decide +kernel

theorem degree_start_monotone (o : Owner) : Monotone (degreeStartAt o) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact le_trans (degree_interval_bounds o i.castSucc).2.1 (degree_adjacent o i)

theorem degree_before (o : Owner) (i j : DegreeIndex) (hij : i < j) :
    degreeEndAt o i ≤ degreeStartAt o j := by
  have hi : i.val < 239 := by have := j.isLt;change i.val<j.val at hij;omega
  let k : Fin 239 := ⟨i.val,hi⟩
  have hk : k.castSucc = i := Fin.ext rfl
  have hkj : k.succ ≤ j := by change i.val+1 ≤ j.val;exact hij
  exact le_trans (by simpa only [hk] using degree_adjacent o k) (degree_start_monotone o hkj)

theorem degree_intervals_separate (o : Owner) (i j : DegreeIndex) (a : Nat)
    (hi : degreeStartAt o i < a ∧ a ≤ degreeEndAt o i)
    (hj : degreeStartAt o j < a ∧ a ≤ degreeEndAt o j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hh := degree_before o i j h;omega
  · exact h
  · have hh := degree_before o j i h;omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem guard_intervals : ∀ (o : Owner) (s : Scope),
    degreeTop o ≤ guardStart o s ∧ guardStart o s+guardCount o s ≤ guardTop o := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem guard_separated : ∀ (o : Owner) (s t : Scope), s < t →
    guardStart o s+guardCount o s ≤ guardStart o t := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem embedding_intervals : ∀ (o : Owner) (s : Scope),
    guardTop o ≤ embeddingStart o s ∧
      embeddingStart o s+embeddingWidth o s ≤ finalTop o := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem embedding_separated : ∀ (o : Owner) (s t : Scope), s < t →
    embeddingStart o s+embeddingWidth o s ≤ embeddingStart o t := by decide +kernel

#print axioms degree_counter_end
#print axioms degree_intervals_separate
end UniformK60.BalancedEncodingData
