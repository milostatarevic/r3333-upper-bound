import UniformK60.SequentialCounter

set_option autoImplicit false
namespace UniformK60.SequentialCounter
open Ramsey61.DenseCounter

theorem regular_atoms_input_or_fresh (x : Nat → Nat) (n k top : Nat)
    (hk : 0 < k) (hn : k+1 < n)
    (clause : List Literal) (hc : clause ∈ regular x n k top)
    (lit : Literal) (hl : lit ∈ clause) : (∃ i<n, lit.2 = x i) ∨
      (top < lit.2 ∧ lit.2 ≤ top+(n-k)*k) := by
  have hm : 2 ≤ n-k := by omega
  have input_bound (i : Nat) (hi : i<n) :
      (∃ e<n, x i=x e) ∨ (top<x i ∧ x i≤top+(n-k)*k) := Or.inl ⟨i,hi,rfl⟩
  have cell_bound (d : Nat) (hd : d<n-k) (j : Nat) (hj : j<k) :
      (∃ e<n, cell top k d j=x e) ∨
        (top<cell top k d j ∧ cell top k d j≤top+(n-k)*k) := by
    exact Or.inr ⟨by unfold cell;omega,cell_le top k (n-k) d j hm hd hj⟩
  obtain ⟨d,hd,hc⟩ := List.mem_flatMap.mp hc
  have hd : d<n-k := List.mem_range.mp hd
  rcases List.mem_append.mp hc with hs | hcap
  · obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hs
    have hj : j<k := List.mem_range.mp hj
    rcases List.mem_append.mp hc with hmain | hforward
    · have hmain := List.mem_singleton.mp hmain
      subst clause
      by_cases hzero : j=0
      · simp only [hzero,if_pos,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl | rfl
        · exact input_bound (d+0) (by omega)
        · exact cell_bound d hd 0 hk
      · simp only [hzero,if_false,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact input_bound (d+j) (by omega)
        · exact cell_bound d hd (j-1) (by omega)
        · exact cell_bound d hd j hj
    · by_cases hf : d+1<n-k
      · simp only [hf,if_pos,List.mem_singleton] at hforward
        subst clause
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl | rfl
        · exact cell_bound d hd j hj
        · exact cell_bound (d+1) hf j hj
      · simp [hf] at hforward
  · simp only [List.mem_singleton] at hcap
    subst clause
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · exact input_bound (d+k) (by omega)
    · exact cell_bound d hd (k-1) (by omega)

/-- Every counter literal is a physical input or one of this block's fresh
auxiliary variables. This permits disjoint interval valuation assembly. -/
theorem counter_atoms_input_or_fresh (x : Nat → Nat) (n k top : Nat)
    (clause : List Literal) (hc : clause ∈ counter x n k top)
    (lit : Literal) (hl : lit ∈ clause) :
    (∃ i<n, lit.2=x i) ∨ (top<lit.2 ∧ lit.2≤finalTop n k top) := by
  by_cases hn : n≤k
  · simp [counter,hn] at hc
  by_cases hk : k=0
  · rw [counter,if_neg hn,if_pos hk] at hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi := List.mem_range.mp hi
    have hl := List.mem_singleton.mp hl
    subst lit
    exact Or.inl ⟨i,hi,rfl⟩
  by_cases hlast : k=n-1
  · rw [counter,if_neg hn,if_neg hk,if_pos hlast] at hc
    have hc := List.mem_singleton.mp hc
    subst clause
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
    exact Or.inl ⟨i,List.mem_range.mp hi,rfl⟩
  · rw [counter,if_neg hn,if_neg hk,if_neg hlast] at hc
    have h := regular_atoms_input_or_fresh x n k top (by omega) (by omega) clause hc lit hl
    simpa [finalTop,hn,hk,hlast] using h

#print axioms counter_atoms_input_or_fresh
end UniformK60.SequentialCounter
