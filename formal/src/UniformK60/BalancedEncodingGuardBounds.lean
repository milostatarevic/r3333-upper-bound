import UniformK60.BalancedEncodingGuard

set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical

theorem oneHot_atoms {n : Nat} (vars : Fin n → Nat)
    (clause : List Literal) (hc : clause ∈ oneHot vars) (lit : Literal) (hl : lit ∈ clause) :
    ∃ i, lit.2=vars i := by
  simp only [oneHot,UniformK61.BalancedEncoding.oneHot,List.mem_append] at hc
  rcases hc with hc | hc
  · have he := List.mem_singleton.mp hc
    subst clause
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hl
    exact ⟨i,rfl⟩
  · obtain ⟨⟨i,j⟩,_,rfl⟩ := List.mem_map.mp hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨i,rfl⟩
    · exact ⟨j,rfl⟩

theorem guard_atoms {n p : Nat} (g : GuardGeometry n p)
    (clause : List Literal) (hc : clause ∈ guardClauses g) (lit : Literal) (hl : lit ∈ clause) :
    lit.2≤7080 ∨ ∃ i,lit.2=g.selector i := by
  rw [guardClauses,List.mem_append] at hc
  rcases hc with hc | hc
  · exact Or.inr (oneHot_atoms g.selector clause hc lit hl)
  · obtain ⟨i,_,hcl⟩ := List.mem_flatMap.mp hc
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hcl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · exact Or.inr ⟨i,rfl⟩
    · exact Or.inl (by
        have h := (edgeVar_bounds g.center (g.member m) g.color (g.distinct m)).2
        change edgeVar g.center (g.member m) g.color≤7080
        omega)

theorem guard_atoms_le {n p : Nat} (g : GuardGeometry n p) (top : Nat)
    (htop : 7080≤top) (hs : ∀ i,g.selector i≤top)
    (clause : List Literal) (hc : clause ∈ guardClauses g) (lit : Literal) (hl : lit ∈ clause) :
    lit.2≤top := by
  rcases guard_atoms g clause hc lit hl with h | ⟨i,he⟩
  · exact le_trans h htop
  · rw [he]
    exact hs i

#print axioms guard_atoms
end UniformK60.BalancedEncoding
