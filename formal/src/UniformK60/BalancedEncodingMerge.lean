import UniformK60.BalancedEncodingValuation

/-! Independent auxiliary witnesses combine on disjoint intervals, while
all local formulas retain exactly one shared physical valuation. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter

structure Block where
  lower : Nat
  upper : Nat
  clauses : CNF

def Block.owns (b : Block) (a : Nat) : Prop := b.lower < a ∧ a ≤ b.upper

noncomputable def mergeBlocks {n : Nat} (blocks : Fin n → Block)
    (physical : Valuation) (locals : Fin n → Valuation) (cut : Nat) (a : Nat) : Bool := by
  classical
  exact if a ≤ cut then physical a else
    if h : ∃ i, (blocks i).owns a then locals (Classical.choose h) a else false

theorem mergeBlocks_physical {n : Nat} (blocks : Fin n → Block)
    (physical : Valuation) (locals : Fin n → Valuation) (cut a : Nat) (ha : a ≤ cut) :
    mergeBlocks blocks physical locals cut a = physical a := by
  simp only [mergeBlocks,if_pos ha]

theorem mergeBlocks_local {n : Nat} (blocks : Fin n → Block)
    (physical : Valuation) (locals : Fin n → Valuation) (cut : Nat)
    (separate : ∀ i j a, (blocks i).owns a → (blocks j).owns a → i = j)
    (agree : ∀ i a, a ≤ cut → locals i a = physical a)
    (i : Fin n) (a : Nat) (ha : a ≤ cut ∨ (blocks i).owns a) :
    mergeBlocks blocks physical locals cut a = locals i a := by
  classical
  by_cases hp : a ≤ cut
  · exact (mergeBlocks_physical blocks physical locals cut a hp).trans (agree i a hp).symm
  · have own : (blocks i).owns a := ha.resolve_left hp
    have he : ∃ j, (blocks j).owns a := ⟨i,own⟩
    simp only [mergeBlocks,if_neg hp,dif_pos he]
    rw [separate _ i a (Classical.choose_spec he) own]

/-- A compositional lemma for exact CNF blocks. Its callers prove the range
and support conditions and construct every local valuation from one host. -/
theorem blocks_satisfiable {n : Nat} (blocks : Fin n → Block)
    (physical : Valuation) (cut : Nat)
    (separate : ∀ i j a, (blocks i).owns a → (blocks j).owns a → i = j)
    (support : ∀ i clause, clause ∈ (blocks i).clauses → ∀ lit ∈ clause,
      lit.2 ≤ cut ∨ (blocks i).owns lit.2)
    (local_sat : ∀ i, ∃ v : Valuation, FormulaSat v (blocks i).clauses ∧
      ∀ a, a ≤ cut → v a = physical a) :
    ∃ v : Valuation,
      FormulaSat v ((List.finRange n).flatMap fun i => (blocks i).clauses) ∧
      ∀ a, a ≤ cut → v a = physical a := by
  classical
  let locals : Fin n → Valuation := fun i => Classical.choose (local_sat i)
  have hs (i : Fin n) : FormulaSat (locals i) (blocks i).clauses :=
    (Classical.choose_spec (local_sat i)).1
  have ha (i : Fin n) (a : Nat) (h : a ≤ cut) : locals i a = physical a :=
    (Classical.choose_spec (local_sat i)).2 a h
  let v := mergeBlocks blocks physical locals cut
  refine ⟨v,?_,mergeBlocks_physical blocks physical locals cut⟩
  intro clause hc
  obtain ⟨i,_,hclause⟩ := List.mem_flatMap.mp hc
  obtain ⟨lit,hl,hvalue⟩ := hs i clause hclause
  exact ⟨lit,hl,(mergeBlocks_local blocks physical locals cut separate ha i lit.2
    (support i clause hclause lit hl)).trans hvalue⟩

#print axioms blocks_satisfiable
end UniformK60.BalancedEncoding
