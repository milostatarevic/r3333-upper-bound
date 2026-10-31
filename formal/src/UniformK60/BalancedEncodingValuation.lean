import UniformK60.BalancedVisible

/-! Fresh local auxiliary choices preserve the already chosen physical host.
This extension works for the literal auxiliary IDs recorded by the encoder. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical

abbrev LocalSlot (n : Nat) := (Fin n × Fin 11) ⊕ Fin 6

def slotAtom {n : Nat} (g : Geometry n) : LocalSlot n → Nat
  | .inl (m,t) => g.roleAtom m t
  | .inr k => g.stateAtom k

def slotValue {n : Nat} {c : Host} {g : Geometry n}
    (w : LocalWitness c g) : LocalSlot n → Bool
  | .inl (m,t) => decide (w.role m = some t)
  | .inr k => decide (k = w.state)

noncomputable def extendLocal {n : Nat} {c : Host} {g : Geometry n}
    (old : Valuation) (w : LocalWitness c g) (a : Nat) : Bool := by
  classical
  exact if h : ∃ s, slotAtom g s = a then slotValue w (Classical.choose h) else old a

theorem extendLocal_at {n : Nat} {c : Host} {g : Geometry n}
    (old : Valuation) (w : LocalWitness c g)
    (hi : Function.Injective (slotAtom g)) (s : LocalSlot n) :
    extendLocal old w (slotAtom g s) = slotValue w s := by
  classical
  have he : ∃ t, slotAtom g t = slotAtom g s := ⟨s,rfl⟩
  simp only [extendLocal,dif_pos he]
  exact congrArg (slotValue w) (hi (Classical.choose_spec he))

theorem extendLocal_below {n : Nat} {c : Host} {g : Geometry n}
    (old : Valuation) (w : LocalWitness c g) (top : Nat)
    (fresh : ∀ s, top < slotAtom g s) (a : Nat) (ha : a ≤ top) :
    extendLocal old w a = old a := by
  classical
  have he : ¬∃ s, slotAtom g s = a := by
    rintro ⟨s,hs⟩
    have h := fresh s
    omega
  simp only [extendLocal,dif_neg he]

/-- One actual pentagon scope extends any physical valuation. The entire
previous prefix below `top` is unchanged; no host edge is recolored. -/
theorem actual_embedding_extension {n : Nat} {c : Host} {g : Geometry n}
    (hc : NoMonochromaticTriangle c) (hg : ActualGeometry c g)
    (old : Valuation) (hp : PhysicalMatches old c) (top : Nat) (htop : 7080 ≤ top)
    (hi : Function.Injective (slotAtom g)) (fresh : ∀ s, top < slotAtom g s) :
    ∃ v : Valuation, FormulaSat v (embeddingClauses g) ∧
      (∀ a, a ≤ top → v a = old a) ∧ PhysicalMatches v c := by
  obtain ⟨w⟩ := actual_local_witness hc hg
  let v := extendLocal old w
  have unchanged : ∀ a, a ≤ top → v a = old a :=
    extendLocal_below old w top fresh
  have phys : PhysicalMatches v c := by
    intro a b hab q
    have bound := (edgeVar_bounds a b q hab).2
    exact (unchanged _ (by omega)).trans (hp a b hab q)
  refine ⟨v,embedding_sat v w phys ?_ ?_,unchanged,phys⟩
  · intro m t
    exact extendLocal_at old w hi (.inl (m,t))
  · intro k
    exact extendLocal_at old w hi (.inr k)

#print axioms actual_embedding_extension
end UniformK60.BalancedEncoding
