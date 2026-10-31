import UniformK60.HostNormalizationPartial

set_option autoImplicit false
namespace UniformK60.HostNormalization
open Ramsey61 UniformK60.Physical

/-- An initial prescribed support extends inside its actual root-color cell to
one complete enumeration. No edges are assigned on the unused positions. -/
theorem extend_cell_embedding (c : Host) (r : Vertex) (q : FourColor)
    {k n : Nat} (hkn : k ≤ n) (hd : colorDegree c q r = n)
    (f : Fin k ↪ Vertex) (hf : ∀ i, f i ∈ colorNeighborhood c q r) :
    ∃ g : Fin n ↪ Vertex,
      (∀ i, g (Fin.castLE hkn i) = f i) ∧
      (∀ i, g i ∈ colorNeighborhood c q r) ∧
      (∀ v ∈ colorNeighborhood c q r, ∃ i, g i = v) := by
  classical
  let cell := {v // v ∈ colorNeighborhood c q r}
  have hc : Fintype.card cell = n := by
    simpa only [cell, Fintype.card_coe, colorDegree] using hd
  let e : Fin n ≃ cell := Fintype.equivOfCardEq (by simpa using hc.symm)
  let a : Fin k → cell := fun i => e (Fin.castLE hkn i)
  let b : Fin k → cell := fun i => ⟨f i, hf i⟩
  have ha : Function.Injective a := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) (e.injective h)
  have hb : Function.Injective b := by
    intro i j h
    exact f.injective (congrArg (fun v : cell => v.val) h)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  let g : Fin n ↪ Vertex :=
    ⟨fun i => (p (e i)).val, Subtype.val_injective.comp (p.injective.comp e.injective)⟩
  refine ⟨g, ?_, fun i => (p (e i)).property, ?_⟩
  · intro i
    exact congrArg (fun v : cell => v.val) (hp i)
  · intro v hv
    refine ⟨e.symm (p.symm ⟨v,hv⟩), ?_⟩
    simp [g]

#print axioms extend_cell_embedding
end UniformK60.HostNormalization
