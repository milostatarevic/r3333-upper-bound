import R4333Lean.SequentialAtMostManyCNF

/-!
# Fresh complement atoms for positive-input cardinality counters

The trusted sequential counter consumes positive SAT atoms.  A lower bound
on a list of atoms can therefore be represented compactly by introducing
one fresh atom for each input, defining it to be the Boolean complement of
that input, and imposing an upper bound on the fresh atoms.

This file defines the exact two-clause equivalence, an explicit semantic
valuation, its preservation and satisfaction theorems, exact namespace
facts, and the true-input-count complement identity.  It does not assert
unsatisfiability of any formula.
-/

namespace R4333
namespace ComplementAtomCNF

open FiniteColorCNF SequentialAtMostCNF

/-- The fresh atom in a reserved leading-tag namespace. -/
def complementAtom (tag key : Nat) : Nat :=
  Nat.pair tag key

@[simp] theorem complementAtom_inNamespace (tag key : Nat) :
    InSequentialNamespace tag (complementAtom tag key) := by
  simp [InSequentialNamespace, complementAtom, Nat.unpair_pair]

theorem complementAtom_injective (tag : Nat) :
    Function.Injective (complementAtom tag) := by
  intro left right h
  exact (Nat.pair_eq_pair.mp h).2

theorem complementAtom_outside_otherNamespace
    {tag reserved key : Nat} (hne : tag ≠ reserved) :
    ¬InSequentialNamespace reserved (complementAtom tag key) := by
  simp [InSequentialNamespace, complementAtom, Nat.unpair_pair, hne]

/-- For source atom `x` and complement atom `z`, the two clauses are
`x ∨ z` and `¬x ∨ ¬z`, i.e. exactly `z ↔ ¬x`. -/
def complementDefinitionClauses
    (tag : Nat) (sourceAtom : Nat → Nat)
    (keys : List Nat) : Sat.Fmla :=
  keys.flatMap fun key =>
    [[Sat.Literal.pos (sourceAtom key),
      Sat.Literal.pos (complementAtom tag key)],
     [Sat.Literal.neg (sourceAtom key),
      Sat.Literal.neg (complementAtom tag key)]]

theorem complementDefinitionClauses_length
    (tag : Nat) (sourceAtom : Nat → Nat) (keys : List Nat) :
    (complementDefinitionClauses tag sourceAtom keys).length =
      2 * keys.length := by
  rw [complementDefinitionClauses, List.length_flatMap]
  simp
  omega

/-- The ordered complement-atom inputs associated to an ordered key list. -/
def complementAtoms (tag : Nat) (keys : List Nat) : List Nat :=
  keys.map (complementAtom tag)

theorem complementAtoms_length (tag : Nat) (keys : List Nat) :
    (complementAtoms tag keys).length = keys.length := by
  simp [complementAtoms]

theorem complementAtoms_nodup (tag : Nat) {keys : List Nat}
    (hkeys : keys.Nodup) : (complementAtoms tag keys).Nodup := by
  exact hkeys.map (complementAtom_injective tag)

theorem complementAtoms_outside_otherNamespace
    {tag reserved : Nat} (hne : tag ≠ reserved) (keys : List Nat) :
    InputsOutsideNamespace reserved (complementAtoms tag keys) := by
  intro atom hatom
  obtain ⟨key, _hkey, rfl⟩ := by
    simpa only [complementAtoms, List.mem_map] using hatom
  exact complementAtom_outside_otherNamespace hne

/-- Explicitly set every atom in the reserved namespace to the complement
of the source selected by its decoded key, and leave every other atom
unchanged. -/
noncomputable def complementExtension
    (tag : Nat) (sourceAtom : Nat → Nat)
    (v : Sat.Valuation) : Sat.Valuation := fun atom =>
  if (Nat.unpair atom).1 = tag then
    ¬v (sourceAtom (Nat.unpair atom).2)
  else v atom

@[simp] theorem complementExtension_complementAtom
    (tag : Nat) (sourceAtom : Nat → Nat)
    (v : Sat.Valuation) (key : Nat) :
    complementExtension tag sourceAtom v (complementAtom tag key) ↔
      ¬v (sourceAtom key) := by
  simp [complementExtension, complementAtom, Nat.unpair_pair]

theorem complementExtension_eq_of_outside
    (tag : Nat) (sourceAtom : Nat → Nat)
    (v : Sat.Valuation) {atom : Nat}
    (houtside : ¬InSequentialNamespace tag atom) :
    complementExtension tag sourceAtom v atom ↔ v atom := by
  have houtside' : (Nat.unpair atom).1 ≠ tag := by
    simpa [InSequentialNamespace] using houtside
  simp [complementExtension, houtside']

private theorem neg_iff_of_atom_iff {v w : Sat.Valuation}
    (literal : Sat.Literal)
    (h : v (literalAtom literal) ↔ w (literalAtom literal)) :
    v.neg literal ↔ w.neg literal := by
  cases literal <;> simp only [literalAtom, Sat.Valuation.neg] at h ⊢
  · exact not_congr h
  · exact h

private theorem satisfies_of_agrees_on_clause
    {v w : Sat.Valuation} (clause : Sat.Clause)
    (hagrees : ∀ literal, List.Mem literal clause →
      (v (literalAtom literal) ↔ w (literalAtom literal)))
    (hw : w.satisfies clause) : v.satisfies clause := by
  revert hagrees hw
  induction clause with
  | nil =>
      intro _ hw
      exact hw
  | cons literal tail ih =>
      intro hagrees hw hvneg
      apply ih
      · intro other hother
        exact hagrees other (List.Mem.tail literal hother)
      · apply hw
        exact (neg_iff_of_atom_iff literal
          (hagrees literal (List.Mem.head tail))).mp hvneg

/-- Any base formula outside the complement namespace remains satisfied. -/
theorem complementExtension_satisfies_base
    (tag : Nat) (sourceAtom : Nat → Nat)
    (base : Sat.Fmla) (v : Sat.Valuation)
    (hbaseOutside : FormulaOutsideNamespace tag base)
    (hbase : v.satisfies_fmla base) :
    (complementExtension tag sourceAtom v).satisfies_fmla base := by
  constructor
  intro clause hclause
  apply satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact complementExtension_eq_of_outside tag sourceAtom v
      (hbaseOutside clause hclause literal hliteral)
  · exact hbase.prop clause hclause

/-- The explicit extension satisfies every two-clause complement
definition, provided each source atom itself lies outside the fresh
namespace. -/
theorem complementExtension_satisfies_definitions
    (tag : Nat) (sourceAtom : Nat → Nat)
    (keys : List Nat) (v : Sat.Valuation)
    (hsourceOutside : ∀ key, key ∈ keys →
      ¬InSequentialNamespace tag (sourceAtom key)) :
    (complementExtension tag sourceAtom v).satisfies_fmla
      (complementDefinitionClauses tag sourceAtom keys) := by
  constructor
  intro clause hclause
  change clause ∈ keys.flatMap (fun key =>
    [[Sat.Literal.pos (sourceAtom key),
      Sat.Literal.pos (complementAtom tag key)],
     [Sat.Literal.neg (sourceAtom key),
      Sat.Literal.neg (complementAtom tag key)]]) at hclause
  obtain ⟨key, hkey, hclause⟩ := List.mem_flatMap.mp hclause
  have hsource := complementExtension_eq_of_outside
    tag sourceAtom v (hsourceOutside key hkey)
  have hcomplement := complementExtension_complementAtom
    tag sourceAtom v key
  rcases List.mem_cons.mp hclause with hfirst | htail
  · subst clause
    by_cases h : v (sourceAtom key)
    · exact satisfies_of_mem_holds _ (List.Mem.head _) (hsource.mpr h)
    · exact satisfies_of_mem_holds _
        (List.Mem.tail _ (List.Mem.head _)) (hcomplement.mpr h)
  · have hsecond := List.mem_singleton.mp htail
    subst clause
    by_cases h : v (sourceAtom key)
    · exact satisfies_of_mem_holds _
        (List.Mem.tail _ (List.Mem.head _)) (by
          intro hcomp
          exact (hcomplement.mp hcomp) h)
    · exact satisfies_of_mem_holds _ (List.Mem.head _) (by
          intro hsourceValue
          exact h (hsource.mp hsourceValue))

/-- Exact Boolean count identity.  Duplicate keys, if deliberately
supplied, are counted as duplicate occurrences on both sides. -/
theorem trueInputCount_complementAtoms
    (tag : Nat) (sourceAtom : Nat → Nat)
    (keys : List Nat) (v : Sat.Valuation) :
    trueInputCount (complementExtension tag sourceAtom v)
        (complementAtoms tag keys) =
      keys.length - trueInputCount v (keys.map sourceAtom) := by
  unfold trueInputCount complementAtoms
  rw [List.countP_map, List.countP_map]
  have hpredicate :
      (truthBit (complementExtension tag sourceAtom v) ∘
          complementAtom tag) =
        (fun key => !truthBit v (sourceAtom key)) := by
    funext key
    apply Bool.eq_iff_iff.mpr
    simp [Function.comp_apply, truthBit,
      complementExtension_complementAtom]
  rw [hpredicate]
  have hpartition : keys.length =
      List.countP (truthBit v ∘ sourceAtom) keys +
        List.countP (fun key => !truthBit v (sourceAtom key)) keys := by
    simpa [Function.comp_apply] using
      keys.length_eq_countP_add_countP (truthBit v ∘ sourceAtom)
  omega

/-- The two-clause definition block avoids any distinct reserved counter
namespace when all of its source atoms do. -/
theorem complementDefinitionClauses_outside_otherNamespace
    {tag reserved : Nat} (hne : tag ≠ reserved)
    (sourceAtom : Nat → Nat) (keys : List Nat)
    (hsourceOutside : ∀ key, key ∈ keys →
      ¬InSequentialNamespace reserved (sourceAtom key)) :
    FormulaOutsideNamespace reserved
      (complementDefinitionClauses tag sourceAtom keys) := by
  intro clause hclause literal hliteral
  change clause ∈ keys.flatMap (fun key =>
    [[Sat.Literal.pos (sourceAtom key),
      Sat.Literal.pos (complementAtom tag key)],
     [Sat.Literal.neg (sourceAtom key),
      Sat.Literal.neg (complementAtom tag key)]]) at hclause
  obtain ⟨key, hkey, hclause⟩ := List.mem_flatMap.mp hclause
  rcases List.mem_cons.mp hclause with hfirst | htail
  · subst clause
    rcases List.mem_cons.mp hliteral with hliteral | hliteral
    · subst literal
      exact hsourceOutside key hkey
    · have hliteral' := List.mem_singleton.mp hliteral
      subst literal
      exact complementAtom_outside_otherNamespace hne
  · have hsecond := List.mem_singleton.mp htail
    subst clause
    rcases List.mem_cons.mp hliteral with hliteral | hliteral
    · subst literal
      exact hsourceOutside key hkey
    · have hliteral' := List.mem_singleton.mp hliteral
      subst literal
      exact complementAtom_outside_otherNamespace hne

#print axioms R4333.ComplementAtomCNF.complementExtension_satisfies_definitions
#print axioms R4333.ComplementAtomCNF.trueInputCount_complementAtoms
#print axioms R4333.ComplementAtomCNF.complementDefinitionClauses_outside_otherNamespace

end ComplementAtomCNF
end R4333
