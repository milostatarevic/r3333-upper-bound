import R4333Lean.FiniteColorCNF
import Mathlib.Data.List.Count

/-!
# A linear, Lean-defined sequential at-most counter

This file is the authoritative CNF boundary for the degree caps used by the
order-61 search.  SAT atoms are Lean naturals (hence atom `a` is printed as
DIMACS variable `a + 1`).  A fixed leading `Nat.pair` tag reserves the
auxiliary namespace; the semantic extension theorem explicitly requires that
namespace to be disjoint from the input and base atoms.

The counter is a one-way unary prefix counter.  `sequentialAuxAtom tag i j`
means "among inputs `0,...,i`, at least `j+1` are true".  Only forward
implications are emitted.  A final negative unit forbids threshold
`bound+1`.  Clause order is, deterministically:

1. all input-trigger clauses, in input order;
2. all carry clauses, in row-major `(row,threshold)` order;
3. all increment clauses, in row-major `(row,threshold)` order;
4. the single overflow unit (absent only for an empty input list).
-/

namespace R4333

open FiniteColorCNF

namespace SequentialAtMostCNF

/-- Internal Lean atom `a` is external DIMACS variable `a+1`. -/
def dimacsVar (a : Nat) : Nat := a + 1

@[simp] theorem dimacsVar_pos (a : Nat) : 0 < dimacsVar a := by
  simp [dimacsVar]

/-- The tagged unary-counter atom at zero-based row `i` and threshold `j`.
Threshold `j` denotes the proposition "at least `j+1`". -/
def sequentialAuxAtom (tag i j : Nat) : Nat :=
  Nat.pair tag (Nat.pair i j)

/-- Membership in the entire leading-tag namespace, not merely in the finite
rectangle used by one counter instance.  Reserving the whole namespace makes
collision obligations simple and auditable. -/
def InSequentialNamespace (tag atom : Nat) : Prop :=
  (Nat.unpair atom).1 = tag

@[simp] theorem sequentialAuxAtom_inNamespace (tag i j : Nat) :
    InSequentialNamespace tag (sequentialAuxAtom tag i j) := by
  simp [InSequentialNamespace, sequentialAuxAtom, Nat.unpair_pair]

/-- Every input atom lies outside the chosen auxiliary namespace. -/
def InputsOutsideNamespace (tag : Nat) (inputs : List Nat) : Prop :=
  ∀ atom ∈ inputs, ¬InSequentialNamespace tag atom

/-- Extract the atom carried by a literal. -/
def literalAtom : Sat.Literal → Nat
  | .pos atom => atom
  | .neg atom => atom

/-- Every atom mentioned by a base formula lies outside the chosen auxiliary
namespace. -/
def FormulaOutsideNamespace (tag : Nat) (base : Sat.Fmla) : Prop :=
  ∀ clause, List.Mem clause base → ∀ literal, List.Mem literal clause →
    ¬InSequentialNamespace tag (literalAtom literal)

/-- Input `p+1` for the transition whose previous row is `p`. -/
def transitionInput (inputs : List Nat)
    (p : Fin (inputs.length - 1)) : Nat :=
  inputs.get ⟨p.val + 1, by omega⟩

/-- `x_i -> s(i,1)`, in input order. -/
def triggerClauses (tag : Nat) (inputs : List Nat) : Sat.Fmla :=
  (List.finRange inputs.length).map fun i =>
    [Sat.Literal.neg inputs[i],
     Sat.Literal.pos (sequentialAuxAtom tag i.val 0)]

/-- `s(i,j) -> s(i+1,j)`, in row-major order. -/
def carryClauses (tag : Nat) (inputCount bound : Nat) : Sat.Fmla :=
  (List.finRange (inputCount - 1)).flatMap fun p =>
    (List.range (bound + 1)).map fun j =>
      [Sat.Literal.neg (sequentialAuxAtom tag p.val j),
       Sat.Literal.pos (sequentialAuxAtom tag (p.val + 1) j)]

/-- `x_(i+1) /\ s(i,j) -> s(i+1,j+1)`, in row-major order. -/
def incrementClauses (tag bound : Nat) (inputs : List Nat) : Sat.Fmla :=
  (List.finRange (inputs.length - 1)).flatMap fun p =>
    (List.range bound).map fun j =>
      [Sat.Literal.neg (transitionInput inputs p),
       Sat.Literal.neg (sequentialAuxAtom tag p.val j),
       Sat.Literal.pos (sequentialAuxAtom tag (p.val + 1) (j + 1))]

/-- Forbid the `(bound+1)`st true input in the final prefix. -/
def overflowClauses (tag bound : Nat) (inputs : List Nat) : Sat.Fmla :=
  if _h : inputs.length = 0 then []
  else [[Sat.Literal.neg
    (sequentialAuxAtom tag (inputs.length - 1) bound)]]

/-- The exact, ordered sequential at-most CNF. -/
def sequentialAtMostFmla (tag bound : Nat) (inputs : List Nat) : Sat.Fmla :=
  triggerClauses tag inputs ++
  carryClauses tag inputs.length bound ++
  incrementClauses tag bound inputs ++
  overflowClauses tag bound inputs

theorem sequentialAtMostFmla_length (tag bound : Nat) (inputs : List Nat) :
    (sequentialAtMostFmla tag bound inputs).length =
      inputs.length +
      (inputs.length - 1) * (bound + 1) +
      (inputs.length - 1) * bound +
      (if inputs.length = 0 then 0 else 1) := by
  by_cases h : inputs.length = 0
  · have : inputs = [] := List.length_eq_zero_iff.mp h
    subst inputs
    simp [sequentialAtMostFmla, triggerClauses, carryClauses,
      incrementClauses, overflowClauses]
  · simp [sequentialAtMostFmla, triggerClauses, carryClauses,
      incrementClauses, overflowClauses, List.length_flatMap, h,
      Nat.add_assoc]

private theorem satisfies_neg_pos {v : Sat.Valuation} {a b : Nat}
    (h : v.satisfies [Sat.Literal.neg a, Sat.Literal.pos b]) :
    v a → v b := by
  intro ha
  by_contra hb
  exact h ha hb

private theorem satisfies_neg_neg_pos {v : Sat.Valuation} {a b d : Nat}
    (h : v.satisfies
      [Sat.Literal.neg a, Sat.Literal.neg b, Sat.Literal.pos d]) :
    v a → v b → v d := by
  intro ha hb
  by_contra hd
  exact h ha hb hd

private theorem satisfies_neg_unit {v : Sat.Valuation} {a : Nat}
    (h : v.satisfies [Sat.Literal.neg a]) : ¬v a := by
  intro ha
  exact h ha

/-! ## Mathematical input count and explicit satisfying extension -/

/-- Boolean reflection of a propositional SAT valuation. -/
noncomputable def truthBit (v : Sat.Valuation) (atom : Nat) : Bool :=
  @ite Bool (v atom) (Classical.propDecidable _) true false

@[simp] theorem truthBit_eq_true {v : Sat.Valuation} {atom : Nat} :
    truthBit v atom = true ↔ v atom := by
  simp [truthBit]

/-- Number of true input occurrences (duplicates, if supplied, count as
separate sequential positions). -/
noncomputable def trueInputCount (v : Sat.Valuation)
    (inputs : List Nat) : Nat :=
  List.countP (truthBit v) inputs

/-- Number of true inputs in the first `prefix` positions. -/
noncomputable def prefixTrueCount (v : Sat.Valuation)
    (inputs : List Nat) (prefixLen : Nat) : Nat :=
  List.countP (truthBit v) (inputs.take prefixLen)

def InputsAtMost (bound : Nat) (inputs : List Nat)
    (v : Sat.Valuation) : Prop :=
  trueInputCount v inputs ≤ bound

theorem prefixTrueCount_length (v : Sat.Valuation) (inputs : List Nat) :
    prefixTrueCount v inputs inputs.length = trueInputCount v inputs := by
  simp [prefixTrueCount, trueInputCount]

theorem prefixTrueCount_succ (v : Sat.Valuation) (inputs : List Nat)
    (i : Nat) (hi : i < inputs.length) :
    prefixTrueCount v inputs (i + 1) =
      prefixTrueCount v inputs i +
        (if truthBit v inputs[i] = true then 1 else 0) := by
  unfold prefixTrueCount
  calc
    List.countP (truthBit v) (inputs.take (i + 1)) =
        List.countP (truthBit v) ((inputs.take i).concat inputs[i]) :=
      congrArg (List.countP (truthBit v))
        (List.take_concat_get (l := inputs) (i := i) hi).symm
    _ = List.countP (truthBit v) (inputs.take i) +
        (if truthBit v inputs[i] = true then 1 else 0) := by
      rw [List.concat_eq_append, List.countP_append,
        List.countP_singleton]

/-- Decode exactly the chosen leading-tag namespace as unary threshold
values; all atoms outside that namespace retain their old value. -/
noncomputable def sequentialExtension (tag : Nat) (inputs : List Nat)
    (v : Sat.Valuation) : Sat.Valuation := fun atom =>
  @dite Prop (InSequentialNamespace tag atom)
      (Classical.propDecidable _)
      (fun _ =>
    let coordinates := Nat.unpair (Nat.unpair atom).2
    coordinates.2 < prefixTrueCount v inputs (coordinates.1 + 1))
      (fun _ => v atom)

@[simp] theorem sequentialExtension_aux (tag : Nat) (inputs : List Nat)
    (v : Sat.Valuation) (i j : Nat) :
    sequentialExtension tag inputs v (sequentialAuxAtom tag i j) ↔
      j < prefixTrueCount v inputs (i + 1) := by
  simp [sequentialExtension, sequentialAuxAtom, InSequentialNamespace,
    Nat.unpair_pair]

theorem sequentialExtension_eq_of_outside
    (tag : Nat) (inputs : List Nat) (v : Sat.Valuation) {atom : Nat}
    (hout : ¬InSequentialNamespace tag atom) :
    sequentialExtension tag inputs v atom ↔ v atom := by
  simp [sequentialExtension, hout]

theorem sequentialExtension_agrees_on_inputs
    (tag : Nat) (inputs : List Nat) (v : Sat.Valuation)
    (hinputs : InputsOutsideNamespace tag inputs) :
    ∀ atom ∈ inputs,
      (sequentialExtension tag inputs v atom ↔ v atom) := by
  intro atom hatom
  exact sequentialExtension_eq_of_outside tag inputs v
    (hinputs atom hatom)

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
      · intro l hl
        exact hagrees l (List.Mem.tail literal hl)
      · apply hw
        exact (neg_iff_of_atom_iff literal
          (hagrees literal (List.Mem.head tail))).mp hvneg

/-- Any formula avoiding the reserved namespace remains satisfied after the
counter extension. -/
theorem sequentialExtension_satisfies_base
    (tag : Nat) (inputs : List Nat) (base : Sat.Fmla)
    (v : Sat.Valuation)
    (hbaseNamespace : FormulaOutsideNamespace tag base)
    (hbase : v.satisfies_fmla base) :
    (sequentialExtension tag inputs v).satisfies_fmla base := by
  constructor
  intro clause hclause
  apply satisfies_of_agrees_on_clause clause
  · intro literal hliteral
    exact sequentialExtension_eq_of_outside tag inputs v
      (hbaseNamespace clause hclause literal hliteral)
  · exact hbase.prop clause hclause

/-! ## Clause-level interfaces -/

theorem trigger_imp_of_satisfies
    {tag bound : Nat} {inputs : List Nat} {v : Sat.Valuation}
    (h : v.satisfies_fmla (sequentialAtMostFmla tag bound inputs))
    (i : Fin inputs.length) :
    v inputs[i] → v (sequentialAuxAtom tag i.val 0) := by
  apply satisfies_neg_pos
  apply h.prop
  simp [sequentialAtMostFmla, triggerClauses]

theorem carry_imp_of_satisfies
    {tag bound : Nat} {inputs : List Nat} {v : Sat.Valuation}
    (h : v.satisfies_fmla (sequentialAtMostFmla tag bound inputs))
    (p : Fin (inputs.length - 1)) (j : Nat) (hj : j < bound + 1) :
    v (sequentialAuxAtom tag p.val j) →
      v (sequentialAuxAtom tag (p.val + 1) j) := by
  apply satisfies_neg_pos
  apply h.prop
  simp only [sequentialAtMostFmla, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (by
    simp only [carryClauses, List.mem_flatMap, List.mem_map]
    exact ⟨p, List.mem_finRange p, j, List.mem_range.mpr hj, rfl⟩)))

theorem increment_imp_of_satisfies
    {tag bound : Nat} {inputs : List Nat} {v : Sat.Valuation}
    (h : v.satisfies_fmla (sequentialAtMostFmla tag bound inputs))
    (p : Fin (inputs.length - 1)) (j : Nat) (hj : j < bound) :
    v (transitionInput inputs p) →
    v (sequentialAuxAtom tag p.val j) →
      v (sequentialAuxAtom tag (p.val + 1) (j + 1)) := by
  apply satisfies_neg_neg_pos
  apply h.prop
  simp only [sequentialAtMostFmla, List.mem_append]
  exact Or.inl (Or.inr (by
    simp only [incrementClauses, List.mem_flatMap, List.mem_map]
    exact ⟨p, List.mem_finRange p, j, List.mem_range.mpr hj, rfl⟩))

theorem overflow_false_of_satisfies
    {tag bound : Nat} {inputs : List Nat} {v : Sat.Valuation}
    (h : v.satisfies_fmla (sequentialAtMostFmla tag bound inputs))
    (hnonempty : inputs.length ≠ 0) :
    ¬v (sequentialAuxAtom tag (inputs.length - 1) bound) := by
  apply satisfies_neg_unit
  apply h.prop
  simp only [sequentialAtMostFmla, List.mem_append]
  exact Or.inr (by simp [overflowClauses, hnonempty])

/-! ## Completeness of the one-way encoding -/

private theorem extension_satisfies_triggers
    (tag _bound : Nat) (inputs : List Nat) (v : Sat.Valuation)
    (hinputs : InputsOutsideNamespace tag inputs) :
    (sequentialExtension tag inputs v).satisfies_fmla
      (triggerClauses tag inputs) := by
  constructor
  intro clause hclause
  simp only [triggerClauses, List.mem_map] at hclause
  obtain ⟨i, _, rfl⟩ := hclause
  by_cases hx : v inputs[i]
  · apply satisfies_of_mem_holds
      (sequentialExtension tag inputs v)
      (l := Sat.Literal.pos (sequentialAuxAtom tag i.val 0))
      (List.Mem.tail _ (List.Mem.head _))
    change sequentialExtension tag inputs v
      (sequentialAuxAtom tag i.val 0)
    rw [sequentialExtension_aux]
    have hstep := prefixTrueCount_succ v inputs i.val i.isLt
    have hbit : truthBit v inputs[i] = true := truthBit_eq_true.mpr hx
    have hbit' : truthBit v inputs[i.val] = true := by simpa using hbit
    rw [if_pos hbit'] at hstep
    omega
  · apply satisfies_of_mem_holds
      (sequentialExtension tag inputs v)
      (l := Sat.Literal.neg inputs[i]) (List.Mem.head _)
    change ¬sequentialExtension tag inputs v inputs[i]
    rw [sequentialExtension_agrees_on_inputs tag inputs v hinputs
      inputs[i] (List.getElem_mem i.isLt)]
    exact hx

private theorem extension_satisfies_carries
    (tag bound : Nat) (inputs : List Nat) (v : Sat.Valuation) :
    (sequentialExtension tag inputs v).satisfies_fmla
      (carryClauses tag inputs.length bound) := by
  constructor
  intro clause hclause
  simp only [carryClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨p, _, j, hj, rfl⟩ := hclause
  have hjlt : j < bound + 1 := List.mem_range.mp hj
  by_cases hprev : sequentialExtension tag inputs v
      (sequentialAuxAtom tag p.val j)
  · apply satisfies_of_mem_holds
      (sequentialExtension tag inputs v)
      (l := Sat.Literal.pos (sequentialAuxAtom tag (p.val + 1) j))
      (List.Mem.tail _ (List.Mem.head _))
    change sequentialExtension tag inputs v
      (sequentialAuxAtom tag (p.val + 1) j)
    rw [sequentialExtension_aux] at hprev ⊢
    have hcurrent : p.val + 1 < inputs.length := by omega
    have hstep := prefixTrueCount_succ v inputs (p.val + 1) hcurrent
    omega
  · apply satisfies_of_mem_holds
      (sequentialExtension tag inputs v)
      (l := Sat.Literal.neg (sequentialAuxAtom tag p.val j))
      (List.Mem.head _)
    exact hprev

private theorem extension_satisfies_increments
    (tag bound : Nat) (inputs : List Nat) (v : Sat.Valuation)
    (hinputs : InputsOutsideNamespace tag inputs) :
    (sequentialExtension tag inputs v).satisfies_fmla
      (incrementClauses tag bound inputs) := by
  constructor
  intro clause hclause
  simp only [incrementClauses, List.mem_flatMap, List.mem_map] at hclause
  obtain ⟨p, _, j, hj, rfl⟩ := hclause
  have hcurrent : p.val + 1 < inputs.length := by omega
  let current : Fin inputs.length := ⟨p.val + 1, hcurrent⟩
  have htransition : transitionInput inputs p = inputs[current] := by
    apply congrArg inputs.get
    apply Fin.ext
    rfl
  by_cases hx : v (transitionInput inputs p)
  · by_cases hprev : sequentialExtension tag inputs v
        (sequentialAuxAtom tag p.val j)
    · apply satisfies_of_mem_holds
        (sequentialExtension tag inputs v)
        (l := Sat.Literal.pos
          (sequentialAuxAtom tag (p.val + 1) (j + 1)))
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      change sequentialExtension tag inputs v
        (sequentialAuxAtom tag (p.val + 1) (j + 1))
      rw [sequentialExtension_aux] at hprev ⊢
      have hstep := prefixTrueCount_succ v inputs (p.val + 1) hcurrent
      have hbit : truthBit v inputs[current] = true := by
        rw [← htransition]
        exact truthBit_eq_true.mpr hx
      have hbit' : truthBit v inputs[p.val + 1] = true := by
        simpa [current] using hbit
      rw [if_pos hbit'] at hstep
      omega
    · apply satisfies_of_mem_holds
        (sequentialExtension tag inputs v)
        (l := Sat.Literal.neg (sequentialAuxAtom tag p.val j))
        (List.Mem.tail _ (List.Mem.head _))
      exact hprev
  · apply satisfies_of_mem_holds
      (sequentialExtension tag inputs v)
      (l := Sat.Literal.neg (transitionInput inputs p))
      (List.Mem.head _)
    change ¬sequentialExtension tag inputs v (transitionInput inputs p)
    rw [htransition,
      sequentialExtension_agrees_on_inputs tag inputs v hinputs
        inputs[current] (List.getElem_mem current.isLt)]
    simpa [htransition] using hx

private theorem extension_satisfies_overflow
    (tag bound : Nat) (inputs : List Nat) (v : Sat.Valuation)
    (hatMost : InputsAtMost bound inputs v) :
    (sequentialExtension tag inputs v).satisfies_fmla
      (overflowClauses tag bound inputs) := by
  constructor
  intro clause hclause
  by_cases hempty : inputs.length = 0
  · simp [overflowClauses, hempty] at hclause
  · simp only [overflowClauses, hempty, ↓reduceDIte,
      List.mem_singleton] at hclause
    subst clause
    apply satisfies_of_mem_holds
      (sequentialExtension tag inputs v)
      (l := Sat.Literal.neg
        (sequentialAuxAtom tag (inputs.length - 1) bound))
      (List.Mem.head _)
    change ¬sequentialExtension tag inputs v
      (sequentialAuxAtom tag (inputs.length - 1) bound)
    rw [sequentialExtension_aux]
    rw [show inputs.length - 1 + 1 = inputs.length by omega,
      prefixTrueCount_length]
    exact Nat.not_lt.mpr hatMost

/-- If at most `bound` input occurrences are true, the explicit unary-prefix
extension satisfies every counter clause and agrees with the old valuation
on all inputs.  This is the exact one-way extension theorem needed when a
checked refutation is used against a mathematical degree cap. -/
theorem sequentialExtension_satisfies_counter
    (tag bound : Nat) (inputs : List Nat) (v : Sat.Valuation)
    (hinputs : InputsOutsideNamespace tag inputs)
    (hatMost : InputsAtMost bound inputs v) :
    (sequentialExtension tag inputs v).satisfies_fmla
      (sequentialAtMostFmla tag bound inputs) := by
  constructor
  intro clause hclause
  simp only [sequentialAtMostFmla, List.mem_append] at hclause
  rcases hclause with ((htrigger | hcarry) | hincrement) | hoverflow
  · exact (extension_satisfies_triggers tag bound inputs v hinputs).prop
      clause htrigger
  · exact (extension_satisfies_carries tag bound inputs v).prop clause hcarry
  · exact (extension_satisfies_increments tag bound inputs v hinputs).prop
      clause hincrement
  · exact (extension_satisfies_overflow tag bound inputs v hatMost).prop
      clause hoverflow

/-! ## Soundness of the unary threshold propagation -/

private theorem aux_of_prefix_threshold
    {tag bound : Nat} {inputs : List Nat} {v : Sat.Valuation}
    (hsat : v.satisfies_fmla (sequentialAtMostFmla tag bound inputs))
    (row : Nat) (hrow : row < inputs.length)
    (j : Nat) (hj : j ≤ bound)
    (hcount : j < prefixTrueCount v inputs (row + 1)) :
    v (sequentialAuxAtom tag row j) := by
  induction row using Nat.strong_induction_on generalizing j with
  | h row ih =>
      by_cases hzero : row = 0
      · subst row
        have hstep := prefixTrueCount_succ v inputs 0 hrow
        have hprefixZero : prefixTrueCount v inputs 0 = 0 := by
          simp [prefixTrueCount]
        by_cases hbit : truthBit v inputs[0] = true
        · rw [if_pos hbit, hprefixZero] at hstep
          have hjzero : j = 0 := by omega
          subst j
          exact trigger_imp_of_satisfies hsat ⟨0, hrow⟩
            (truthBit_eq_true.mp hbit)
        · rw [if_neg hbit, hprefixZero] at hstep
          omega
      · have hprevRow : row - 1 < row := by omega
        have hprevInRange : row - 1 < inputs.length := by omega
        have htransitionRange : row - 1 < inputs.length - 1 := by omega
        let p : Fin (inputs.length - 1) :=
          ⟨row - 1, htransitionRange⟩
        have hpSucc : p.val + 1 = row := by
          simp [p]
          omega
        have hstep := prefixTrueCount_succ v inputs row hrow
        by_cases hbelow : j < prefixTrueCount v inputs row
        · have hprevAux := ih (row - 1) hprevRow hprevInRange j hj
            (by simpa [show row - 1 + 1 = row by omega] using hbelow)
          have hcarried := carry_imp_of_satisfies hsat p j (by omega) hprevAux
          simpa [hpSucc] using hcarried
        · have hcountLe : prefixTrueCount v inputs row ≤ j :=
            Nat.le_of_not_gt hbelow
          by_cases hbit : truthBit v inputs[row] = true
          · rw [if_pos hbit] at hstep
            have hcountEq : prefixTrueCount v inputs row = j := by omega
            by_cases hjzero : j = 0
            · have htrigger := trigger_imp_of_satisfies hsat ⟨row, hrow⟩
                (truthBit_eq_true.mp hbit)
              simpa [hjzero] using htrigger
            · let q := j - 1
              have hqBelow : q < prefixTrueCount v inputs row := by
                simp [q, hcountEq]
                omega
              have hqLe : q ≤ bound := by omega
              have hqBound : q < bound := by omega
              have hprevAux := ih (row - 1) hprevRow hprevInRange q hqLe
                (by simpa [show row - 1 + 1 = row by omega] using hqBelow)
              have htransition : transitionInput inputs p =
                  inputs.get ⟨row, hrow⟩ := by
                apply congrArg inputs.get
                apply Fin.ext
                exact hpSucc
              have hincremented := increment_imp_of_satisfies hsat p q hqBound
                (by
                  rw [htransition]
                  exact truthBit_eq_true.mp hbit)
                hprevAux
              have hqSucc : q + 1 = j := by
                simp [q]
                omega
              simpa [hpSucc, hqSucc] using hincremented
          · rw [if_neg hbit] at hstep
            omega

/-- Every valuation satisfying the generated clauses has at most `bound`
true input occurrences.  Thus the one-way auxiliary implications are already
strong enough to enforce the mathematical cardinality condition. -/
theorem inputsAtMost_of_satisfies_counter
    {tag bound : Nat} {inputs : List Nat} {v : Sat.Valuation}
    (hsat : v.satisfies_fmla (sequentialAtMostFmla tag bound inputs)) :
    InputsAtMost bound inputs v := by
  unfold InputsAtMost
  by_cases hempty : inputs.length = 0
  · have : inputs = [] := List.length_eq_zero_iff.mp hempty
    subst inputs
    simp [trueInputCount]
  · apply Nat.le_of_not_gt
    intro htooMany
    have hrow : inputs.length - 1 < inputs.length := by omega
    have hthreshold : bound <
        prefixTrueCount v inputs ((inputs.length - 1) + 1) := by
      rw [show inputs.length - 1 + 1 = inputs.length by omega,
        prefixTrueCount_length]
      exact htooMany
    have haux := aux_of_prefix_threshold hsat
      (inputs.length - 1) hrow bound (Nat.le_refl bound) hthreshold
    exact (overflow_false_of_satisfies hsat hempty) haux

/-! ## Appending the counter to a base formula and LRAT soundness -/

/-- Authoritative append order: all base clauses first, then the complete
sequential counter in its documented deterministic order. -/
def withSequentialAtMost (base : Sat.Fmla) (tag bound : Nat)
    (inputs : List Nat) : Sat.Fmla :=
  base ++ sequentialAtMostFmla tag bound inputs

theorem withSequentialAtMost_length (base : Sat.Fmla) (tag bound : Nat)
    (inputs : List Nat) :
    (withSequentialAtMost base tag bound inputs).length =
      base.length +
        (inputs.length +
        (inputs.length - 1) * (bound + 1) +
        (inputs.length - 1) * bound +
        (if inputs.length = 0 then 0 else 1)) := by
  simp [withSequentialAtMost, sequentialAtMostFmla_length]

/-- Satisfying the appended formula really enforces the mathematical cap;
this direction needs no namespace hypothesis. -/
theorem inputsAtMost_of_satisfies_withSequentialAtMost
    {base : Sat.Fmla} {tag bound : Nat} {inputs : List Nat}
    {v : Sat.Valuation}
    (hsat : v.satisfies_fmla
      (withSequentialAtMost base tag bound inputs)) :
    InputsAtMost bound inputs v := by
  apply inputsAtMost_of_satisfies_counter
  constructor
  intro clause hclause
  exact hsat.prop clause (List.mem_append.mpr (Or.inr hclause))

/-- A base model satisfying the mathematical cap extends to a model of the
appended CNF.  Agreement on the base is protected by the explicit whole-tag
namespace-disjointness premise. -/
theorem sequentialExtension_satisfies_withSequentialAtMost
    (base : Sat.Fmla) (tag bound : Nat) (inputs : List Nat)
    (v : Sat.Valuation)
    (hbaseNamespace : FormulaOutsideNamespace tag base)
    (hinputs : InputsOutsideNamespace tag inputs)
    (hbase : v.satisfies_fmla base)
    (hatMost : InputsAtMost bound inputs v) :
    (sequentialExtension tag inputs v).satisfies_fmla
      (withSequentialAtMost base tag bound inputs) := by
  constructor
  intro clause hclause
  rcases List.mem_append.mp hclause with hbaseClause | hcounterClause
  · exact (sequentialExtension_satisfies_base
      tag inputs base v hbaseNamespace hbase).prop clause hbaseClause
  · exact (sequentialExtension_satisfies_counter
      tag bound inputs v hinputs hatMost).prop clause hcounterClause

/-- Trusted refutation boundary for degree caps.  A kernel-checked LRAT proof
of the exact Lean append rules out a base valuation with at most `bound` true
inputs: such a valuation would have the explicit satisfying extension above.

The theorem consumes only `Sat.Fmla.proof []`, exactly the type produced by
`checked_lrat_proof`; no external variable map or cardinality encoder is
trusted. -/
theorem no_base_valuation_atMost_of_lrat
    (base : Sat.Fmla) (tag bound : Nat) (inputs : List Nat)
    (hbaseNamespace : FormulaOutsideNamespace tag base)
    (hinputs : InputsOutsideNamespace tag inputs)
    (hunsat : (withSequentialAtMost base tag bound inputs).proof []) :
    ¬∃ v : Sat.Valuation,
      v.satisfies_fmla base ∧ InputsAtMost bound inputs v := by
  rintro ⟨v, hbase, hatMost⟩
  exact hunsat (sequentialExtension tag inputs v)
    (sequentialExtension_satisfies_withSequentialAtMost
      base tag bound inputs v hbaseNamespace hinputs hbase hatMost)

#print axioms R4333.SequentialAtMostCNF.sequentialAtMostFmla_length
#print axioms R4333.SequentialAtMostCNF.sequentialExtension_satisfies_counter
#print axioms R4333.SequentialAtMostCNF.inputsAtMost_of_satisfies_counter
#print axioms R4333.SequentialAtMostCNF.no_base_valuation_atMost_of_lrat

end SequentialAtMostCNF

end R4333
