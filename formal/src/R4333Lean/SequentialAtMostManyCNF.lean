import R4333Lean.SequentialAtMostCNF

/-!
# Ordered families of sequential at-most counters

Production degree formulas contain many cardinality caps.  This file lifts
the single-counter trusted boundary to a finite ordered family while keeping
all ordering and namespace obligations explicit.

The authoritative formula is a left fold: start with the base formula and
append each complete counter block in list order.  The explicit iterated
valuation uses the same list order.  Pairwise-distinct leading tags, together
with the requirement that every semantic input and base atom avoids every
reserved tag, ensures that a later extension cannot change an earlier
counter, a later counter's inputs, or the base formula.
-/

namespace R4333

open FiniteColorCNF SequentialAtMostCNF

namespace SequentialAtMostManyCNF

/-- One ordered cardinality-cap specification. -/
structure CounterSpec where
  tag : Nat
  bound : Nat
  inputs : List Nat
deriving Repr, DecidableEq

/-- The complete clause block contributed by one specification. -/
def counterBlock (spec : CounterSpec) : Sat.Fmla :=
  sequentialAtMostFmla spec.tag spec.bound spec.inputs

/-- Authoritative clause order: a left fold appending whole counter blocks. -/
def manySequentialAtMostFmla (base : Sat.Fmla)
    (specs : List CounterSpec) : Sat.Fmla :=
  specs.foldl (fun formula spec => formula ++ counterBlock spec) base

/-- Explicit iterated semantic extension in exactly the specification order. -/
noncomputable def iteratedSequentialExtension
    (specs : List CounterSpec) (v : Sat.Valuation) : Sat.Valuation :=
  specs.foldl (fun current spec =>
    sequentialExtension spec.tag spec.inputs current) v

/-- All caps hold in the original mathematical/base valuation. -/
def AllCaps (specs : List CounterSpec) (v : Sat.Valuation) : Prop :=
  ∀ spec, List.Mem spec specs →
    InputsAtMost spec.bound spec.inputs v

/-- The complete namespace contract for an ordered counter family.

* tags are pairwise distinct;
* every base atom avoids every reserved tag;
* the inputs of every counter avoid every reserved tag (including their own).
-/
structure ManyCounterWellFormed (base : Sat.Fmla)
    (specs : List CounterSpec) : Prop where
  tags_nodup : (specs.map CounterSpec.tag).Nodup
  base_outside : ∀ reserved, List.Mem reserved specs →
    FormulaOutsideNamespace reserved.tag base
  inputs_outside : ∀ reserved, List.Mem reserved specs →
    ∀ target, List.Mem target specs →
      InputsOutsideNamespace reserved.tag target.inputs

@[simp] theorem manySequentialAtMostFmla_nil (base : Sat.Fmla) :
    manySequentialAtMostFmla base [] = base := rfl

@[simp] theorem manySequentialAtMostFmla_cons
    (base : Sat.Fmla) (spec : CounterSpec) (specs : List CounterSpec) :
    manySequentialAtMostFmla base (spec :: specs) =
      manySequentialAtMostFmla (base ++ counterBlock spec) specs := rfl

@[simp] theorem iteratedSequentialExtension_nil (v : Sat.Valuation) :
    iteratedSequentialExtension [] v = v := rfl

@[simp] theorem iteratedSequentialExtension_cons
    (spec : CounterSpec) (specs : List CounterSpec) (v : Sat.Valuation) :
    iteratedSequentialExtension (spec :: specs) v =
      iteratedSequentialExtension specs
        (sequentialExtension spec.tag spec.inputs v) := rfl

/-- A flattened characterization useful for external mirrors: the left fold
is base clauses followed by blocks in list order, without interleaving. -/
theorem manySequentialAtMostFmla_eq_append_flatMap
    (base : Sat.Fmla) (specs : List CounterSpec) :
    manySequentialAtMostFmla base specs =
      base ++ specs.flatMap counterBlock := by
  induction specs generalizing base with
  | nil => simp
  | cons spec specs ih =>
      rw [manySequentialAtMostFmla_cons, ih]
      simp [List.append_assoc]

theorem manySequentialAtMostFmla_length
    (base : Sat.Fmla) (specs : List CounterSpec) :
    (manySequentialAtMostFmla base specs).length =
      base.length + (specs.map fun spec =>
        (counterBlock spec).length).sum := by
  rw [manySequentialAtMostFmla_eq_append_flatMap]
  simp [List.length_flatMap]

/-- Distinct leading tags reserve disjoint whole `Nat.pair` namespaces. -/
theorem namespaces_disjoint_of_tag_ne
    {leftTag rightTag atom : Nat} (hne : leftTag ≠ rightTag)
    (hleft : InSequentialNamespace leftTag atom) :
    ¬InSequentialNamespace rightTag atom := by
  intro hright
  exact hne (hleft.symm.trans hright)

private theorem aux_outside_other_namespace
    {counterTag reservedTag i j : Nat} (hne : counterTag ≠ reservedTag) :
    ¬InSequentialNamespace reservedTag
      (sequentialAuxAtom counterTag i j) := by
  simp [InSequentialNamespace, sequentialAuxAtom, hne]

/-- A counter block avoids another reserved namespace when its semantic
inputs avoid that namespace and its own tag differs from the reserved tag. -/
theorem counterBlock_outside_other_namespace
    (spec : CounterSpec) (reservedTag : Nat)
    (htag : spec.tag ≠ reservedTag)
    (hinputs : InputsOutsideNamespace reservedTag spec.inputs) :
    FormulaOutsideNamespace reservedTag (counterBlock spec) := by
  intro clause hclause literal hliteral
  change List.Mem clause
    (sequentialAtMostFmla spec.tag spec.bound spec.inputs) at hclause
  change List.Mem clause
    (((triggerClauses spec.tag spec.inputs ++
      carryClauses spec.tag spec.inputs.length spec.bound) ++
      incrementClauses spec.tag spec.bound spec.inputs) ++
      overflowClauses spec.tag spec.bound spec.inputs) at hclause
  rcases List.mem_append.mp hclause with hleft | hoverflow
  rcases List.mem_append.mp hleft with hleft | hincrement
  rcases List.mem_append.mp hleft with htrigger | hcarry
  · simp only [triggerClauses, List.mem_map] at htrigger
    obtain ⟨i, _, rfl⟩ := htrigger
    cases hliteral with
    | head =>
        exact hinputs spec.inputs[i] (List.getElem_mem i.isLt)
    | tail _ htail =>
        cases htail with
        | head => exact aux_outside_other_namespace htag
        | tail _ hnil => exact nomatch hnil
  · simp only [carryClauses, List.mem_flatMap, List.mem_map] at hcarry
    obtain ⟨p, _, j, _, rfl⟩ := hcarry
    cases hliteral with
    | head => exact aux_outside_other_namespace htag
    | tail _ htail =>
        cases htail with
        | head => exact aux_outside_other_namespace htag
        | tail _ hnil => exact nomatch hnil
  · simp only [incrementClauses, List.mem_flatMap, List.mem_map] at hincrement
    obtain ⟨p, _, j, _, rfl⟩ := hincrement
    cases hliteral with
    | head =>
        apply hinputs (transitionInput spec.inputs p)
        exact List.get_mem spec.inputs
          ⟨p.val + 1, by omega⟩
    | tail _ htail =>
        cases htail with
        | head => exact aux_outside_other_namespace htag
        | tail _ htail =>
            cases htail with
            | head => exact aux_outside_other_namespace htag
            | tail _ hnil => exact nomatch hnil
  · simp only [overflowClauses] at hoverflow
    split at hoverflow
    · exact nomatch hoverflow
    · simp only [List.mem_singleton] at hoverflow
      subst clause
      cases hliteral with
      | head => exact aux_outside_other_namespace htag
      | tail _ hnil => exact nomatch hnil

private theorem formulaOutsideNamespace_append
    {tag : Nat} {left right : Sat.Fmla}
    (hleft : FormulaOutsideNamespace tag left)
    (hright : FormulaOutsideNamespace tag right) :
    FormulaOutsideNamespace tag (left ++ right) := by
  intro clause hclause literal hliteral
  rcases List.mem_append.mp hclause with hclause | hclause
  · exact hleft clause hclause literal hliteral
  · exact hright clause hclause literal hliteral

/-- Pointwise agreement on a list preserves the mathematical count of true
input occurrences, including the documented duplicate-occurrence behavior. -/
theorem trueInputCount_eq_of_agrees
    {v w : Sat.Valuation} (inputs : List Nat)
    (hagrees : ∀ atom, List.Mem atom inputs → (v atom ↔ w atom)) :
    trueInputCount v inputs = trueInputCount w inputs := by
  induction inputs with
  | nil => simp [trueInputCount]
  | cons atom inputs ih =>
      have hbit : truthBit v atom = truthBit w atom :=
        Bool.eq_iff_iff.mpr (by
          simpa using hagrees atom (List.Mem.head inputs))
      simp only [trueInputCount, List.countP_cons]
      rw [hbit]
      congr 1
      apply ih
      intro a ha
      exact hagrees a (List.Mem.tail atom ha)

/-- One extension preserves a cap whose inputs avoid that extension's tag. -/
theorem inputsAtMost_sequentialExtension_iff
    (extensionSpec target : CounterSpec) (v : Sat.Valuation)
    (houtside : InputsOutsideNamespace extensionSpec.tag target.inputs) :
    InputsAtMost target.bound target.inputs
        (sequentialExtension extensionSpec.tag extensionSpec.inputs v) ↔
      InputsAtMost target.bound target.inputs v := by
  unfold InputsAtMost
  rw [trueInputCount_eq_of_agrees target.inputs (by
    intro atom hatom
    exact sequentialExtension_eq_of_outside
      extensionSpec.tag extensionSpec.inputs v (houtside atom hatom))]

private theorem head_tag_ne_tail_tag
    {head reserved : CounterSpec} {tail : List CounterSpec}
    (hnodup : ((head :: tail).map CounterSpec.tag).Nodup)
    (hreserved : List.Mem reserved tail) :
    head.tag ≠ reserved.tag := by
  intro heq
  have hnotmem : head.tag ∉ tail.map CounterSpec.tag :=
    (List.nodup_cons.mp hnodup).1
  apply hnotmem
  exact List.mem_map.mpr ⟨reserved, hreserved, heq.symm⟩

/-- Removing the head and appending its block preserves the full
well-formedness invariant needed by the induction. -/
private theorem wellFormed_tail_after_head
    {base : Sat.Fmla} {head : CounterSpec} {tail : List CounterSpec}
    (hwf : ManyCounterWellFormed base (head :: tail)) :
    ManyCounterWellFormed (base ++ counterBlock head) tail := by
  refine ⟨List.Nodup.of_cons hwf.tags_nodup, ?_, ?_⟩
  · intro reserved hreserved
    apply formulaOutsideNamespace_append
    · exact hwf.base_outside reserved (List.Mem.tail head hreserved)
    · apply counterBlock_outside_other_namespace head reserved.tag
      · exact head_tag_ne_tail_tag hwf.tags_nodup hreserved
      · exact hwf.inputs_outside reserved (List.Mem.tail head hreserved)
          head (List.Mem.head tail)
  · intro reserved hreserved target htarget
    exact hwf.inputs_outside
      reserved (List.Mem.tail head hreserved)
      target (List.Mem.tail head htarget)

/-- The explicit iterated valuation satisfies the exact left-fold formula
whenever the base model obeys every mathematical cap and the namespace
contract holds. -/
theorem iteratedExtension_satisfies_manySequentialAtMostFmla
    (base : Sat.Fmla) (specs : List CounterSpec) (v : Sat.Valuation)
    (hwf : ManyCounterWellFormed base specs)
    (hbase : v.satisfies_fmla base)
    (hcaps : AllCaps specs v) :
    (iteratedSequentialExtension specs v).satisfies_fmla
      (manySequentialAtMostFmla base specs) := by
  induction specs generalizing base v with
  | nil => simpa using hbase
  | cons head tail ih =>
      let nextValuation := sequentialExtension head.tag head.inputs v
      have hheadInputs : InputsOutsideNamespace head.tag head.inputs :=
        hwf.inputs_outside head (List.Mem.head tail)
          head (List.Mem.head tail)
      have hnextBase : nextValuation.satisfies_fmla
          (base ++ counterBlock head) := by
        exact sequentialExtension_satisfies_withSequentialAtMost
          base head.tag head.bound head.inputs v
          (hwf.base_outside head (List.Mem.head tail))
          hheadInputs hbase
          (hcaps head (List.Mem.head tail))
      have htailCaps : AllCaps tail nextValuation := by
        intro target htarget
        rw [inputsAtMost_sequentialExtension_iff head target v
          (hwf.inputs_outside head (List.Mem.head tail)
            target (List.Mem.tail head htarget))]
        exact hcaps target (List.Mem.tail head htarget)
      have htail := ih (base ++ counterBlock head) nextValuation
        (wellFormed_tail_after_head hwf) hnextBase htailCaps
      exact htail

/-- Conversely, any satisfying valuation of the full left-fold formula
obeys every mathematical cap.  No namespace assumptions are needed in this
direction. -/
theorem allCaps_of_satisfies_manySequentialAtMostFmla
    {base : Sat.Fmla} {specs : List CounterSpec} {v : Sat.Valuation}
    (hsat : v.satisfies_fmla (manySequentialAtMostFmla base specs)) :
    AllCaps specs v := by
  intro spec hspec
  apply inputsAtMost_of_satisfies_counter
  constructor
  intro clause hclause
  apply hsat.prop clause
  rw [manySequentialAtMostFmla_eq_append_flatMap]
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨spec, hspec, hclause⟩

/-- Checked-refutation boundary for an ordered counter family.  A theorem of
type `(...).proof []` can come directly from `checked_lrat_proof`; the explicit
iterated extension then rules out any base model satisfying all caps. -/
theorem no_base_valuation_allCaps_of_lrat
    (base : Sat.Fmla) (specs : List CounterSpec)
    (hwf : ManyCounterWellFormed base specs)
    (hunsat : (manySequentialAtMostFmla base specs).proof []) :
    ¬∃ v : Sat.Valuation, v.satisfies_fmla base ∧ AllCaps specs v := by
  rintro ⟨v, hbase, hcaps⟩
  exact hunsat (iteratedSequentialExtension specs v)
    (iteratedExtension_satisfies_manySequentialAtMostFmla
      base specs v hwf hbase hcaps)

#print axioms R4333.SequentialAtMostManyCNF.manySequentialAtMostFmla_eq_append_flatMap
#print axioms R4333.SequentialAtMostManyCNF.iteratedExtension_satisfies_manySequentialAtMostFmla
#print axioms R4333.SequentialAtMostManyCNF.allCaps_of_satisfies_manySequentialAtMostFmla
#print axioms R4333.SequentialAtMostManyCNF.no_base_valuation_allCaps_of_lrat

end SequentialAtMostManyCNF

end R4333
